using MBBSEmu.Database.Repositories.Account;
using MBBSEmu.Database.Repositories.AccountKey;
using MBBSEmu.Date;
using MBBSEmu.Disassembler.Artifacts;
using MBBSEmu.DOS;
using MBBSEmu.Extensions;
using MBBSEmu.HostProcess.Enums;
using MBBSEmu.HostProcess.ExportedModules;
using MBBSEmu.HostProcess.GlobalRoutines;
using MBBSEmu.HostProcess.HostRoutines;
using MBBSEmu.IO;
using MBBSEmu.Logging;
using MBBSEmu.Memory;
using MBBSEmu.Module;
using MBBSEmu.Reports;
using MBBSEmu.Session;
using MBBSEmu.Session.Attributes;
using MBBSEmu.Session.Enums;
using MBBSEmu.Session.Rlogin;
using MBBSEmu.TextVariables;
using MBBSEmu.Util;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Threading;

namespace MBBSEmu.HostProcess
{
    /// <summary>
    ///     MbbsHost acts as the Host Process would in MajorBBS or Worldgroup.
    ///
    ///     This is the focal point of all this MBBSEmu, as it handles:
    ///     - Loading Modules
    ///     - Applying Relocation Records for Exported Functions
    ///     - Adding incoming connections to a Channel
    ///     - Processing the main MajorBBS/Worldgroup event loop
    /// </summary>
    public class MbbsHost : IMbbsHost, IDisposable
    {
        // MMEXTEND: cache the player struct segment per channel so we don't
        // get drift onto a coincidental (map, room) match in some unrelated
        // allocation. Cleared on stale-read (struct moved or freed).
        private static readonly System.Collections.Concurrent.ConcurrentDictionary<ushort, ushort>
            PlayerStructSegByChannel = new();

        // Last (map, room) we reported back via `rm`. Used by the smart-wait
        // so we can detect "the previous move hasn't applied yet" and briefly
        // poll the player struct until it changes (capped).
        private static readonly System.Collections.Concurrent.ConcurrentDictionary<ushort, (int Map, int Room)>
            LastReportedLocByChannel = new();

        // True when the most recent typed input on this channel was a
        // movement direction. Set by the move-input detector below; checked
        // and cleared by the `rm` interceptor's smart-wait.
        private static readonly System.Collections.Concurrent.ConcurrentDictionary<ushort, bool>
            MovePendingByChannel = new();


        private static bool IsMoveCommand(string typed)
        {
            switch (typed)
            {
                case "n": case "s": case "e": case "w":
                case "ne": case "nw": case "se": case "sw":
                case "u": case "d":
                case "up": case "down":
                case "north": case "south": case "east": case "west":
                case "northeast": case "northwest":
                case "southeast": case "southwest":
                    return true;
                default: return false;
            }
        }

        public IMessageLogger Logger { get; init; }
        public IClock Clock { get; init; }

        /// <summary>
        ///     Dictionary containing all active Channels
        /// </summary>
        private readonly PointerDictionary<SessionBase> _channelDictionary;

        /// <summary>
        ///     Dictionary containing all added Modules
        /// </summary>
        private readonly Dictionary<string, MbbsModule> _modules;

        /// <summary>
        ///     Dictionary containing all Exported Functions
        /// </summary>
        private readonly Dictionary<string, IExportedModule> _exportedFunctions;

        /// <summary>
        ///     Boolean denoting if the Host is Running or Not
        /// </summary>
        private bool _isRunning;

        /// <summary>
        ///     Stopwatch tracking wall time for Real Time Events
        /// </summary>
        private readonly Stopwatch _realTimeStopwatch;

        /// <summary>
        ///     Host Routines for Non-Module Status (Menus, Signup, etc.)
        /// </summary>
        private readonly IEnumerable<IHostRoutine> _mbbsRoutines;

        /// <summary>
        ///     Routines for Global Commands to be intercepted while logged in
        /// </summary>
        private readonly IEnumerable<IGlobalRoutine> _globalRoutines;

        /// <summary>
        ///     Queue of incoming sessions not added to a Channel yet
        /// </summary>
        private readonly Queue<SessionBase> _incomingSessions;

        /// <summary>
        ///     Configuration Class giving access to the appsettings.json file
        /// </summary>
        private readonly AppSettingsManager _configuration;

        /// <summary>
        ///     Time of day that the cleanup routine will trigger
        /// </summary>
        private readonly TimeSpan _cleanupTime;

        /// <summary>
        ///     Timer that triggers when nightly cleanup should occur
        /// </summary>
        private readonly Timer _cleanupTimer;

        /// <summary>
        ///     Timer that triggers when nightly cleanup warning messages should start
        /// </summary>
        private Timer _cleanupWarningTimer;

        /// <summary>
        ///     Amount of time to start warning before cleanup grace period ends.
        /// </summary>
        private const int CleanupWarningInitialMinutes = 5;

        /// <summary>
        ///     Track minutes left until the nightly cleanup occurs.
        /// </summary>
        private int _cleanupWarningMinutesRemaining = CleanupWarningInitialMinutes;

        /// <summary>
        ///     Amount of time to give as a grace period to logoff after nightly cleanup.
        /// </summary>
        private const int CleanupGracePeriodMinutes = 10;
        private readonly TimeSpan _cleanupGracePeriod = TimeSpan.FromMinutes(CleanupGracePeriodMinutes);


        /// <summary>
        ///     Timer that sets _timerEvent on a set interval, controlled by Timer.Hertz
        /// </summary>
        private readonly Timer _tickTimer;
        private readonly EventWaitHandle _timerEvent;

        /// <summary>
        ///     Flag that controls whether the main loop will perform a nightly cleanup
        /// </summary>
        private bool _performCleanup = false;
        private EventWaitHandle _cleanupRestartEvent = null;

        /// <summary>
        ///     Global Cache of objects maintained and accessible everywhere within the process
        /// </summary>
        private readonly IGlobalCache _globalCache;

        /// <summary>
        ///     File Utility used for safely handling cross-platform File operations
        /// </summary>
        private readonly IFileUtility _fileUtility;

        /// <summary>
        ///     Main Worker Thread that processes the main loop within MBBSEmu
        /// </summary>
        private Thread _workerThread;

        /// <summary>
        ///     Repository for Account Keys related to Accounts within MBBSEmu
        /// </summary>
        private readonly IAccountKeyRepository _accountKeyRepository;

        /// <summary>
        ///     Repository for the MBBSEmu Accounts Database
        /// </summary>
        private readonly IAccountRepository _accountRepository;

        /// <summary>
        ///     Text Variable Service used to process Global Text Variables
        /// </summary>
        private readonly ITextVariableService _textVariableService;

        /// <summary>
        ///     Message Center used to handle notifications and events from other parts of the system
        /// </summary>
        private readonly IMessagingCenter _messagingCenter;

        public MbbsHost(IClock clock, LogFactory logger, IGlobalCache globalCache, IFileUtility fileUtility, IEnumerable<IHostRoutine> mbbsRoutines, AppSettingsManager configuration, IEnumerable<IGlobalRoutine> globalRoutines, IAccountKeyRepository accountKeyRepository, IAccountRepository accountRepository, PointerDictionary<SessionBase> channelDictionary, ITextVariableService textVariableService, IMessagingCenter messagingCenter)
        {
            Logger = logger.GetLogger<MessageLogger>();
            Clock = clock;
            _globalCache = globalCache;
            _fileUtility = fileUtility;
            _mbbsRoutines = mbbsRoutines;
            _configuration = configuration;
            _globalRoutines = globalRoutines;
            _channelDictionary = channelDictionary;
            _accountKeyRepository = accountKeyRepository;
            _accountRepository = accountRepository;
            _textVariableService = textVariableService;
            _messagingCenter = messagingCenter;

            Logger.Info("Constructing MBBSEmu Host...");

            _modules = new Dictionary<string, MbbsModule>();
            _exportedFunctions = new Dictionary<string, IExportedModule>();
            _realTimeStopwatch = Stopwatch.StartNew();
            _incomingSessions = new Queue<SessionBase>();

            //Setup Cleanup Restart Event
            _cleanupTime = _configuration.CleanupTime;
            _cleanupTimer = new Timer(_ => _performCleanup = true, null, NowUntil(_cleanupTime + _cleanupGracePeriod), TimeSpan.FromDays(1));
            _cleanupWarningTimer = SetupCleanupWarningTimer();

            if (_configuration.TimerHertz > 0)
            {
                _timerEvent = new AutoResetEvent(true);
                _tickTimer = new Timer(_ => _timerEvent.Set(), this, TimeSpan.Zero, TimeSpan.FromMilliseconds(1000 / configuration.TimerHertz));
            }

            //Setup Text Variables
            _textVariableService.SetVariable("SYSTEM_NAME", () => _configuration.BBSTitle);
            _textVariableService.SetVariable("SYSTEM_COMPANY", () => _configuration.BBSCompanyName);
            _textVariableService.SetVariable("SYSTEM_ADDRESS1", () => _configuration.BBSAddress1);
            _textVariableService.SetVariable("SYSTEM_ADDRESS2", () => _configuration.BBSAddress2);
            _textVariableService.SetVariable("SYSTEM_PHONE", () => _configuration.BBSDataPhone);
            _textVariableService.SetVariable("NUMBER_OF_LINES", () => _configuration.BBSChannels.ToString());
            _textVariableService.SetVariable("DATE", () => Clock.Now.ToString("M/d/yy"));
            _textVariableService.SetVariable("TIME", () => Clock.Now.ToString("t"));
            _textVariableService.SetVariable("TOTAL_ACCOUNTS", () => _accountRepository.GetAccounts().Count().ToString());
            _textVariableService.SetVariable("OTHERS_ONLINE", () => (GetUserSessions().Count - 1).ToString());
            _textVariableService.SetVariable("REG_NUMBER", () => _configuration.GSBLBTURNO);

            //Setup Message Subscribers
            _messagingCenter.Subscribe<SysopGlobal, string>(this, EnumMessageEvent.EnableModule, (sender, moduleId) => { EnableModule(moduleId); });
            _messagingCenter.Subscribe<SysopGlobal, string>(this, EnumMessageEvent.DisableModule, (sender, moduleId) => { DisableModule(moduleId); });
            _messagingCenter.Subscribe<MbbsModule, string>(this, EnumMessageEvent.DisableModule, (sender, moduleId) => { DisableModule(moduleId, true); });
            _messagingCenter.Subscribe<SysopGlobal>(this, EnumMessageEvent.Cleanup, (sender) => { _performCleanup = true; });

            Logger.Info("Constructed MBBSEmu Host!");
        }

        public void Dispose()
        {
            foreach (var module in _modules)
                module.Value.Dispose();

            _modules.Clear();
        }

        /// <summary>
        ///     Starts the MbbsHost Worker Thread
        /// </summary>
        public void Start(List<ModuleConfiguration> moduleConfigurations)
        {
            //Load Modules
            foreach (var m in moduleConfigurations)
                AddModule(new MbbsModule(_fileUtility, Clock, Logger, m, null, _messagingCenter));

            //Remove any modules that did not properly initialize
            foreach (var (_, value) in _modules.Where(m => m.Value.MainModuleDll.EntryPoints.Count == 1 && (bool)m.Value.ModuleConfig.ModuleEnabled))
            {
                Logger.Error($"{value.ModuleIdentifier} not properly initialized, Removing");
                moduleConfigurations.RemoveAll(x => x.ModuleIdentifier == value.ModuleIdentifier);
                _modules.Remove(value.ModuleIdentifier);
                foreach (var e in _exportedFunctions.Keys.Where(x => x.StartsWith(value.ModuleIdentifier)))
                    _exportedFunctions.Remove(e);
            }

            _isRunning = true;

            if (_workerThread == null)
            {
                _workerThread = new Thread(WorkerThread);
                _workerThread.Start();
            }
        }

        /// <summary>
        ///     Stops the MbbsHost worker thread
        /// </summary>
        public void Stop()
        {
            _isRunning = false;
            _cleanupTimer?.Dispose();
            _cleanupWarningTimer?.Dispose();
            _tickTimer?.Dispose();
            // this set must come after _isRunning is set to false, to trigger the exit of the
            // worker thread.
            _timerEvent?.Set();
        }

        public void ScheduleNightlyShutdown(EventWaitHandle eventWaitHandle)
        {
            _cleanupRestartEvent = eventWaitHandle;
            _performCleanup = true;
        }

        public void WaitForShutdown()
        {
            _workerThread.Join();
        }

        private void WaitForNextTick()
        {
            if (_timerEvent == null ||
                _channelDictionary.Values.Any(session => session.DataFromClient.Count > 0 || session.DataToClient.Count > 0 || session.DataToProcess))
                return;

            _timerEvent.WaitOne();
        }

        public void TriggerProcessing() => _timerEvent?.Set();

        /// <summary>
        ///     This is the main MajorBBS/Worldgroup loop similar to how it actually functions with the software itself.
        ///
        ///     Because it was a DOS based software, it did not support threads/tasking, so all the events had to happen in
        ///     serial order as quickly as possible. For compatibility, we've replicated the process here as well.
        /// </summary>
        private void WorkerThread()
        {
            while (_isRunning)
            {
                WaitForNextTick();

                ProcessNightlyCleanup();

                //Handle Channels
                ProcessIncomingSessions();
                ProcessDisconnects();

                //Process Channel Events
                foreach (var session in _channelDictionary.Values)
                {
                    try {
                    //Process a single incoming byte from the client session
                    session.ProcessDataFromClient();

                    //Handle GSBL Chain of Events
                    if (!ProcessGSBLInputEvents(session))
                    {
                        session.DataToProcess = false;
                        continue;
                    }

                    //Handle Character based Events
                    if (session.DataToProcess)
                        ProcessIncomingCharacter(session);

                    //Global Command Handler
                    if (session.GetStatus() == EnumUserStatus.CR_TERMINATED_STRING_AVAILABLE && DoGlobalsAttribute.Get(session.SessionState))
                    {
                        //Transfer Input Buffer to Command Buffer, but don't clear it
                        session.InputBuffer.WriteByte(0x0);
                        session.InputCommand = session.InputBuffer.ToArray();

                        //Check for Internal System Globals
                        if (_globalRoutines.Any(g =>
                            g.ProcessCommand(session.InputCommand, session.Channel, _channelDictionary, _modules)))
                        {
                            session.Status.Enqueue(EnumUserStatus.RINGING);
                            session.InputBuffer.SetLength(0);

                            //Redisplay Main Menu prompt after global if session is at Main Menu
                            if (session.SessionState == EnumSessionState.MainMenuInput)
                            {
                                session.SessionState = EnumSessionState.MainMenuInputDisplay;
                            }

                            session.Status.Dequeue();
                            continue;
                        }

                        //Check for Module Globals
                        foreach (var m in _modules.Values.Where(x => x.GlobalCommandHandlers.Any()))
                        {
                            var result = Run(m.ModuleIdentifier,
                                m.GlobalCommandHandlers.First(), session.Channel);

                            //Command Not Processed
                            if (result == 0) continue;

                            //Otherwise dequeue the input status to denote we've handled it
                            session.Status.Dequeue();
                            break;

                        }
                    }

                    switch (session.SessionState)
                    {
                        case EnumSessionState.RloginEnteringModule:
                            {
                                ProcessLONROU_FromRlogin(session);
                                break;
                            }
                        //Initial call to STTROU when a User is Entering a Module
                        case EnumSessionState.EnteringModule:
                            {
                                ProcessSTTROU_EnteringModule(session);
                                break;
                            }

                        //Post-Login Display Routine
                        case EnumSessionState.LoginRoutines:
                            {
                                ProcessLONROU(session);
                                break;
                            }

                        //User is in the module, process all the in-module type of events
                        case EnumSessionState.InModule:
                            {
                                //Did BTUCHI or a previous command cause a status change?
                                if (session.GetStatus() == EnumUserStatus.CYCLE || session.GetStatus() == EnumUserStatus.OUTPUT_BUFFER_EMPTY)
                                {
                                    ProcessSTSROU(session);
                                    break;
                                }

                                //User Input Available? Invoke *STTROU
                                if (session.GetStatus() == EnumUserStatus.CR_TERMINATED_STRING_AVAILABLE)
                                {
                                    ProcessSTTROU(session);
                                }

                                //If the channel has been registered with BEGIN_POLLING
                                if (session.PollingRoutine != null)
                                {
                                    session.Status.Enqueue(EnumUserStatus.POLLING_STATUS);
                                    ProcessPollingRoutine(session);
                                    session.Status.Dequeue();
                                }

                                break;
                            }

                        //Check for any other session states, we handle these here as they are
                        //lower priority than handling "in-module" states
                        default:
                            {
                                foreach (var r in _mbbsRoutines)
                                    if (r.ProcessSessionState(session, _modules))
                                        break;

                            }
                            break;
                    }

                    //Mark Data Processing for this Channel as Complete
                    session.DataToProcess = false;
                    } catch (System.Exception sessionEx) {
                        // CRITICAL: a single session's exception MUST NOT kill the
                        // entire BBS worker thread. Before this guard, any unhandled
                        // exception in per-session code (e.g. FSD navigating off the
                        // end of the field list, or a buggy module exit path) would
                        // bubble all the way to the .NET runtime and terminate the
                        // process — disconnecting EVERY user and refusing new
                        // connections. Now we log, drop the offending session, and
                        // keep serving the others.
                        try {
                            Logger.Error($"[ch={session?.Channel}] worker iter threw: {sessionEx.GetType().Name}: {sessionEx.Message}");
                            Logger.Error(sessionEx.StackTrace ?? "(no stack)");
                            if (session != null) {
                                session.DataToProcess = false;
                                session.SessionState = EnumSessionState.LoggedOff;
                            }
                        } catch { /* never leak from the safety net */ }
                    }

                }

                //Process Timed/Real-Time Events
                ProcessRTKICK();
                ProcessRTIHDLR();
                ProcessSYSCYC();
                ProcessTasks();

                foreach (var c in _channelDictionary.Where(x => x.Value.Status.Count > 0))
                    c.Value.Status.Dequeue();
            }

            Shutdown();
        }

        private void Shutdown()
        {
            Logger.Info("SHUTTING DOWN");

            // kill all active sessions
            foreach (var session in _channelDictionary.Values)
            {
                session.Stop();
            }

            // let modules clean themselves up
            CallModuleRoutine("finrou", module => Logger.Info($"Calling shutdown routine on module {module.ModuleIdentifier}"));

            //clean up modules
            foreach (var m in _modules)
            {
                m.Value.Dispose();
                _modules.Remove(m.Key);

                var exportedFunctionsToRemove = _exportedFunctions.Keys.Where(x => x.StartsWith(m.Key)).ToList();

                foreach (var e in exportedFunctionsToRemove)
                {
                    _exportedFunctions[e].Dispose();
                    _exportedFunctions.Remove(e);
                }
            }
        }

        private void CallModuleRoutine(string routine, Action<MbbsModule> preRunCallback, ushort channel = ushort.MaxValue)
        {
            foreach (var m in _modules.Values.Where(x => (bool)x.ModuleConfig.ModuleEnabled))
            {
                if (!m.MainModuleDll.EntryPoints.TryGetValue(routine, out var routineEntryPoint)) continue;

                if (routineEntryPoint.Segment != 0 &&
                    routineEntryPoint.Offset != 0)
                {
#if DEBUG
                    Logger.Info($"Calling {routine} on module {m.ModuleIdentifier} for channel {channel}");
#endif

                    preRunCallback?.Invoke(m);

                    Run(m.ModuleIdentifier, routineEntryPoint, channel);
                }
            }
        }

        /// <summary>
        ///     Adds any incoming sessions to an available Channel
        /// </summary>
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private void ProcessIncomingSessions()
        {
            while (_incomingSessions.TryDequeue(out var incomingSession))
            {
                incomingSession.Channel = (ushort)_channelDictionary.Allocate(incomingSession);
                incomingSession.SessionTimer.Start();
                Logger.Info($"Added Session {incomingSession.SessionId} to channel {incomingSession.Channel}");
            }
        }

        /// <summary>
        ///     Removes any channels that have disconnected
        /// </summary>
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private void ProcessDisconnects()
        {
            // We only remove channels that are logged off
            RemoveSessions(session =>
                session.SessionState == EnumSessionState.LoggedOff);
        }

        private void RemoveSessions(Predicate<SessionBase> match)
        {
            // for removing channels sequentially, starting with the highest index to not break
            // _channelDictionary
            Stack<ushort> channelsToRemove = new Stack<ushort>();

            for (ushort i = 0; i < _channelDictionary.Count; i++)
            {
                //Because users might not be on sequential channels (0,1,3), we verify if the channel number
                //is even in use first.
                if (!_channelDictionary.ContainsKey(i) || !match(_channelDictionary[i])) continue;

                channelsToRemove.Push(i);
            }

            while (channelsToRemove.Count > 0)
            {
                ushort ch = channelsToRemove.Pop();
                try {
                    RemoveSession(ch);
                } catch (System.Exception ex) {
                    // Defensive: a session whose CancellationTokenSource was
                    // already disposed (e.g. socket abruptly torn down by
                    // peer while in a bad state) can crash CloseSocket.
                    // That used to take down the entire BBS — refusing new
                    // connections forever. Now: log, force-remove from the
                    // channel dict so we don't try again, keep serving.
                    try {
                        Logger.Error($"[RemoveSession ch={ch}] {ex.GetType().Name}: {ex.Message}");
                        _channelDictionary.Remove(ch);
                    } catch { /* never leak from safety net */ }
                }
            }
        }

        /// <summary>
        ///     When first entering a module, we need to set a couple first time variables before
        ///     invoking STTROU
        /// </summary>
        /// <param name="session"></param>
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private void ProcessSTTROU_EnteringModule(SessionBase session)
        {
            if (session.GetStatus() != EnumUserStatus.CR_TERMINATED_STRING_AVAILABLE)
            {
                session.Status.Clear();
                session.Status.Enqueue(EnumUserStatus.CR_TERMINATED_STRING_AVAILABLE);
            }

            session.SessionState = EnumSessionState.InModule;
            session.UsrPtr.State = session.CurrentModule.MainModuleDll.StateCode;
            ProcessSTTROU(session);
        }

        /// <summary>
        ///     Invokes routine registered as STTROU during MAJORBBS->REGISTER_MODULE() call
        ///
        ///     Method is invoked any time user enters input and hits ENTER/RETURN
        /// </summary>
        /// <param name="session"></param>
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private void ProcessSTTROU(SessionBase session)
        {
            //Transfer Input Buffer to Command Buffer
            //Null terminated already by Global Command Handler
            session.InputCommand = session.InputBuffer.ToArray();
            session.InputBuffer.SetLength(0);

            // MMEXTEND command-response buffer: any rm/abil/rmsnap reply we
            // compute below is stashed here and emitted AFTER sttrou runs,
            // matching the slot where wccmmud's own commands flush via
            // outprf. Emitting directly inside the interceptor (the old
            // behavior) injected our bytes mid-stream and corrupted the
            // framing of whatever wccmmud was emitting at the moment.
            byte[] pendingRmResponse = null;
            // When we handle rm/abil/rmsnap ourselves, set this so we SKIP
            // calling wccmmud's sttrou below. Otherwise sttrou runs with
            // the {0} we wrote into InputCommand, and wccmmud's default
            // behavior for empty input is to redraw the room — which
            // gives users a duplicate room paint on every walker step
            // (one from the move, one from our empty sttrou). The bug
            // looks like "you're sending a bare Enter after each step"
            // but it's actually wccmmud's reaction to no-input dispatch.
            bool skipSttrou = false;

            // Arm the room-display capture: only the FIRST rooms-file query
            // during this dispatch is the user's current room.
            if (session.CurrentModule?.ModuleIdentifier == "WCCMMUD")
                HostProcess.ExportedModules.Majorbbs.CaptureNextRoomByChannel[session.Channel] = true;

            // === ParaMUD-parity: `rm` interceptor (WCCMMUD only) ===
            // Reads the live per-channel VDA and emits Location:/Regen Time:/Room Illu:
            // in the exact ParaMUD format the MegaMUD+ walker expects.
            //
            // NMR's WCCUSERS record layout places MapNumber/RoomNum at byte offsets
            // 196/200 of the user struct. The same struct is mirrored into the VDA
            // at runtime BUT the offset within VDA where the user-struct anchor sits
            // is unconfirmed for the 16-bit DOS build. We log a hex window so the
            // first in-game `rm` test reveals where the real (map, room) live.
            if (session.CurrentModule?.ModuleIdentifier == "WCCMMUD"
                && session.InputCommand != null && session.InputCommand.Length > 0)
            {
                var typed = System.Text.Encoding.ASCII
                    .GetString(session.InputCommand)
                    .TrimEnd('\0', '\r', '\n', ' ')
                    .Trim()
                    .ToLowerInvariant();
                // Track when a movement command was just dispatched, so the
                // next `rm` knows to use smart-wait (the move handler may
                // not have updated +0xC8 yet).
                if (IsMoveCommand(typed))
                    MovePendingByChannel[session.Channel] = true;
                if (typed == "rmsnap")
                {
                    // Memory snapshot for player-struct hunt. Dump every populated
                    // segment of the protected-mode memory to /tmp so we can diff
                    // between two known rooms and find which bytes hold map/room.
                    try
                    {
                        int seqno;
                        unchecked
                        {
                            seqno = (int)(System.DateTime.UtcNow.Ticks / 10_000_000) % 100000;
                        }
                        var path = $"/tmp/rmsnap_{seqno}.bin";
                        using (var fs = System.IO.File.Create(path))
                        using (var bw = new System.IO.BinaryWriter(fs))
                        {
                            var pm = session.CurrentModule?.ProtectedMemory;
                            if (pm != null)
                            {
                                int dumped = 0;
                                for (int s = 0; s <= 0xFFFF; s++)
                                {
                                    if (!pm.HasSegment((ushort)s)) continue;
                                    var span = pm.VirtualToPhysical((ushort)s, 0);
                                    bw.Write((ushort)s);
                                    bw.Write((int)span.Length);
                                    bw.Write(span.ToArray());
                                    dumped++;
                                }
                                System.Console.Error.WriteLine($"[rmsnap] ch={session.Channel} wrote {path} ({dumped} segs)");
                            }
                        }
                        session.SendToClient($"\r\n[rmsnap] saved /tmp/rmsnap_{seqno}.bin\r\n");
                    }
                    catch (System.Exception ex)
                    {
                        System.Console.Error.WriteLine($"[rmsnap] error: {ex.Message}");
                    }
                    session.InputCommand = new byte[] { 0 };
                    skipSttrou = true;
                }
                else if (typed == "share" || typed == "shar" || typed == "sha"
                         || typed.StartsWith("share ") || typed.StartsWith("shar ")
                         || typed.StartsWith("sha "))
                {
                    // MMEXTEND bug-fix: disable the `share` command to close
                    // the long-standing encumbrance/coin exploit. Repeated
                    // shares of large coin amounts cause a character's
                    // encumbrance counter to roll over, letting them walk
                    // around freely while carrying millions of coins. The
                    // community fix is to block `share` outright (NMR/FU
                    // Globals route); doing it at the MBBSEmu intercept
                    // layer means no wccmmud.dll patch needed.
                    pendingRmResponse = System.Text.Encoding.ASCII.GetBytes(
                        "\r\nThe share command is disabled on this server.\r\n");
                    session.InputCommand = new byte[] { 0 };
                    skipSttrou = true;
                }
                else if (typed == "abil")
                {
                    // ParaMUD-parity `abil` command. Emits rm header + Race + Class +
                    // (Worn Items / Spell effects empty for now) + GrantedAbilities,
                    // formatted as Name(ID)<pad>VALUE per line, sections separated by
                    // blank lines.
                    try
                    {
                        var pm = session.CurrentModule?.ProtectedMemory;
                        if (pm == null) { session.InputCommand = new byte[] { 0 }; goto AbilDone; }

                        // Find player struct
                        byte[] playerStruct = null;
                        for (int s = 0; s <= 0xFFFF; s++)
                        {
                            if (!pm.HasSegment((ushort)s)) continue;
                            var span = pm.VirtualToPhysical((ushort)s, 0);
                            if (span.Length < 0x76E) continue;
                            int m = System.BitConverter.ToInt32(span.Slice(0xC4, 4));
                            int r = System.BitConverter.ToInt32(span.Slice(0xC8, 4));
                            if (m >= 1 && m <= 30 && r >= 1 && r <= 3000)
                            {
                                playerStruct = span.ToArray();
                                break;
                            }
                        }
                        if (playerStruct == null) { session.InputCommand = new byte[] { 0 }; goto AbilDone; }

                        int mapNum = System.BitConverter.ToInt32(playerStruct, 0xC4);
                        int roomNum = System.BitConverter.ToInt32(playerStruct, 0xC8);
                        int raceId = System.BitConverter.ToInt16(playerStruct, 0x90);
                        int classId = System.BitConverter.ToInt16(playerStruct, 0x92);

                        var sb = new System.Text.StringBuilder();
                        sb.Append($"\r\nLocation:            {mapNum},{roomNum}\r\n");
                        sb.Append("Regen Time:            1m 30s\r\n");
                        sb.Append("Room Illu:            -25 (50)\r\n");

                        // Helper: format a name(id) value line, pad name+id to col 27
                        void Emit(string name, int id, int val)
                        {
                            string left = $"{name}({id})";
                            if (left.Length < 27) left = left + new string(' ', 27 - left.Length);
                            sb.Append($"{left}{val,4}\r\n");
                        }

                        var modPath = session.CurrentModule.ModulePath;
                        // RACE section
                        sb.Append("Race\r\n");
                        ReadRaceClassAbilities(System.IO.Path.Combine(modPath, "WCCRACE.DB"),
                            raceId, /*idOff*/50, /*valOff*/72, Emit);
                        sb.Append("\r\n");

                        // CLASS section
                        sb.Append("Class\r\n");
                        ReadRaceClassAbilities(System.IO.Path.Combine(modPath, "WCCCLASS.DB"),
                            classId, /*idOff*/44, /*valOff*/74, Emit);
                        sb.Append("\r\n");

                        // WORN ITEMS / SPELL EFFECTS sections (empty for v1)
                        sb.Append("Worn Items\r\n\r\n");
                        sb.Append("Spell effects\r\n\r\n");

                        // GRANTED ABILITIES section — read +0x722 (IDs) and +0x75E (vals)
                        sb.Append("GrantedAbilities\r\n");
                        for (int i = 0; i < 30; i++)
                        {
                            short aid = System.BitConverter.ToInt16(playerStruct, 0x722 + i * 2);
                            short aval = System.BitConverter.ToInt16(playerStruct, 0x75E + i * 2);
                            if (aid != 0) Emit(AbilityName(aid), aid, aval);
                        }
                        sb.Append("\r\n");

                        // No trailing prompt — same reasoning as rm: abil is
                        // a silent command now and the prior tick's wccmmud
                        // prompt already covers the screen position.
                        pendingRmResponse = System.Text.Encoding.ASCII.GetBytes(sb.ToString());
                    }
                    catch (System.Exception ex)
                    {
                        System.Console.Error.WriteLine($"[abil] error: {ex.Message}");
                    }
                    session.InputCommand = new byte[] { 0 };
                    skipSttrou = true;
                    AbilDone: ;
                }
                else if (typed == "rm")
                {
                    // Live player-struct scan. wccmmud's _MOVE_USER decompile
                    // (Ghidra) showed:
                    //   local_14 = _GET_PLAYER(channel, 0x1280);   // 4736 bytes
                    //   *(int*)(local_14 + 0xC4) == current map
                    //   *(int*)(local_14 + 0xC8) == current room
                    // Segment number changes per session, so scan all allocated
                    // segments for any region whose (+0xC4, +0xC8) holds a valid
                    // (map, room) pair.
                    int mapNum = 0, roomNum = 0;
                    int pickedSeg = -1;
                    int matchCount = 0;
                    // Validates a candidate segment as the player struct: must have
                    // plausible map/room AND race(1..13)/class(1..15)/level(1..200).
                    // Random buffers won't satisfy ALL four fields at the same offsets.
                    static bool IsPlayerStruct(System.ReadOnlySpan<byte> span, out int m, out int r)
                    {
                        m = 0; r = 0;
                        if (span.Length < 0xCC) return false;
                        m = System.BitConverter.ToInt32(span.Slice(0xC4, 4));
                        r = System.BitConverter.ToInt32(span.Slice(0xC8, 4));
                        if (m < 1 || m > 30) return false;
                        if (r < 1 || r > 3000) return false;
                        int race = System.BitConverter.ToInt16(span.Slice(0x90, 2));
                        int cls  = System.BitConverter.ToInt16(span.Slice(0x92, 2));
                        int lvl  = System.BitConverter.ToInt16(span.Slice(0x94, 2));
                        if (race < 1 || race > 13) return false;
                        if (cls  < 1 || cls  > 15) return false;
                        if (lvl  < 1 || lvl  > 200) return false;
                        return true;
                    }
                    try
                    {
                        var pm = session.CurrentModule?.ProtectedMemory;
                        if (pm != null)
                        {
                            // 1) Cache hit fast path
                            if (PlayerStructSegByChannel.TryGetValue(session.Channel, out var cachedSeg))
                            {
                                if (pm.HasSegment(cachedSeg))
                                {
                                    var cspan = pm.VirtualToPhysical(cachedSeg, 0);
                                    if (IsPlayerStruct(cspan, out int cm, out int cr))
                                    {
                                        mapNum = cm; roomNum = cr; pickedSeg = cachedSeg;
                                        matchCount = -1; // sentinel: cached
                                    }
                                }
                                if (pickedSeg < 0) PlayerStructSegByChannel.TryRemove(session.Channel, out _);
                            }
                            // 2) Cold scan with strict validation
                            if (pickedSeg < 0)
                            {
                                for (int s = 0; s <= 0xFFFF; s++)
                                {
                                    if (!pm.HasSegment((ushort)s)) continue;
                                    var span = pm.VirtualToPhysical((ushort)s, 0);
                                    if (IsPlayerStruct(span, out int m, out int r))
                                    {
                                        matchCount++;
                                        if (pickedSeg < 0)
                                        {
                                            mapNum = m; roomNum = r; pickedSeg = s;
                                            PlayerStructSegByChannel[session.Channel] = (ushort)s;
                                        }
                                    }
                                }
                            }
                        }
                    }
                    catch { /* defensive */ }
                    // Async smart-wait: spin up a background task that polls
                    // the player struct off-thread (so MBBSEmu's main loop
                    // keeps running ticks that update +0xC8). When the room
                    // changes OR a timeout hits, emit the rm response.
                    //
                    // Only triggers when a move command was just dispatched
                    // AND the current read matches the last reported (stale).
                    // Otherwise emits immediately with current values.
                    bool wantWait = MovePendingByChannel.TryGetValue(session.Channel, out var pending) && pending;
                    MovePendingByChannel[session.Channel] = false;
                    bool staleMatch = wantWait
                        && pickedSeg >= 0
                        && LastReportedLocByChannel.TryGetValue(session.Channel, out var prev)
                        && prev.Map == mapNum && prev.Room == roomNum;
                    System.Console.Error.WriteLine(
                        $"[rm-trace] t={System.DateTime.UtcNow:HH:mm:ss.fff} ch={session.Channel} picked=0x{pickedSeg:X4}({mapNum},{roomNum}) matches={matchCount} wantWait={wantWait} staleMatch={staleMatch}");

                    if (staleMatch && pickedSeg >= 0)
                    {
                        // Struct still on the OLD room — wccmmud's move
                        // handler hasn't ticked yet. Wait on a BACKGROUND
                        // thread so the dispatch loop keeps running and
                        // wccmmud can actually update the struct. A sync
                        // wait would deadlock: blocking ProcessSTTROU
                        // starves the very tick that flips +0xC4/+0xC8.
                        // When the flip is detected, send Location: via
                        // SendToClient — by that time wccmmud's room desc
                        // has already flushed (it goes out during the
                        // move-handler tick that flipped the struct), so
                        // Location: lands AFTER "Obvious exits:" naturally.
                        var capturedPm = session.CurrentModule?.ProtectedMemory;
                        var capturedSeg = (ushort)pickedSeg;
                        var capturedMap = mapNum;
                        var capturedRoom = roomNum;
                        var capturedSession = session;
                        var capturedChannel = session.Channel;
                        System.Threading.Tasks.Task.Run(() =>
                        {
                            int m = capturedMap, r = capturedRoom;
                            var sw = System.Diagnostics.Stopwatch.StartNew();
                            bool settled = false;
                            while (sw.ElapsedMilliseconds < 4500)
                            {
                                System.Threading.Thread.Sleep(10);
                                if (capturedPm == null || !capturedPm.HasSegment(capturedSeg)) break;
                                var span2 = capturedPm.VirtualToPhysical(capturedSeg, 0);
                                if (span2.Length < 0xCC) break;
                                int m2 = System.BitConverter.ToInt32(span2.Slice(0xC4, 4));
                                int r2 = System.BitConverter.ToInt32(span2.Slice(0xC8, 4));
                                if (m2 != capturedMap || r2 != capturedRoom)
                                {
                                    m = m2; r = r2;
                                    settled = true;
                                    System.Console.Error.WriteLine(
                                        $"[rm-async] ch={capturedChannel} settled to ({m},{r}) after {sw.ElapsedMilliseconds}ms");
                                    break;
                                }
                            }
                            if (!settled)
                                System.Console.Error.WriteLine(
                                    $"[rm-async] ch={capturedChannel} TIMEOUT — still ({m},{r}) after {sw.ElapsedMilliseconds}ms");
                            // Cushion: wccmmud flips the player struct at the
                            // START of its movement tick but emits the room
                            // description (Also here:, Obvious exits:) via
                            // outprf a few internal cycles later. If we send
                            // Location: the instant we detect the flip, it
                            // can win the race into DataToClient and land
                            // before the room block — then MegaMUD's entity
                            // array is empty when the walker's COMBAT_WAIT
                            // check runs, and combat doesn't fire. 100ms is
                            // invisible inside an async wait that's already
                            // 1+ second long.
                            if (settled)
                                System.Threading.Thread.Sleep(100);
                            LastReportedLocByChannel[capturedChannel] = (m, r);
                            // No trailing prompt: the move handler already
                            // emitted wccmmud's real (class-appropriate)
                            // prompt before our async fires, and the walker
                            // filters the Location/Regen/Illu lines but not
                            // a prompt, so adding one would double up.
                            var asyncResp =
                                $"\r\nLocation:            {m},{r}\r\n" +
                                "Regen Time:            1m 30s\r\n" +
                                "Room Illu:            -25 (50)\r\n";
                            try { capturedSession.SendToClient(asyncResp); }
                            catch (System.Exception ex)
                            {
                                System.Console.Error.WriteLine($"[rm-async] send err: {ex.Message}");
                            }
                        });
                    }
                    else
                    {
                        // Struct already shows the new room (or no move just
                        // dispatched). STAGE the reply for post-sttrou flush
                        // so framing matches a real wccmmud command response.
                        // Append the [HP=N/MA=N] prompt so the client sees
                        // the same response shape as any normal wccmmud
                        // command (look, stat, direction, etc.). Without
                        // this the client redraws the room mid-flow because
                        // it thinks no prompt was issued.
                        // Offsets from Ghidra _PRF_PROMPT decomp:
                        //   +0xB0 (uint16) = current HP
                        //   +0xBA (uint16) = current Mana
                        LastReportedLocByChannel[session.Channel] = (mapNum, roomNum);
                        // No trailing prompt: rm is a silent command now
                        // (skipSttrou path), so the prior tick's wccmmud
                        // prompt is already on screen above us. Adding our
                        // own would double up (and would use a fixed
                        // [HP=N/MA=N]: format that doesn't match the real
                        // class-appropriate prompt — e.g. thieves get
                        // [HP=N]: only).
                        pendingRmResponse = System.Text.Encoding.ASCII.GetBytes(
                            $"\r\nLocation:            {mapNum},{roomNum}\r\n" +
                            "Regen Time:            1m 30s\r\n" +
                            "Room Illu:            -25 (50)\r\n");
                    }
                    // Hand the response back ourselves and skip sttrou: wccmmud
                    // never sees "rm", so the unknown-command → say fallback
                    // can't fire and there's no stealth break. Chars typed
                    // before Enter were already echoed live by wccmmud's
                    // char-input handler, so the user already sees
                    // `[HP=X/MA=Y]:rm` on screen; pendingRmResponse opens
                    // with \r\n to advance past it.
                    session.InputCommand = new byte[] { 0 };
                    skipSttrou = true;
                }
            }
            // === end rm interceptor ===

            // Run sttrou unless an MMEXTEND intercept handled the line
            // itself. Skipping prevents wccmmud from running its parser
            // on commands it doesn't know about (rm/abil/etc), which
            // would otherwise fall through to the say-broadcast path
            // and break stealth.
            ushort result = 1;
            if (!skipSttrou)
            {
                result = Run(session.CurrentModule.ModuleIdentifier,
                    session.CurrentModule.MainModuleDll.EntryPoints["sttrou"], session.Channel);
            }

            // Flush any deferred MMEXTEND response NOW — sttrou has already
            // returned (so wccmmud's outprf for THIS dispatch has already
            // queued whatever it was going to emit), and we're emitting
            // before the prompt char. This is the same slot a real wccmmud
            // command would output its response, so framing is preserved.
            if (pendingRmResponse != null && pendingRmResponse.Length > 0)
                session.SendToClient(pendingRmResponse);

            //Finally, display prompt character if one is set
            if (session.PromptCharacter > 0)
                session.SendToClient(new[] { session.PromptCharacter });

            //stt returned an exit code -- we're done
            if (result == 0)
                ExitModule(session);
        }

        // === MMEXTEND `abil` helpers ===

        // Read race or class record by ID, decode AbilityA + AbilityB arrays, emit each.
        private void ReadRaceClassAbilities(string dbPath, int recordId, int idArrayOff,
            int valArrayOff, System.Action<string, int, int> emit)
        {
            if (!System.IO.File.Exists(dbPath)) return;
            try
            {
                var connStr = $"Data Source=file:{dbPath}?mode=ro&immutable=1;Cache=Shared";
                using var c = new Microsoft.Data.Sqlite.SqliteConnection(connStr);
                c.Open();
                using var cmd = c.CreateCommand();
                cmd.CommandText = "SELECT data FROM data_t";
                using var rdr = cmd.ExecuteReader();
                while (rdr.Read())
                {
                    var rowBytes = (byte[])rdr["data"];
                    if (rowBytes.Length < valArrayOff + 20) continue;
                    short rid = System.BitConverter.ToInt16(rowBytes, 0);
                    if (rid != recordId) continue;
                    for (int i = 0; i < 10; i++)
                    {
                        short aid = System.BitConverter.ToInt16(rowBytes, idArrayOff + i * 2);
                        short aval = System.BitConverter.ToInt16(rowBytes, valArrayOff + i * 2);
                        if (aid != 0) emit(AbilityName(aid), aid, aval);
                    }
                    break;
                }
            }
            catch (System.Exception ex)
            {
                System.Console.Error.WriteLine($"[abil:db] {dbPath}: {ex.Message}");
            }
        }

        // Ability ID → name table (from MMUD-Explorer's GetAbilityName).
        private static string AbilityName(int id) => id switch
        {
            1 => "Damage", 2 => "AC", 3 => "Resist-Cold", 4 => "MaxDamage",
            5 => "Resist-Fire", 6 => "Enslave", 7 => "DR", 8 => "DrainLife",
            9 => "Shadow", 10 => "ACBlur", 11 => "AlterEnergyLevel", 12 => "Summon",
            13 => "Illu", 14 => "RoomIllu", 17 => "Damage(-MR)", 18 => "Heal",
            19 => "Poison", 20 => "CurePoison", 21 => "ImmuPoison", 22 => "Accuracy",
            23 => "AffectsUndeadOnly", 24 => "ProtEvil", 25 => "ProtGood",
            26 => "DetectMagic", 27 => "Stealth", 28 => "Magical", 29 => "Punch",
            30 => "Kick", 31 => "Bash", 32 => "Smash", 33 => "Killblow", 34 => "Dodge",
            35 => "JumpKick", 36 => "M.R.", 37 => "Picklocks", 38 => "Tracking",
            39 => "Thievery", 40 => "FindTraps", 41 => "DisarmTraps", 42 => "LearnSp",
            43 => "CastsSp", 44 => "Intel", 45 => "Wisdom", 46 => "Strength",
            47 => "Health", 48 => "Agility", 49 => "Charm", 51 => "AntiMagic",
            52 => "EvilInCombat", 53 => "BlindingLight", 54 => "IlluTarget",
            55 => "AlterLightDuration", 56 => "RechargeItem", 57 => "SeeHidden",
            58 => "Crits", 59 => "ClassOk", 60 => "Fear", 61 => "AffectExit",
            62 => "AlterEvilChance", 63 => "AlterExperience", 64 => "AddCP",
            65 => "Resist-Stone", 66 => "Resist-Lightning", 67 => "Quickness",
            68 => "Slowness", 69 => "MaxMana", 70 => "Spellcasting", 71 => "Confusion",
            72 => "ShockShield", 73 => "DispellMagic", 74 => "HoldPerson",
            75 => "Paralyze", 76 => "Mute", 77 => "Perception", 78 => "Animal",
            79 => "MageBind", 80 => "AffectsAnimalsOnly", 81 => "Freedom",
            82 => "Cursed", 83 => "CursedMajor", 84 => "RemoveCurse", 85 => "Shatter",
            86 => "Quality", 87 => "Speed", 88 => "MaxHP", 89 => "PunchAcc",
            90 => "KickAcc", 91 => "JumpKAcc", 92 => "PunchDmg", 93 => "KickDmg",
            94 => "JumpKDmg", 95 => "Slay", 96 => "Encum", 97 => "GoodOnly",
            98 => "EvilOnly", 99 => "AlterDRpercent", 100 => "LoyalItem",
            102 => "RaceStealth", 103 => "ClassStealth", 104 => "DefenseModifier",
            105 => "Accuracy2", 106 => "Accuracy3", 107 => "BlindUser",
            108 => "AffectsLivingOnly", 109 => "NonLiving", 110 => "NotGood",
            111 => "NotEvil", 112 => "NeutralOnly", 113 => "NotNeutral",
            114 => "%Spell", 116 => "BSAccu", 117 => "BsMinDmg", 118 => "BsMaxDmg",
            119 => "DelAtMaint", 121 => "Recharge", 122 => "RemovesSpell",
            123 => "HPRegen", 124 => "NegateAbility", 135 => "MinLevel",
            136 => "MaxLevel", 138 => "RoomVisible", 139 => "SpellImmu",
            140 => "TeleportRoom", 141 => "TeleportMap", 142 => "HitMagic",
            143 => "ClearItem", 145 => "ManaRegen", 146 => "MonsGuards",
            147 => "Resist-Water", 148 => "TextBlock", 149 => "RemoveAtMaint",
            150 => "HealMana", 151 => "EndCast", 152 => "Rune", 153 => "KillSpell",
            154 => "VisibleAtMaint", 160 => "GiveTempSpell", 174 => "StealMana",
            175 => "StealHPToMP", 176 => "StealMPtoHP", 177 => "SpellColours",
            178 => "Shadowform", 179 => "FindTrapsValue", 180 => "PickLocksValue",
            185 => "NoAttackIfItemNum", 186 => "PerfectStealth", 187 => "Meditate",
            _ => $"Ability"
        };

        /// <summary>
        ///     Invoked when a users STTROU returns 0, which means they're exiting
        ///
        ///     This method handles session, input buffer, and status cleanup returning the
        ///     user to the main menu with a clean session
        /// </summary>
        /// <param name="session"></param>
        private void ExitModule(SessionBase session)
        {
            //Clear VDA
            Array.Clear(session.VDA, 0, Majorbbs.VOLATILE_DATA_SIZE);

            session.SessionState = EnumSessionState.MainMenuDisplay;
            session.CurrentModule = null;
            session.CharacterInterceptor = null;
            session.PromptCharacter = 0;

            //Reset States
            session.Status.Clear();
            session.UsrPtr.Substt = 0;

            //Clear the Input Buffer
            session.InputBuffer.SetLength(0);

            //Clear any data waiting to be processed from the client
            session.InputBuffer.SetLength(0);

            //Is this an Rlogin session and its specific to a module, log them off
            if (session.SessionType == EnumSessionType.Rlogin &&
                !string.IsNullOrEmpty(((RloginSession)session).ModuleIdentifier))
            {
                session.SessionState = EnumSessionState.ConfirmLogoffDisplay;
            }
        }

        /// <summary>
        ///     Invokes routine registered as LONROU during MAJORBBS->REGISTER_MODULE() call for
        ///     all modules, and then enters module specified by ModuleIdentifier.
        ///
        ///     Executes on the given channel once after a user successfully logs in.
        /// </summary>
        private void ProcessLONROU_FromRlogin(SessionBase session)
        {
            session.OutputEnabled = false; // always disabled for RLogin

            CallModuleRoutine("lonrou", preRunCallback: null, session.Channel);

            session.SessionState = EnumSessionState.EnteringModule;
            session.OutputEnabled = true;
        }

        /// <summary>
        ///     Invokes routine registered as LONROU during MAJORBBS->REGISTER_MODULE() call
        ///
        ///     Executes on the given channel once after a user successfully logs in.
        /// </summary>
        /// <param name="session"></param>
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private void ProcessLONROU(SessionBase session)
        {
            session.OutputEnabled = _configuration.ModuleDoLoginRoutine;

            CallModuleRoutine("lonrou", preRunCallback: null, session.Channel);

            session.SessionState = EnumSessionState.MainMenuDisplay;
            session.OutputEnabled = true;
        }

        /// <summary>
        ///     When BTUCHE is enabled on a given channel, the registered BTUCHI routine is invoked
        ///     whenever the Echo Buffer to a given channel is empty (after everything that needed to
        ///     be sent, has been sent)
        ///
        ///     The registered BTUCHI routine is invoked with a keycode of -1, denoting the invocation
        ///     came from BTUCHE
        /// </summary>
        /// <param name="session"></param>
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private void ProcessEchoEmptyInvoke(SessionBase session)
        {
            session.EchoEmptyInvoke = false;

            //Call BTUCHI when Echo Buffer Is Empty
            var initialStackValues = new Queue<ushort>(2);
            initialStackValues.Enqueue(0xFFFF); //-1 is the keycode passed in
            initialStackValues.Enqueue(session.Channel);

            var _ = Run(session.CurrentModule.ModuleIdentifier,
                session.CharacterInterceptor,
                session.Channel, true,
                initialStackValues);
        }

        /// <summary>
        ///     Invokes routine registered using GSBL->BTUCHI()
        ///
        ///     BTUCHI is a character interceptor method which intercepts every incoming character on a channel
        ///     and processes it before it's sent to the buffer. In the case of MBBSEmu, since the byte is ALREADY in
        ///     the buffer, we overwrite the last byte received with the result of the registered BTUCHI routine
        /// </summary>
        /// <param name="session"></param>
        /// <returns></returns>
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private ushort ProcessBTUCHI(SessionBase session)
        {
            //Create Parameters for BTUCHI Routine
            var initialStackValues = new Queue<ushort>(2);
            initialStackValues.Enqueue(session.CharacterReceived);
            initialStackValues.Enqueue(session.Channel);

            var result = Run(session.CurrentModule.ModuleIdentifier,
                session.CharacterInterceptor,
                session.Channel, true,
                initialStackValues);

            //Only Take the low bytes, as it's the return character and not every routine/compiler
            //would clear out AH before assigning AL
            result &= 0xFF;

            if (result == 0)
                return result;

            session.CharacterProcessed = (byte)result;

            if (session.CharacterProcessed == 0xD)
            {
                session.Status.Clear();
                session.Status.Enqueue(EnumUserStatus.CR_TERMINATED_STRING_AVAILABLE);
            }

            return result;
        }

        /// <summary>
        ///     Invokes routine registered as STSROU during MAJORBBS->REGISTER_MODULE() call
        ///
        ///     The registered STSROU is invoked any time there is a status change or deferred processing
        ///     using a channel Status code of 240 or 5. Most modules that utilize this use it as a method to
        ///     rapidly call the module to perform actions at a calculated interval
        /// </summary>
        /// <param name="session"></param>
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private void ProcessSTSROU(SessionBase session)
        {
            Run(session.CurrentModule.ModuleIdentifier, session.CurrentModule.MainModuleDll.EntryPoints["stsrou"],
                session.Channel);
        }

        /// <summary>
        ///     Invokes routine registered during MAJORBBS->BEGIN_POLLING()
        ///
        ///     Method registered using BEGIN_POLLING() is called as often as possible to poll for a specific event
        ///     and will not stop polling until STOP_POLLING() is invoked
        /// </summary>
        /// <param name="session"></param>
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private void ProcessPollingRoutine(SessionBase session)
        {
            Run(session.CurrentModule.ModuleIdentifier, session.PollingRoutine, session.Channel,
                true);
        }
        /// <summary>
        ///     Invokes routine registered during MAJORBBS->RTKICK()
        ///
        ///     Methods registered using RTKICK are automatically invoked after a specified delay (in seconds). Methods
        ///     only execute once and are then discarded.
        /// </summary>
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private void ProcessRTKICK()
        {
            //Check for any rtkick routines
            foreach (var module in _modules.Values.Where(m => (bool)m.ModuleConfig.ModuleEnabled))
            {
                if (module.RtkickRoutines.Count == 0) continue;

                foreach (var (key, value) in module.RtkickRoutines.ToList())
                {
                    if (!value.Executed && value.Elapsed.ElapsedMilliseconds > value.Delay * 1000)
                    {
#if DEBUG
                        Logger.Info($"Running RTKICK-{key}: {value}");
#endif
                        Run(module.ModuleIdentifier, value, ushort.MaxValue);

                        value.Elapsed.Stop();
                        value.Executed = true;
                        module.RtkickRoutines.Remove(key);
                    }
                }
            }
        }

        /// <summary>
        ///     Invokes routine registered during MAJORBBS->RTIHDLR()
        ///
        ///     Methods registered with RTIHDLR execute at 18hz (every ~55ms) and on the original DOS MajorBBS/Worldgroup
        ///     were executed at the DOS interrupt level. This is why on later Windows versions of worldgroup, any Module
        ///     that relied on RTIHDLR wouldn't work.
        ///
        ///     Unlike RTKICK, methods registered with RTIHDLR() only need to be registered once and will run until the BBS
        ///     is shut down.
        /// </summary>
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private void ProcessRTIHDLR()
        {
            //Too soon? Bail.
            if (_realTimeStopwatch.ElapsedMilliseconds <= 55) return;

            foreach (var m in _modules.Values.Where(m => (bool)m.ModuleConfig.ModuleEnabled))
            {
                if (m.RtihdlrRoutines.Count == 0) continue;

                foreach (var r in m.RtihdlrRoutines)
                {
                    Run(m.ModuleIdentifier, r.Value, ushort.MaxValue);
                }
            }

            _realTimeStopwatch.Restart();
        }

        /// <summary>
        ///     Processes the routine set to a modules specified SYSCYC Pointer
        /// </summary>
        private void ProcessSYSCYC()
        {
            foreach (var m in _modules.Values.Where(m => (bool)m.ModuleConfig.ModuleEnabled))
            {
                var syscycPointer = m.Memory.GetPointer(m.Memory.GetVariablePointer("SYSCYC"));
                if (syscycPointer == FarPtr.Empty) continue;

                Run(m.ModuleIdentifier, syscycPointer, ushort.MaxValue);
            }
        }

        /// <summary>
        ///     Invokes routine registered during MAJORBBS->INITASK()
        ///
        ///     Similar to BEGIN_POLLING() or RTIHDLR(), methods registered with INITASK() are invoked very quickly as often
        ///     as possible.
        /// </summary>
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private void ProcessTasks()
        {
            //Run task routines
            foreach (var m in _modules.Values.Where(m => (bool)m.ModuleConfig.ModuleEnabled))
            {
                if (m.TaskRoutines.Count == 0) continue;

                foreach (var r in m.TaskRoutines)
                {
                    var initialStackValues = new Queue<ushort>(1);
                    initialStackValues.Enqueue((ushort)r.Key);
                    Run(m.ModuleIdentifier, r.Value, ushort.MaxValue, false, initialStackValues);
                }
            }
        }

        /// <summary>
        ///     Processes the incoming character from a channel through the GSBL series of events.
        ///
        ///     In an actual MBBS System, these events are all triggered before MBBS even "gets" the character
        ///     from the serial channel.
        /// </summary>
        /// <param name="session"></param>
        /// <returns>
        ///     TRUE == Data Processed, Continue
        ///     FALSE == Data Processed, Halt Processing on Channel
        /// </returns>
        private bool ProcessGSBLInputEvents(SessionBase session)
        {
            //Quick Exit
            if (session.CharacterInterceptor == null)
                return true;

            //Invoke BTUCHI registered routine if one exists
            if (session.DataToProcess)
            {
                return ProcessBTUCHI(session) != 0;
            }

            //Invoke routine registered with BTUCHE if it has been registered and the criteria is met
            if (session.EchoEmptyInvokeEnabled && session.EchoEmptyInvoke)
            {
                ProcessEchoEmptyInvoke(session);
                return true;
            }

            return true;
        }

        /// <summary>
        ///     Processes the incoming character from a given channel and takes specific action depending on the
        ///     character and the current state of the channel.
        ///
        ///     Echoing of the character back to the channel is also handled within this method
        /// </summary>
        /// <param name="session"></param>
        private void ProcessIncomingCharacter(SessionBase session)
        {
            //Handling Incoming Characters
            switch (session.CharacterReceived)
            {
                //Backspace
                case 127 when session.SessionState == EnumSessionState.InModule:
                case 0x8:
                    {
                        if (session.InputBuffer.Length > 0)
                        {
                            session.SendToClient(new byte[] { 0x08, 0x20, 0x08 });
                            session.InputBuffer.SetLength(session.InputBuffer.Length - 1);
                        }
                        break;
                    }

                //Enter or Return
                case 0xD when (session.SessionState != EnumSessionState.InFullScreenDisplay && session.SessionState != EnumSessionState.InFullScreenEditor):
                    {
                        //If we're in transparent mode or BTUCHI has changed the character to null, don't echo
                        if (!session.TransparentMode && session.CharacterProcessed > 0)
                            session.SendToClient(new byte[] { 0xD, 0xA });

                        //If BTUCHI Injected a deferred Execution Status, respect that vs. processing the input
                        if (session.GetStatus() == EnumUserStatus.CYCLE)
                        {
                            //If we're cycling, ignore \r for triggering STTROU and add it to the input buffer for STSROU to handle
                            if (session.TransparentMode)
                            {
                                session.InputBuffer.WriteByte(session.CharacterProcessed);
                                break;
                            }

                            //Set Status == 3, which means there is a Command Ready
                            session.Status.Clear(); //Clear the 240
                            session.Status.Enqueue(EnumUserStatus.CR_TERMINATED_STRING_AVAILABLE); //Enqueue Status of 3
                            session.EchoSecureEnabled = false;
                            break;
                        }

                        //Always Enqueue Input Ready, if one already not queued (from BTUCHI)
                        if(session.GetStatus() != EnumUserStatus.CR_TERMINATED_STRING_AVAILABLE)
                            session.Status.Enqueue(EnumUserStatus.CR_TERMINATED_STRING_AVAILABLE);

                        break;
                    }

                case 0xA: //Ignore Linefeed
                case 0x0: //Ignore Null
                    break;
                default:
                    {
                        //If Secure Echo is on, enforce maximum length
                        if (session.EchoSecureEnabled && session.InputBuffer.Length >= session.ExtUsrAcc.wid)
                            break;

                        if (session.CharacterProcessed > 0)
                        {
                            session.InputBuffer.WriteByte(session.CharacterProcessed);

                            //If the client is in transparent mode, don't echo
                            if (session.TransparentMode)
                                break;

                            //FSD handles its own echo
                            if (session.SessionState == EnumSessionState.InFullScreenDisplay ||
                                session.SessionState == EnumSessionState.InFullScreenEditor)
                                break;

                            if (session.Status.Count == 0 || session.GetStatus() == EnumUserStatus.UNUSED || session.GetStatus() == EnumUserStatus.RINGING ||
                               session.GetStatus() == EnumUserStatus.POLLING_STATUS)
                            {

                                {
                                    //Check for Secure Echo being Enabled
                                    session.SendToClient(session.EchoSecureEnabled
                                        ? new[] { session.ExtUsrAcc.ech }
                                        : new[] { session.CharacterReceived });
                                }
                            }

                        }

                        break;
                    }
            }
        }

        /// <summary>
        ///     Runs the specified EXE file during cleanup by modules that require one
        /// </summary>
        /// <param name="modulePath"></param>
        /// <param name="cmdline"></param>
        private void RunProgram(string modulePath, string cmdline)
        {
            var exe = cmdline.Split(' ')[0];
            var args = cmdline.Split(' ').Skip(1).ToArray();
            exe = Path.ChangeExtension(exe, ".EXE");

            exe = _fileUtility.FindFile(modulePath, exe);

            Logger.Info($"Running auxiliary program: {cmdline}");

            var runtime = new ExeRuntime(
                            new Disassembler.MZFile(Path.Combine(modulePath, exe)),
                            Clock,
                            Logger,
                            _fileUtility,
                            modulePath,
                            sessionBase: null,
                            new TextReaderStream(Console.In),
                            new TextWriterStream(Console.Out),
                            new TextWriterStream(Console.Error));
            runtime.Load(args);
            runtime.Run();

            runtime.Dispose();
        }

        /// <summary>
        ///     Adds the specified module to the MBBS Host
        ///
        ///     This includes:
        ///     - Patching Relocation Information for Exported Modules
        ///     - Setting up Module Memory and loading Disassembly
        ///     - Executing Module "_INIT_" routine
        /// </summary>
        /// <param name="module"></param>
        public void AddModule(MbbsModule module)
        {
            Logger.Info($"({module.ModuleIdentifier}) Adding Module...");
            Logger.Info($"({module.ModuleIdentifier}) CRC32: {module.MainModuleDll.File.CRC32}");

            //Setup Exported Modules
            module.ExportedModuleDictionary.Add(Majorbbs.Segment, GetFunctions(module, "MAJORBBS"));
            module.ExportedModuleDictionary.Add(Galgsbl.Segment, GetFunctions(module, "GALGSBL"));
            module.ExportedModuleDictionary.Add(Phapi.Segment, GetFunctions(module, "PHAPI"));
            module.ExportedModuleDictionary.Add(Galme.Segment, GetFunctions(module, "GALME"));
            module.ExportedModuleDictionary.Add(Doscalls.Segment, GetFunctions(module, "DOSCALLS"));
            module.ExportedModuleDictionary.Add(Galmsg.Segment, GetFunctions(module, "GALMSG"));

            //Patch Relocation Information to Bytecode
            PatchRelocation(module);

            //Run Segments through AOT Decompiler & add them to Memory
            for (var i = 0; i < module.ModuleDlls.Count; i++)
            {
                var dll = module.ModuleDlls[i];

                //Only add the main module to the Modules List
                if (i == 0)
                    _modules[module.ModuleIdentifier] = module;

                foreach (var seg in dll.File.SegmentTable)
                {
                    var originalOrdinal = seg.Ordinal;
                    seg.Ordinal += dll.SegmentOffset;
                    module.ProtectedMemory.AddSegment(seg);
                    Logger.Debug($"({module.ModuleIdentifier}:{dll.File.FileName}:{originalOrdinal}) Segment {seg.Ordinal} ({seg.Data.Length} bytes) loaded!");
                }

                dll.StateCode = (short)(_modules.Count * 10 + i);
            }

            //Run INIT
            foreach (var dll in module.ModuleDlls.OrderBy(m => m.File.FileName))
            {
                if (!dll.EntryPoints.TryGetValue("_INIT_", out var entryPointer))
                    continue;

                foreach (var bbsup in module.Mdf.BBSUp)
                    RunProgram(module.ModulePath, bbsup);

                Run(module.ModuleIdentifier, entryPointer, ushort.MaxValue);
            }

            Logger.Info($"({module.ModuleIdentifier}) Module Added!");
        }

        /// <summary>
        ///     Gets the Registered instance of the specified Module within the MBBS Host Process
        /// </summary>
        /// <param name="uniqueIdentifier"></param>
        /// <returns></returns>
        public MbbsModule GetModule(string uniqueIdentifier) => _modules[uniqueIdentifier];

        /// <summary>
        ///     Assigns a Channel # to a session and adds it to the Channel Dictionary
        /// </summary>
        /// <param name="session"></param>
        public void AddSession(SessionBase session)
        {
            Logger.Info($"Session {session.SessionId} added to incoming queue");
            _incomingSessions.Enqueue(session);
        }

        /// <summary>
        ///     Removes a Channel # from the Channel Dictionary
        /// </summary>
        /// <param name="channel"></param>
        /// <returns></returns>
        public bool RemoveSession(ushort channel)
        {
            if (!_channelDictionary.ContainsKey(channel))
            {
                return false;
            }

            Logger.Info($"Removing Channel: {channel}");

            CallModuleRoutine("huprou", preRunCallback: null, channel);

            var session = _channelDictionary[channel];
            session.Stop();
            session.SessionState = EnumSessionState.Disconnected;

            _channelDictionary.Remove(channel);

            return true;
        }

        /// <summary>
        ///     Runs the specified routine in the specified module
        /// </summary>
        /// <param name="moduleName"></param>
        /// <param name="routine"></param>
        /// <param name="channelNumber"></param>
        /// <param name="simulateCallFar"></param>
        /// <param name="initialStackValues"></param>
        private ushort Run(string moduleName, FarPtr routine, ushort channelNumber, bool simulateCallFar = false, Queue<ushort> initialStackValues = null)
        {
            var resultRegisters = _modules[moduleName].Execute(routine, channelNumber, simulateCallFar, false, initialStackValues);
            return resultRegisters.AX;
        }

        /// <summary>
        ///     Returns the specified Exported Module for the specified MajorBBS Module
        ///
        ///     Each Module gets its own copy of the Exported Modules, this module keeps track
        ///     of them using a Dictionary and will create them as needed.
        /// </summary>
        /// <param name="module"></param>
        /// <param name="exportedModule"></param>
        /// <returns></returns>
        private IExportedModule GetFunctions(MbbsModule module, string exportedModule)
        {
            var key = $"{module.ModuleIdentifier}-{exportedModule}";

            if (!_exportedFunctions.TryGetValue(key, out var functions))
            {
                _exportedFunctions[key] = exportedModule switch
                {
                    "MAJORBBS" => new Majorbbs(Clock, Logger, _configuration, _fileUtility, _globalCache, module, _channelDictionary, _accountKeyRepository, _accountRepository, _textVariableService),
                    "GALGSBL" => new Galgsbl(Clock, Logger, _configuration, _fileUtility, _globalCache, module, _channelDictionary, _textVariableService),
                    "DOSCALLS" => new Doscalls(Clock, Logger, _configuration, _fileUtility, _globalCache, module, _channelDictionary, _textVariableService),
                    "GALME" => new Galme(Clock, Logger, _configuration, _fileUtility, _globalCache, module, _channelDictionary, _textVariableService),
                    "PHAPI" => new Phapi(Clock, Logger, _configuration, _fileUtility, _globalCache, module, _channelDictionary, _textVariableService),
                    "GALMSG" => new Galmsg(Clock, Logger, _configuration, _fileUtility, _globalCache, module, _channelDictionary, _textVariableService),
                    _ => throw new Exception($"Unknown Exported Library: {exportedModule}")
                };

                functions = _exportedFunctions[key];
            }

            return functions;
        }

        /// <summary>
        ///     Returns the current list of active User Sessions
        /// </summary>
        /// <returns></returns>
        public IList<SessionBase> GetUserSessions() => _channelDictionary.Values.ToList();

        /// <summary>
        ///     Patches Relocation information from each Code Segment Relocation Records into the Segment Byte Code
        ///
        ///     Because the compiler doesn't know the location in memory of the hosts Exported Modules (Imported when
        ///     viewed from the standpoint of the DLL), it saves the information to the Relocation Records for the
        ///     given Code Segment.
        ///
        ///     The x86 Emulator knows that any CALL FAR to a Segment >= 0xFF00 is an emulated Exported Module and properly
        ///     handles calling the correct Module using the Segment of the target, and the Ordinal of the call using the Offset.
        ///     A relocation record for a call to MAJORBBS->ATOL() would be patched as:
        ///
        ///     CALL FAR 0xFFFF:0x004D
        ///
        ///     Segment & Offset meaning:
        ///     0xFFFF == MAJORBBS
        ///     0x004D == 77, Ordinal for ATOL()
        /// </summary>
        /// <param name="module"></param>
        private void PatchRelocation(MbbsModule module)
        {

            foreach (var dll in module.ModuleDlls)
            {
                //Patch Segment 0 (PHAPI) to just RETF (0xCB)
                dll.File.SegmentTable[0].Data[0] = 0xCB;

                foreach (var s in dll.File.SegmentTable)
                {
                    if (s.RelocationRecords == null || s.RelocationRecords.Count == 0)
                        continue;

                    foreach (var relocationRecord in s.RelocationRecords.Values)
                    {
                        //Ignored Relocation Record
                        if (relocationRecord.TargetTypeValueTuple == null)
                            continue;

                        switch (relocationRecord.TargetTypeValueTuple.Item1)
                        {
                            case EnumRecordsFlag.ImportOrdinalAdditive:
                            case EnumRecordsFlag.ImportOrdinal:
                                {
                                    var nametableOrdinal = relocationRecord.TargetTypeValueTuple.Item2;
                                    var functionOrdinal = relocationRecord.TargetTypeValueTuple.Item3;

                                    var relocationPointer = FarPtr.Empty;
                                    switch (dll.File.ImportedNameTable[nametableOrdinal].Name)
                                    {
                                        case "MAJORBBS":
                                            relocationPointer = new FarPtr(module.ExportedModuleDictionary[Majorbbs.Segment].Invoke(functionOrdinal, true));
                                            break;
                                        case "GALGSBL":
                                            relocationPointer = new FarPtr(module.ExportedModuleDictionary[Galgsbl.Segment].Invoke(functionOrdinal, true));
                                            break;
                                        case "DOSCALLS":
                                            relocationPointer = new FarPtr(module.ExportedModuleDictionary[Doscalls.Segment].Invoke(functionOrdinal, true));
                                            break;
                                        case "GALME":
                                            relocationPointer = new FarPtr(module.ExportedModuleDictionary[Galme.Segment].Invoke(functionOrdinal, true));
                                            break;
                                        case "PHAPI":
                                            relocationPointer = new FarPtr(module.ExportedModuleDictionary[Phapi.Segment].Invoke(functionOrdinal, true));
                                            break;
                                        case "GALMSG":
                                            relocationPointer = new FarPtr(module.ExportedModuleDictionary[Galmsg.Segment].Invoke(functionOrdinal, true));
                                            break;
                                        case var importedName
                                            when module.ModuleDlls.Any(m =>
                                                m.File.FileName.Split('.')[0].ToUpper() == importedName):
                                            {
                                                //Find the Imported DLL in the List of Required
                                                var importedDll = module.ModuleDlls.First(m =>
                                                    m.File.FileName.Split('.')[0].ToUpper() == importedName);

                                                //Get The Entry Point based on the Ordinal
                                                var initEntryPoint =
                                                    importedDll.File.EntryTable.First(x => x.Ordinal == functionOrdinal);
                                                relocationPointer = new FarPtr((ushort)(initEntryPoint.SegmentNumber + importedDll.SegmentOffset),
                                                    initEntryPoint.Offset);
                                                break;
                                            }
                                        default:
                                            Logger.Error($"({module.ModuleIdentifier}) Unknown or Unimplemented Imported Library: {dll.File.ImportedNameTable[nametableOrdinal].Name}");
                                            continue;
                                    }

                                    //32-Bit Pointer
                                    if (relocationRecord.SourceType == 3)
                                    {
                                        Array.Copy(relocationPointer.Data, 0, s.Data, relocationRecord.Offset, 4);
                                        continue;
                                    }

                                    //16-Bit Values
                                    var result = relocationRecord.SourceType switch
                                    {
                                        //Offset
                                        2 => relocationPointer.Segment,
                                        5 => relocationPointer.Offset,
                                        _ => throw new ArgumentOutOfRangeException(
                                            $"Unhandled Relocation Source Type: {relocationRecord.SourceType}")
                                    };

                                    if (relocationRecord.Flag.HasFlag(EnumRecordsFlag.ImportOrdinalAdditive))
                                        result += BitConverter.ToUInt16(s.Data, relocationRecord.Offset);

                                    Array.Copy(BitConverter.GetBytes(result), 0, s.Data, relocationRecord.Offset, 2);
                                    break;
                                }
                            case EnumRecordsFlag.InternalRef when relocationRecord.SourceType == 3:
                                {
                                    var relocationPointer = new FarPtr(
                                        (ushort)(relocationRecord.TargetTypeValueTuple.Item2 + dll.SegmentOffset),
                                        relocationRecord.TargetTypeValueTuple.Item4);

                                    Array.Copy(relocationPointer.Data, 0, s.Data, relocationRecord.Offset, 4);
                                    break;
                                }
                            case EnumRecordsFlag.InternalRef:
                                {
                                    Array.Copy(
                                        BitConverter.GetBytes(relocationRecord.TargetTypeValueTuple.Item2 +
                                                              dll.SegmentOffset), 0,
                                        s.Data, relocationRecord.Offset, 2);
                                    break;
                                }
                            case EnumRecordsFlag.ImportNameAdditive:
                            case EnumRecordsFlag.ImportName:
                                {
                                    var nametableOrdinal = relocationRecord.TargetTypeValueTuple.Item2;
                                    var functionOrdinal = relocationRecord.TargetTypeValueTuple.Item3;

                                    var newSegment = dll.File.ImportedNameTable[nametableOrdinal].Name switch
                                    {
                                        "MAJORBBS" => Majorbbs.Segment,
                                        "GALGSBL" => Galgsbl.Segment,
                                        "PHAPI" => Phapi.Segment,
                                        "GALME" => Galme.Segment,
                                        "DOSCALLS" => Doscalls.Segment,
                                        _ => throw new Exception(
                                            $"Unknown or Unimplemented Imported Module: {dll.File.ImportedNameTable[nametableOrdinal].Name}")

                                    };

                                    var relocationPointer = new FarPtr(newSegment, functionOrdinal);

                                    //32-Bit Pointer
                                    if (relocationRecord.SourceType == 3)
                                    {
                                        Array.Copy(relocationPointer.Data, 0, s.Data, relocationRecord.Offset, 4);
                                        continue;
                                    }

                                    //16-Bit Values
                                    var result = relocationRecord.SourceType switch
                                    {
                                        //Offset
                                        2 => relocationPointer.Segment,
                                        5 => relocationPointer.Offset,
                                        _ => throw new ArgumentOutOfRangeException(
                                            $"Unhandled Relocation Source Type: {relocationRecord.SourceType}")
                                    };

                                    if (relocationRecord.Flag.HasFlag(EnumRecordsFlag.ImportNameAdditive))
                                        result += BitConverter.ToUInt16(s.Data, relocationRecord.Offset);

                                    Array.Copy(BitConverter.GetBytes(result), 0, s.Data, relocationRecord.Offset, 2);
                                    break;

                                }
                            default:
                                throw new Exception("Unsupported Records Flag for Relocation Value");
                        }
                    }
                }
            }
        }

        /// <summary>
        ///     Marks the specified module as "Enabled"
        /// </summary>
        /// <param name="moduleId"></param>
        private void EnableModule(string moduleId)
        {
            _modules[moduleId].ModuleConfig.ModuleEnabled = true;
        }

        /// <summary>
        ///     Disables a Module while the service host is running
        /// </summary>
        /// <param name="moduleId"></param>
        /// <param name="isCrashed"></param>
        private void DisableModule(string moduleId, bool isCrashed = false)
        {
            //Ensure Module is marked Disabled
            _modules[moduleId].ModuleConfig.ModuleEnabled = false;

            //Log Crashed or Disabled
            if (isCrashed)
            {
                Logger.Error($"Module {moduleId} has crashed. Disabling.");
            }
            else
            {
                Logger.Info($"Module {moduleId} has been disabled by /SYSOP command.");
            }

            //Notify Users and Exit Modules
            foreach (var c in _channelDictionary.Values.Where(x => x.CurrentModule?.ModuleIdentifier == moduleId))
            {
                if (isCrashed)
                {
                    c.SendToClient($"|RESET|\r\n|B||RED|The module you were in ({moduleId}) has crashed. Please contact the Sysop and try again later.|RESET|\r\n".EncodeToANSIArray());
                }
                else
                {
                    c.SendToClient($"|RESET|\r\n|B||RED|The module you were in ({moduleId}) has been disabled by the Sysop. Please try again later.|RESET|\r\n".EncodeToANSIArray());
                }

                ExitModule(c);
            }
        }

        /// <summary>
        ///     Returns a new Timer that counts down to the Cleanup Warning prior to the cleanup routine running
        /// </summary>
        /// <returns></returns>
        private Timer SetupCleanupWarningTimer()
        {
            _cleanupWarningMinutesRemaining = CleanupWarningInitialMinutes;

            var initialWarningTime = _cleanupTime + _cleanupGracePeriod - TimeSpan.FromMinutes(CleanupWarningInitialMinutes);
            var dueTime = NowUntil(initialWarningTime);
            var period = TimeSpan.FromMinutes(1);

            return new Timer(SendCleanupWarning, null, (int) dueTime.TotalMilliseconds, (int) period.TotalMilliseconds);
        }

        /// <summary>
        ///     Goes through all the currently active sessions and sends them a warning that the Nightly Cleanup is about to run
        /// </summary>
        /// <param name="_"></param>
        private void SendCleanupWarning(object _)
        {
            if (_cleanupWarningMinutesRemaining > 0)
            {
                Logger.Debug($"in SendCleanupWarning, _cleanupWarningMinutesRemaining = {_cleanupWarningMinutesRemaining}");

                var minuteText = (_cleanupWarningMinutesRemaining > 1) ? "minutes" : "minute";

                foreach (var channel in _channelDictionary.Select(c => c.Value.Channel))
                {
                    Logger.Debug($"Sending cleanup warning to channel {channel}: {_cleanupWarningMinutesRemaining} {minuteText} until shutdown.");
                    _channelDictionary[channel].SendToClient($"|RESET|\r\n|B||MAGENTA|Sorry to interrupt here, but the server will be shutting down in {_cleanupWarningMinutesRemaining} {minuteText} for the nightly \"auto-cleanup\" process. Please finish up and log off... thank you!|RESET|\r\n".EncodeToANSIArray());
                }
                _cleanupWarningMinutesRemaining--;
            }
            else
            {
                _cleanupWarningTimer.Dispose();
                _cleanupWarningTimer = null;
            }
        }

        /// <summary>
        ///     Method Invoked by the Nightly Cleanup time to begin the Nightly Cleanup Process
        /// </summary>
        private void ProcessNightlyCleanup()
        {
            if (_performCleanup)
            {
                Logger.Info($"Beginning nightly cleanup process.");
                _performCleanup = false;
                DoNightlyCleanup();

                // signal that cleanup has completed
                _cleanupRestartEvent?.Set();
                _cleanupRestartEvent = null;

                _cleanupWarningTimer = SetupCleanupWarningTimer();
                Logger.Info($"Nightly cleanup complete.");
            }
        }

        /// <summary>
        ///     Performs the Nightly Cleanup by invoking "MCUROU" (Nightly Cleanup) and "FINROU" (Finish-Up) routines in each module
        /// </summary>
        private void DoNightlyCleanup()
        {
            Logger.Info("PERFORMING NIGHTLY CLEANUP");

            // Notify Users of Nightly Cleanup
            foreach (var c in _channelDictionary)
                _channelDictionary[c.Value.Channel].SendToClient($"|RESET|\r\n|B||RED|Nightly Cleanup Running -- Please log back on shortly|RESET|\r\n".EncodeToANSIArray());

            // removes all sessions and stops worker thread
            RemoveSessions(session => true);

            CallModuleRoutine("mcurou", module => Logger.Info($"Calling nightly cleanup routine on module {module.ModuleIdentifier}"));
            CallModuleRoutine("finrou", module => Logger.Info($"Calling finish-up (sys-shutdown) routine on module {module.ModuleIdentifier}"));

            //Save current module config
            var moduleConfigurations = (from m in _modules select m.Value.ModuleConfig).ToList();

            foreach (var m in _modules)
            {
                var modulePath = m.Value.ModulePath;

                m.Value.Dispose();
                _modules.Remove(m.Value.ModuleIdentifier);
                var exportedFunctionsToRemove = _exportedFunctions.Keys.Where(x => x.StartsWith(m.Value.ModuleIdentifier)).ToList();

                foreach (var e in exportedFunctionsToRemove)
                {
                    _exportedFunctions[e].Dispose();
                    _exportedFunctions.Remove(e);
                }

                foreach (var cleanup in m.Value.Mdf.Cleanup)
                    RunProgram(modulePath, cleanup);
            }

            Logger.Info("NIGHTLY CLEANUP COMPLETE -- RESTARTING HOST");

            Start(moduleConfigurations);
        }

        /// <summary>
        ///     Returns a TimeSpan representing the time between now and the specified time.
        /// </summary>
        /// <param name="timeOfDay">24-hour timespan representing a time of day, and determining the time between now and the time specified</param>
        /// <returns></returns>
        private TimeSpan NowUntil(TimeSpan timeOfDay)
        {
            var waitTime = timeOfDay - Clock.Now.TimeOfDay;
            if (waitTime < TimeSpan.Zero)
            {
                waitTime += TimeSpan.FromDays(1);
            }

            return waitTime;
        }

        /// <summary>
        ///     Returns an API Report for all currently loaded modules
        ///
        ///     The API Report contains all SDK APIs that are used by the module
        /// </summary>
        public void GenerateAPIReport()
        {
            foreach (var apiReport in _modules.Select(m => new ApiReport(Logger, m.Value)))
            {
                apiReport.GenerateReport();
            }
        }
    }
}
