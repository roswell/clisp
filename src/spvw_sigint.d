/* Handling of signals SIGINT and SIGALRM. */

/* -------------------------- Specification ---------------------------- */

#ifdef HAVE_SIGNALS
/* Installs the Ctrl-C handler. */
local void install_sigint_handler (void);
#endif
#ifdef WIN32_NATIVE
/* Installs the Ctrl-C handler. */
extern void install_sigint_handler (void);
#endif

/* -------------------------- Implementation --------------------------- */


#if defined(PENDING_INTERRUPTS) && !defined(MULTITHREAD)
/* Flag, if an interrupt is pending. */
global uintB interrupt_pending = false;
#endif

#ifdef HAVE_SIGNALS

/* this must be done by signal handler before entering lisp.
 also used in spvw_sigterm.d */
local void signal_handler_prepare_for_lisp (int sig) {
  /* wait, until break is allowed: */
  if (!break_sems_cleared())
    return;
  /* we jump now out of the signal-handler, neither with 'return'
   nor with 'longjmp'.

   Hans-J. Boehm <boehm@parc.xerox.com> points out that this might
   cause problems, if the signal has interrupted a running malloc() or
   free() and the malloc()-library is not reentrant.
   remedy: instead of malloc() always use xmalloc() , that sets a break-
   semaphore? But how about malloc()-calls, that are issued by routines
   like opendir(), getpwnam(), tgetent(), ... ? Should we define malloc()
   on our own and hope that it is called by all library-
   functions (statically linked or via DLL)?? */

 #if defined(SIGNALBLOCK_POSIX) && ((defined(USE_SIGACTION) ? defined(SIGACTION_NEED_UNBLOCK) : defined(SIGNAL_NEED_UNBLOCK)) || defined(GNU_READLINE))
  { /* either if handlers, installed with [SIGNAL_NEED_UNBLOCK] and signal(),
   are called with blocked signal anyway - usually on
   BSD-systems -, or if other unsecure components [GNU_READLINE] can cause
   the blocking of the signal on call via sigaction() or similar,
   we must unblock the right now blocked signal: */
    var sigset_t sigblock_mask;
    sigemptyset(&sigblock_mask); sigaddset(&sigblock_mask,sig);
    sigprocmask(SIG_UNBLOCK,&sigblock_mask,NULL);
  }
 #endif
 #ifdef HAVE_SAVED_STACK
  /* set STACK to a meaningful value: */
  if (saved_STACK != NULL) { setSTACK(STACK = saved_STACK); }
 #endif
}

/* React on signal SIGINT: Leave the signal handler and enter a break driver
 loop. If this function returns, this means the signal handler should try
 again later. */
local void react_on_sigint (int sig) { /* sig = SIGINT or SIGALRM */
 #ifndef NO_ASYNC_INTERRUPTS
  signal_handler_prepare_for_lisp(sig);
#if defined(MULTITHREAD)
  /* NB: we are in the main thread - always
     it is possible to be in interrupted in blocking system call. So - 
     the GC to be enabled as SAFE for the main thread. We have to check 
     for this case and be sure to disable it before jumping to the 
     error handler.
  */
  ASSERT(main_threadp()); /* main thread - ASSERT not safe here - but 
			   equally bad is not to ASSERT */
  /* TODO: may be just get the allthreads[0] here, since current_thread()
     may expand to something unwanted in signal handler ???*/
  var clisp_thread_t *thr=current_thread(); 
  if (!spinlock_tryacquire(&thr->_gc_suspend_ack)) {
    /* hmmm - there is GC in progress or simply there was 
     no GC since the beginning of the system call (if there was 
     one at all) - and main thread already holds the lock. 
     Te best thing we can do is to lock on suspend mutex, try 
     acquire the ack and unlock the suspend mutex.
    */
    /* wait for GC to finish (if it is running now - otherwise 
     no problems at all to lock) 
     NB: we can safely call mutex locking without thinking of 
     deadlock - since if we cannot acquire ack - than we can not 
     also hold the mutex lock (see spvw_global.d:gc_resume_all_threads(),
     lispbibl.d:GC_SAFE_REGION_END().
    */
    xmutex_lock(&thr->_gc_suspend_lock); 
    /* try to acquire ack - if we succeed - great - there was really GC in 
     progress. If not - simply there was no GC since possibly blocking call that
     has been interrupted -  so we already hold the ack (and have never lost 
     control over it). */
    spinlock_tryacquire(&thr->_gc_suspend_ack);
    /* unlock the suspend mutex */
    xmutex_unlock(&thr->_gc_suspend_lock);
  }
#endif
  /* jump into a break-loop via 'error': */
  error(interrupt_condition,GETTEXT("Ctrl-C: User break"));
 #endif  /* NO_ASYNC_INTERRUPTS */
}

/* a keyboard-interrupt (signal SIGINT, created by Ctrl-C)
 is suspended for a second. During this period of time it can be handled
 via 'interruptp' in a continuable manner. After expiry,
 the program is interrupted un-continuably.
 Signal-Handler for signal SIGINT: */
#ifdef PENDING_INTERRUPTS
local void interrupt_handler (int sig) { /* sig = SIGINT */
  inc_break_sem_5();
  signal_acknowledge(SIGINT,&interrupt_handler);
  if (!interrupt_pending) { /* is an interrupt pending -> nothing to do */
    interrupt_pending = true;   /* set flag for 'interruptp' */
   #ifdef HAVE_UALARM
    /* wait half a second, then try every 1/20 sec */
    ualarm(ticks_per_second/2,ticks_per_second/20);
   #else
    alarm(1);          /* wait a second, continues with alarm_handler */
   #endif
  }
  dec_break_sem_5();
}
local void alarm_handler (int sig) { /* sig = SIGALRM */
  /* the time is now up. */
  inc_break_sem_5();
  signal_acknowledge(SIGALRM,&alarm_handler);
  dec_break_sem_5();
  react_on_sigint(sig);
 #ifndef HAVE_UALARM
  alarm(1);                     /* let's try in another second */
 #endif
  return;         /* after a short time a SIGALRM is triggered again. */
}
#define install_sigint_handler()    do {        \
  SIGNAL(SIGINT,&interrupt_handler);            \
  SIGNAL(SIGALRM,&alarm_handler);               \
 } while (0)
#else                                    /* PENDING_INTERRUPTS */
local void interrupt_handler (int sig) { /* sig = SIGINT */
  inc_break_sem_5();
  signal_acknowledge(SIGINT,&interrupt_handler);
  dec_break_sem_5();
  react_on_sigint(sig);
  return;                       /* the user must try it again. */
}
#define install_sigint_handler()  \
    SIGNAL(SIGINT,&interrupt_handler)
#endif  /* PENDING_INTERRUPTS */

#endif  /* HAVE_SIGNALS */

#ifdef WIN32_NATIVE

/* This is the Ctrl-C handler. It is executed in the main thread and must
 not return! */
global void interrupt_handler (void) {
  /* printf("Entering interrupt handler.\n"); */
 #ifdef HAVE_SAVED_STACK
  /* set STACK to a meaningful value: */
  if (saved_STACK != NULL) { setSTACK(STACK = saved_STACK); }
 #endif
  /* jump into a break-loop via 'error': */
  error(interrupt_condition,GETTEXT("Ctrl-C: User break"));
}

/* install_sigint_handler() is defined in win32aux.d. */

#endif  /* WIN32_NATIVE */
