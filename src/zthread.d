/*
 * CLISP thread functions - multiprocessing
 * Distributed under the GNU GPL as a part of GNU CLISP
 * Sam Steingold 2003-2008
 */

#include "lispbibl.c"

#ifdef MULTITHREAD

/* operations on a lisp stack that is not the current one (NC) 
   - ie. belongs to other not yet started threads */
#ifdef STACK_DOWN
  #define NC_STACK_(non_current_stack,n)  (non_current_stack[(sintP)(n)])
#endif
#ifdef STACK_UP
  #define NC_STACK_(non_current_stack,n)  (non_current_stack[-1-(sintP)(n)])
#endif
#define NC_pushSTACK(non_current_stack,obj)  \
  (NC_STACK_(non_current_stack,-1) = (obj), non_current_stack skipSTACKop -1)


/* releases the clisp_thread_t memory of the list of Thread records */
global void release_threads (object list) {
  while (!endp(list)) {
    /* may be the stack as well ??? currently freed in delete_thread(). */
    free(TheThread(Car(list))->xth_globals);
    list = Cdr(list);
  }
}

/* disable async signals (SIGINT,SIGALRM,SIGTERM,SIGWINCH)
   on UNIX forthe current  thread. All these signals should be handled
   ony in main thread.
   On Win32 - anyway all signals are handled in the main thread */
local void disable_thread_async_signals()
{
 #if (defined(HAVE_SIGNALS) && defined(UNIX))
  var sigset_t sigblock_mask;
  sigemptyset(&sigblock_mask);
  sigaddset(&sigblock_mask,SIGINT);
  sigaddset(&sigblock_mask,SIGALRM);    
  sigaddset(&sigblock_mask,SIGTERM);
#if defined(SIGWINCH) && !defined(NO_ASYNC_INTERRUPTS)
  sigaddset(&sigblock_mask,SIGWINCH);;    
#endif
  /* we can use the pthread_sigmask() as well for pthreads 
     but this seems better - since it's the same if we have
     POSIX_THREADS and SOLARIS_THREADS. Waht about others ??? */
  sigprocmask(SIG_BLOCK,&sigblock_mask,NULL);
 #endif
}

/* VTZ: All newly created threads start here.*/
local /*maygc*/ void *thread_stub(void *arg)
{
  #if USE_CUSTOM_TLS == 2
  tse __tse_entry;
  tse *__thread_tse_entry=&__tse_entry;
  #endif
  clisp_thread_t *me=(clisp_thread_t *)arg;
  disable_thread_async_signals();
  set_current_thread(me);
  me->_SP_anchor=(void*)SP();

  funcall(STACK_0,0); /* call it */
  /*VTZ: may be store the return value in the thread record ??*/
  delete_thread(me,false);
  return NULL;
}

LISPFUN(make_thread,seclass_default,1,0,norest,key,1,(kw(name)))
{ /* (MAKE-THREAD function &key name) */
  /* VTZ: new thread lisp stack size is the same as the calling one 
   may be add another keyword argument for it ???*/
  var uintM lisp_stack_size=(STACK_item_count(STACK_bound,STACK_start)+0x40)*
                            sizeof(gcv_object_t *);
  var clisp_thread_t *new_thread;
  /* do allocations before thread locking */ 
  pushSTACK(allocate_thread(&STACK_0)); /* put it in GC visible place */
  pushSTACK(allocate_cons());
  /* create clsp_thread_t - no need for locking */
  new_thread=create_thread(lisp_stack_size);
  if (!new_thread) {
    skipSTACK(4); VALUES1(NIL); return;
  }
  /* let's lock in order to register */
  begin_blocking_system_call(); /* give chance the GC to work while we wait*/
  lock_threads(); 
  end_blocking_system_call();
  /* prepare the new thread stack */
  /* push 2 nullobj */
  NC_pushSTACK(new_thread->_STACK,nullobj); 
  NC_pushSTACK(new_thread->_STACK,nullobj);
  /* push the function to be executed */ 
  NC_pushSTACK(new_thread->_STACK,STACK_3);
  new_thread->_aktenv=aktenv; /* set it the same as current thread one */
  new_thread->_pinned = NIL;
  /* VTZ:TODO we have to  copy the symvalues as well. */
  if (register_thread(new_thread)<0) {
    /* total failure */
    unlock_threads();
    delete_thread(new_thread,true);
    VALUES1(NIL);
    skipSTACK(4); 
    return;
  }
  var object new_cons=popSTACK();
  var object lthr=popSTACK();
  skipSTACK(2);
  /* initialize the thread references */
  new_thread->_lthread=lthr;
  TheThread(lthr)->xth_globals=new_thread;
  /* add to all_threads global */
  Car(new_cons) = lthr;
  Cdr(new_cons) = O(all_threads);
  O(all_threads) = new_cons;
  unlock_threads(); /* allow GC and other thread creation. */
  /* create the OS thread */
  xthread_create(&TheThread(lthr)->xth_system, &thread_stub,new_thread);
  VALUES1(lthr);
}

struct call_timeout_data_t {
  xmutex_t mutex;
  xcondition_t cond;
  clisp_thread_t *caller;
};

/* the thread the executes the call-with-timeout body function*/
local maygc void *exec_timeout_call (void *arg)
{
  #if USE_CUSTOM_TLS == 2
  tse __tse_entry;
  tse *__thread_tse_entry=&__tse_entry;
  #endif
  var struct call_timeout_data_t *pcd = (struct call_timeout_data_t*)arg;
  disable_thread_async_signals();
  /* simply reuse the calling thread stack. 
   the calling thread does not have a lot of job to do until we work so it seems safe. */
  set_current_thread(pcd->caller);  
  begin_system_call();
  xmutex_lock(&pcd->mutex); /* wait for the main thread to start waiting */
  xmutex_unlock(&pcd->mutex); /* allow the main thread to timeout */
  end_system_call();
  /*VTZ:TODO The back_trace resides on the caller thread C stack - there maybe problems here*/  
  SP_anchor=(void*)SP(); /* hmm. The back_trace resides on*/
  funcall(STACK_0,0); /* run the function */
  /* now we have to restore our original stack (that OS has provided to us) */
  begin_system_call();
  xcondition_broadcast(&pcd->cond);
  end_system_call();
  return NULL;
}

/* VTZ: a new OS thread will be created that will reuse the clisp_thread_t structure of the calling one.
 no lisp record for this thread will be created. it works on the behalf of the calling one. */
LISPFUNN(call_with_timeout,3)
{ /* (CALL-WITH-TIMEOUT timeout timeout-function body-function)
 the reason we go with C instead of Lisp is that we save on creating a
 separate STACK for the body thread (i.e., the waiting thread and the
 body thread run in the same "stack group").
 the return values come either from body-function or from timeout-function */
  var struct timeval tv;
  var struct timeval *tvp = sec_usec(STACK_2,unbound,&tv);
  if (tvp) {
    /* we will backup our current thread here and restore it in case of cancellation */
    /* VTZ:TODO also symvalues should be backed up !!!*/
    clisp_thread_t restore_after_cancel; 
    var xthread_t xth;
    var struct call_timeout_data_t cd;
    var struct timeval now;
    var struct timespec timeout;
    var int retval=0;
    memcpy(&restore_after_cancel,current_thread(),thread_size(0)); /* everything without symvalues */
    cd.caller=current_thread();
    begin_system_call();
    xcondition_init(&cd.cond); xmutex_init(&cd.mutex);
    xmutex_lock(&cd.mutex);
    end_system_call();
    xthread_create(&xth,&exec_timeout_call,(void*)&cd);
    gettimeofday(&now,NULL);
    timeout.tv_sec = now.tv_sec + tv.tv_sec;
    timeout.tv_nsec = 1000*(now.tv_usec + tv.tv_usec);
    retval = xcondition_timedwait(&cd.cond,&cd.mutex,&timeout);
    if (retval == ETIMEDOUT) {
      xthread_wait(xth); /*VTZ: currently we do not have safe way to cancel thread (esp. GC)*/ 
      memcpy(current_thread(),&restore_after_cancel,thread_size(0));
      funcall(STACK_1,0); /* run timeout-function */
    }
    begin_system_call();
    xcondition_destroy(&cd.cond);
    xmutex_destroy(&cd.mutex);
    end_system_call();
  } else
    funcall(STACK_1,0);
  skipSTACK(3);
}

LISPFUN(thread_wait,seclass_default,3,0,rest,nokey,0,NIL)
{ /* (THREAD-WAIT whostate timeout predicate &rest arguments)
   predicate may be a LOCK structure in which case we wait for its release
   timeout maybe NIL in which case we wait forever */
  /* set whostate! */
  NOTREACHED;
}

LISPFUNN(thread_yield,0)
{ /* (THREAD-YIELD) */
  begin_blocking_system_call();
  xthread_yield();
  end_blocking_system_call();
  VALUES1(current_thread()->_lthread);
}

LISPFUNN(thread_kill,1)
{ /* (THREAD-KILL thread) */
  NOTREACHED;
}

LISPFUN(thread_interrupt,seclass_default,2,0,rest,nokey,0,NIL)
{ /* (THREAD-INTERRUPT thread function &rest arguments) */
  NOTREACHED;
}

LISPFUNN(thread_restart,1)
{ /* (THREAD-RESTART thread) */
  NOTREACHED;
}

LISPFUNN(threadp,1)
{ /* (THREADP object) */
  NOTREACHED;
}

LISPFUNN(thread_name,1)
{ /* (THREAD-NAME thread) */
  NOTREACHED;
}

LISPFUNN(thread_active_p,1)
{ /* (THREAD-ACTIVE-P thread) */
  NOTREACHED;
}

LISPFUNN(thread_state,1)
{ /* (THREAD-STATE thread) */
  NOTREACHED;
}

LISPFUNN(thread_whostate,1)
{ /* (THREAD-WHOSTATE thread) */
  NOTREACHED;
}

LISPFUNN(current_thread,0)
{ /* (CURRENT-THREAD) */
  VALUES1(current_thread()->_lthread);
}

LISPFUNN(list_threads,0)
{ /* (LIST-THREADS) */
  /* we cannot copy the all_threads list, since it maygc 
     and while we hold the threads lock - deadlock will occur. */
  var uintC count=0;
  begin_blocking_system_call();
  lock_threads(); /* stop GC and thread creation*/
  end_blocking_system_call();
  var object list=O(all_threads);
  while (!endp(list)) {
    count++;
    pushSTACK(Car(list));
    list=Cdr(list);
  }
  begin_system_call();
  unlock_threads();
  end_system_call();
  /*
  VALUES1(listof(count));
  */

  var object vec=allocate_bit_vector(Atype_8Bit,20);
  current_thread()->_pinned=vec;
  VALUES2(listof(count),current_thread()->_pinned);

}

#endif  /* MULTITHREAD */
