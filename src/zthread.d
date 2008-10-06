/*
 * CLISP thread functions - multiprocessing
 * Distributed under the GNU GPL as a part of GNU CLISP
 * Sam Steingold 2003-2008
 */

#include "lispbibl.c"

#ifdef MULTITHREAD

/* signals an error of obj is not thread. returns the thread*/
local maygc object check_thread(object obj)
{
  while (!threadp(obj)) {
    pushSTACK(NIL); /* no PLACE */
    pushSTACK(obj);       /* TYPE-ERROR slot DATUM */
    pushSTACK(S(thread)); /* TYPE-ERROR slot EXPECTED-TYPE */
    pushSTACK(obj); pushSTACK(subr_self);
    check_value(type_error,GETTEXT("~S: ~S is not a thread"));
    /*NB:  since the reader cannot read thread objects - let's eval 
     what the user has entered. It does not look nice - TBD. 
     may be allow just symbols and take their value or look for thread
     name ???
    */
    eval(value1);
    obj=value1;
  } 
  return obj;
}

/* releases the clisp_thread_t memory of the list of Thread records */
global void release_threads (object list) {
  while (!endp(list)) {
    clisp_thread_t *thread = TheThread(Car(list))->xth_globals;
    free(thread->_ptr_symvalues);
    free(thread);
    list = Cdr(list);
  }
}

/* VTZ: All newly created threads start here.*/
local /*maygc*/ void *thread_stub(void *arg)
{
  #if USE_CUSTOM_TLS == 2
  tse __tse_entry;
  tse *__thread_tse_entry=&__tse_entry;
  #endif
  clisp_thread_t *me=(clisp_thread_t *)arg;
  var struct backtrace_t bt;
  set_current_thread(me);
  me->_SP_anchor=(void*)SP();
  /* initialize backtrace */
  bt.bt_next = NULL;
  bt.bt_function = L(make_thread); /* not exactly */
  bt.bt_stack = STACK STACKop -1;
  bt.bt_num_arg = -1;
  back_trace = &bt;
  /* establish driver frame so on thread exit by 
   thread-kill we can unwind the stack properly by reset(0); */
  var gcv_object_t *initial_bindings = &STACK_0;
  var gcv_object_t *funptr = &STACK_1;
  /* make "top" driver frame */
  var gcv_object_t* top_of_frame = STACK; /* pointer above frame */
  var sp_jmp_buf returner; /* remember entry point */
  /* driver frame in order to be able to kill the thread and unwind the stack 
     via reset(0) call. */
  finish_entry_frame(DRIVER,returner,,{skipSTACK(2);goto end_of_thread;});
  /* create special vars initial dynamic bindings. 
     we do not create DYNBIND frame since anyway we are at the 
     "top level" of the thread. */
  if (boundp(*initial_bindings) && !endp(*initial_bindings)) {
    while (!endp(*initial_bindings)) {
      var object pair=Car(*initial_bindings);
      if (consp(pair) && symbolp(Car(pair))) {
	/* only if the symbol is special per thread variable */
	if (TheSymbol(Car(pair))->tls_index != SYMBOL_TLS_INDEX_NONE) {
	  eval(Cdr(pair)); /* maygc */
	  pair=Car(*initial_bindings);
	  Symbol_thread_value(Car(pair)) = value1;
	}
      }
      *initial_bindings = Cdr(*initial_bindings);
    }
  }
  /* now execute the function */
  funcall(*funptr,0); /* call fun */
  /* the return value(s) are in the mv_space of the clisp_thread_t */
  reset(0);  /* unwind what we have till now */
  NOTREACHED;
 end_of_thread:
  skipSTACK(2); /* function + init bindings */
  /* the lisp stack should be unwound here. check it and complain. */
  if (!(eq(STACK_0,nullobj) && eq(STACK_1,nullobj))) {
    /* we should always have empty stack - this is an error. */
    NOTREACHED;
  }
  /* just unregister it from the active threads. the allocated memory
     will be released during GC (if there are no references to thread object)*/
  delete_thread(me,false); 
  return NULL;
}

LISPFUN(make_thread,seclass_default,1,0,norest,key,2,(kw(name),kw(initial_bindings)))
{ /* (MAKE-THREAD function &key name (initial-bindings mt:*default-special-bindings*)) */
  /* VTZ: new thread lisp stack size is the same as the calling one 
   may be add another keyword argument for it ???*/
  var uintM lisp_stack_size=(STACK_item_count(STACK_bound,STACK_start)+0x40)*
                            sizeof(gcv_object_t *);
  var clisp_thread_t *new_thread;
  /* check initial bindings */
  if (!boundp(STACK_0)) /* if not bound set to mt:*default-special-bidnings* */
    STACK_0 = Symbol_value(S(default_special_bindings));
  if (boundp(STACK_0)) {
    if (!listp(STACK_0))
      error_list(STACK_0);
  }
  if (!boundp(STACK_1)) {
    /* no thread name supplied - ask for it. */
    STACK_1 = check_string_replacement(STACK_1);
  }
  /* do allocations before thread locking */ 
  pushSTACK(allocate_thread(&STACK_1)); /* put it in GC visible place */
  pushSTACK(allocate_cons());
  /* create clsp_thread_t - no need for locking */
  new_thread=create_thread(lisp_stack_size);
  if (!new_thread) {
    skipSTACK(5); VALUES1(NIL); return;
  }
  /* let's lock in order to register */
  begin_blocking_call(); /* give chance the GC to work while we wait*/
  lock_threads(); 
  end_blocking_call();
  /* push 2 null objects in the thread stack in order to stop
     marking in GC while initializing the thread and stack unwinding
     in case of error. */
  NC_pushSTACK(new_thread->_STACK,nullobj);
  NC_pushSTACK(new_thread->_STACK,nullobj);
  /* push the function to be executed */ 
  NC_pushSTACK(new_thread->_STACK,STACK_4);
  /* push the initial bindings alist */
  NC_pushSTACK(new_thread->_STACK,STACK_2);
  if (register_thread(new_thread)<0) {
    /* total failure */
    unlock_threads();
    delete_thread(new_thread,true);
    VALUES1(NIL);
    skipSTACK(5); 
    return;
  }
  var object new_cons=popSTACK();
  var object lthr=popSTACK();
  skipSTACK(3);
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
/* Currently broken -waiting for signal handling */
LISPFUNN(call_with_timeout,3)
{ /* (CALL-WITH-TIMEOUT timeout timeout-function body-function)
 the reason we go with C instead of Lisp is that we save on creating a
 separate STACK for the body thread (i.e., the waiting thread and the
 body thread run in the same "stack group").
 the return values come either from body-function or from timeout-function */
  NOTREACHED;
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
    memcpy(&restore_after_cancel,current_thread(),sizeof(clisp_thread_t)); /* wrong */
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
      memcpy(current_thread(),&restore_after_cancel,sizeof(clisp_thread_t)); /* wrong !!! */
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
  /* TODO: interrupt with reset(0); */
  NOTREACHED;
}

LISPFUN(thread_interrupt,seclass_default,2,0,rest,nokey,0,NIL)
{ /* (THREAD-INTERRUPT thread function &rest arguments) */
  /* TODO: waiting for MT signal handling */
  NOTREACHED;
  
}

LISPFUNN(thread_restart,1)
{ /* (THREAD-RESTART thread) */
  NOTREACHED;
}

LISPFUNN(threadp,1)
{ /* (THREADP object) */
  var object obj = popSTACK();
  VALUES_IF(threadp(obj));
}

LISPFUNN(thread_name,1)
{ /* (THREAD-NAME thread) */
  var object obj=check_thread(popSTACK());
  VALUES1(TheThread(obj)->xth_name);
}

LISPFUNN(thread_active_p,1)
{ /* (THREAD-ACTIVE-P thread) */
  var object obj=check_thread(popSTACK());
  VALUES_IF(TheThread(obj)->xth_globals->_STACK != 0);
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
  VALUES1(listof(count));
}

/* helper function that returns pointer to the symbol's symvalue 
   in a thread. If the symbol is not bound in the thread - NULL is 
   returned */
local maygc gcv_object_t* thread_symbol_place(gcv_object_t *symbol, 
					      gcv_object_t *thread)
{
  var object sym=check_symbol(*symbol);
  if (eq(*thread,NIL)) {
    /* global value */
    return &TheSymbol(sym)->symvalue;
  } else {
    var clisp_thread_t *thr;
    if (eq(*thread,T)) {
      /* current thread value */
      thr=current_thread();
    } else {
      /* thread object */
      pushSTACK(sym); 
      *thread=check_thread(*thread);
      sym = popSTACK();
      thr=TheThread(*thread)->xth_globals;
    }
    *thread=thr->_lthread; /* for error reporting if needed */
    var uintL idx=TheSymbol(sym)->tls_index;
    if (idx == SYMBOL_TLS_INDEX_NONE ||
	thr->_ptr_symvalues[idx] == SYMVALUE_EMPTY) 
      return NULL; /* not per thread special, or no bidning in thread */
    return &thr->_ptr_symvalues[idx];
  }
}

LISPFUNNR(symbol_value_thread,2)
{ /* (MT:SYMBOL-VALUE-THREAD symbol thread) */
  gcv_object_t *symval=thread_symbol_place(&STACK_1, &STACK_0);
  if (!symval || eq(unbound,*symval)) {
    VALUES2(NIL,NIL); /* not bound */
  } else {
    VALUES2(*symval,T);
  }
  skipSTACK(2);
}

LISPFUNN(set_symbol_value_thread,3)
{ /* (SETF (MT:SYMBOL-VALUE-THREAD symbol thread) value) */
  gcv_object_t *symval=thread_symbol_place(&STACK_2, &STACK_1);
  if (!symval) {
    var object symbol=STACK_2;
    var object thread=STACK_1;
    pushSTACK(symbol); /* CELL-ERROR Slot NAME */
    pushSTACK(thread);
    pushSTACK(symbol); pushSTACK(S(set_symbol_value_thread));
    error(unbound_variable,GETTEXT("~S: variable ~S has no binding in thread ~S"));
  } else {
    *symval=STACK_0;
    VALUES1(*symval);
  }
  skipSTACK(3);
}


#endif  /* MULTITHREAD */
