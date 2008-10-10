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
  /* mark dummy end of stack - only upon request we will reveal ourselves */
  pushSTACK(nullobj); pushSTACK(nullobj); 
  me->_dummy_stack_end = &STACK_0;
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
  skipSTACK(2); /* skip the dummy null objects */
  reset(0);  /* unwind what we have till now */
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
  xthread_exit(0);
  return NULL;
}

local inline ensure_uint32(object x)
{
  return 
    (uint32_p(x) ? I_to_uint32(x) : I_to_uint32(check_uint32_replacement(x)));
}

LISPFUN(make_thread,seclass_default,1,0,norest,key,4,
	(kw(name),kw(initial_bindings),kw(cstack_size),kw(vstack_depth)))
{ /* (MAKE-THREAD function 
                  &key name 
                  (initial-bindings THREADS:*default-special-bindings*)
		  (cstack-size THREADS::*DEFAULT-CONTROL-STACK-SIZE*)
		  (vstack-depth THREADS::*DEFAULT-VALUE-STACK-DEPTH*))
   */
  var clisp_thread_t *new_thread;
  /* init the stack size if not specified */
  if (missingp(STACK_0)) STACK_0 = Symbol_value(S(default_value_stack_depth));
  if (missingp(STACK_1)) STACK_1 = Symbol_value(S(default_control_stack_size));
  /* vstack_size */
  var uintM vstack_depth = ensure_uint32(popSTACK());
  /* cstack_size */
  var uintM cstack_size = ensure_uint32(popSTACK());
  if (!vstack_depth) { /* lisp stack empty ??? */
    /* use the same as the caller */
    vstack_depth=STACK_item_count(STACK_bound,STACK_start); /*skip 2 nullobj*/
  }
  if (cstack_size > 0 && cstack_size < 0x10000) { /* cstack too small ? */
    /*TODO: or may be signal an error */
    /* lets allocate at least 64 K */
    cstack_size = 0x10000;
  }
  if (vstack_depth < ca_limit_1) {
    /* TODO: may be signal an error */
    vstack_depth=ca_limit_1;
  }
  /* check initial bindings */
  if (!boundp(STACK_0)) /* if not bound set to mt:*default-special-bidnings* */
    STACK_0 = Symbol_value(S(default_special_bindings));
  if (!listp(STACK_0))
    error_list(STACK_0);
  /* check thread name */
  if (!stringp(STACK_1)) 
    STACK_1 = check_string_replacement(STACK_1);

  /* do allocations before thread locking */ 
  pushSTACK(allocate_thread(&STACK_1)); /* put it in GC visible place */
  pushSTACK(allocate_cons());
  /* create clsp_thread_t - no need for locking */
  new_thread=create_thread(vstack_depth);
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
  if (xthread_create(&TheThread(lthr)->xth_system, &thread_stub,new_thread,cstack_size)) {
    pushSTACK(lthr);
    delete_thread(new_thread,false); /* remove it from the list */
    lthr=popSTACK();
    /*TODO: signal an error */
    VALUES1(NIL); /* for now jsut return NIL - however the threadobj is here*/
  } else
    VALUES1(lthr);
}

LISPFUNN(call_with_timeout,3)
{ /* (CALL-WITH-TIMEOUT timeout timeout-function body-function)
     It's two expensive to spawn a new OS thread for any call here.
     We are going to do it via hackich signal handling within 
     the current thread. 
     TODO: implement.  */
  NOTREACHED;
}

LISPFUN(thread_wait,seclass_default,3,0,rest,nokey,0,NIL)
{ /* (THREAD-WAIT whostate timeout predicate &rest arguments)
   predicate may be a LOCK structure in which case we wait for its release
   timeout maybe NIL in which case we wait forever */
  /* set whostate! */
  /* Probbaly this will go entirely in LISP when locks are ready. */
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
#ifdef HAVE_SIGNALS 
  var object thr = check_thread(popSTACK());
  var xthread_t systhr=TheThread(thr)->xth_system;
  var clisp_thread_t *clt=TheThread(thr)->xth_globals;
  /* This is the same as THREAD-INTERRUPT with the special case 
     that the dummy stack end is revealed for unwinding.
     It's possible to "reuse" THREAD-INTERRUPT but we will have to 
     stop the world twice (_dummy_stack_end may be accessed
     safely only from the thread itself ot when the world is stopped).
   */
  if (clt == current_thread()) {
    /* we want to kill ourselves :). 
       no need to stop the world for this */
    gcv_object_t *stack_end=clt->_dummy_stack_end;
    *stack_end=NIL;
    stack_end skipSTACKop 1; /* advance */
    *stack_end=NIL; 
    pushSTACK(posfixnum(0));
    funcall(S(unwind_to_driver),1);
    NOTREACHED;
  }
  pushSTACK(thr);
  /* make sure we can send signals to this thread. */
  GC_SAFE_SPINLOCK_ACQUIRE(&clt->_signal_reenter_ok);
  WITH_STOPPED_THREAD
    (clt,true,
     {
       if (clt->_STACK != NULL) { /* only if alive */
	 /* let's reveal the dummy stack end */
	 gcv_object_t *stack_end=clt->_dummy_stack_end;
	 *stack_end=NIL;
	 stack_end skipSTACKop 1; /* advance */
	 *stack_end=NIL; 
	 NC_pushSTACK(clt->_STACK,posfixnum(0));
	 NC_pushSTACK(clt->_STACK,posfixnum(1)); /* one argument */
	 NC_pushSTACK(clt->_STACK,S(unwind_to_driver)); /* function to be called */
	 xthread_signal(TheThread(thr)->xth_system,SIG_THREAD_INTERRUPT);
       } else {
	 /* release it since we are not going to signal the thread */
	 spinlock_release(&clt->_signal_reenter_ok);
       }
     });
  VALUES1(popSTACK());
#else
  NOTREACHED; /*win32 will have to wait*/ 
#endif
}

LISPFUN(thread_interrupt,seclass_default,2,0,rest,nokey,0,NIL)
{ /* (THREAD-INTERRUPT thread function &rest arguments) */
#ifdef HAVE_SIGNALS
  var object thr=check_thread(STACK_(argcount+1));
  var xthread_t systhr=TheThread(thr)->xth_system;
  var clisp_thread_t *clt=TheThread(thr)->xth_globals; 
  if (TheThread(thr)->xth_globals == current_thread()) {
    /* we want to interrupt ourselves ? strange but let's do it */
    funcall(Before(rest_args_pointer),argcount); skipSTACK(2);
  } else {
    var bool thread_was_stopped=false;
    /* we want ot interrupt different thread. */
    STACK_(argcount+1)=thr; /* gc may happen */
    /*TODO: may be check that the function argument can be 
      funcall-ed, since it is not very nice to get errors
      in interrupted thread (but basically this is not a 
      problem)*/
    /* be sure that the signal we send will be received */
    GC_SAFE_SPINLOCK_ACQUIRE(&clt->_signal_reenter_ok);
    WITH_STOPPED_THREAD
      (clt,true,
       {
	 if (clt->_STACK == NULL) { /* thread has terminated */
	   thread_was_stopped=true;
	   spinlock_release(&clt->_signal_reenter_ok);
	 } else {
	   while (rest_args_pointer != args_end_pointer) {
	     var object arg = NEXT(rest_args_pointer);
	     NC_pushSTACK(clt->_STACK,arg);
	   }
	   NC_pushSTACK(clt->_STACK,posfixnum(argcount));
	   NC_pushSTACK(clt->_STACK,STACK_(argcount)); /* function */
	   xthread_signal(systhr,SIG_THREAD_INTERRUPT);
	 }
       });
    skipSTACK(2 + (uintL)argcount);
    /* TODO: may be signal an error if we try to interrupt
       terminated thread ???*/
  }
  VALUES1(clt->_lthread); /* return the thread */
#else
  NOTREACHED; /* win32 not implemented */
#endif
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
  VALUES_IF(TheThread(obj)->xth_globals->_STACK != NULL);
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
	eq(thr->_ptr_symvalues[idx], SYMVALUE_EMPTY))
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
