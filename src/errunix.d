  # Handling of UNIX errors
  # OS_error();
  # > int errno: error code
    nonreturning_function(global, OS_error, (void));
    nonreturning_function(global, OS_file_error, (object pathname));

  # Problem: many different UNIX variants, each with its own set of error
  # messages.
  # Solution: The error names are quite portable. We take the english
  # error message from the system, and provide the translations ourselves.
  # French translations were provided by Tristan <marc@david.saclay.cea.fr>.

  #ifndef HAVE_STRERROR
    # Older systems have sys_nerr and sys_errlist instead of POSIX strerror().
    #if !(defined(UNIX) || defined(EMUNIX)) # avoid conflict with unix.d, msdos.d, <stdlib.h>
      extern int sys_nerr; # Number of OS error messages
      extern char* sys_errlist[]; # Table of OS error messages
    #endif
    local const char* strerror (int errnum);
    local const char* strerror(errnum)
      var int errnum;
      {
        # Attention: There is no guarantee that all system error values are
        # less than sys_nerr. On IRIX 5.2, EDQUOT >= sys_nerr.
        if (errnum >= 0 && errnum < sys_nerr)
          return sys_errlist[errnum];
        else {
          errno = EINVAL;
          return NULL;
        }
      }
  #endif

  #ifdef GNU_GETTEXT
    # Let the caller of get_errormsg() translate the messages.
    #define clgettext
  #endif

  # Returns a system error message.
  # get_errormsg(errcode,&os_error);
    typedef struct { const char* name; const char* msg; } os_error_t;
    local void get_errormsg (uintC errcode, os_error_t* errormsg);
    local void get_errormsg(errcode,errormsg)
      var uintC errcode;
      var os_error_t* errormsg;
      {
        errormsg->name = NULL;
        errormsg->msg = NULL;
        # Special case all the well-known error codes for which we have
        # good English messages and good translations. The if cascade
        # is not the most efficient code, but this function is not time
        # critical.
          # Common UNIX errors:
          #ifdef EPERM
          if (errcode == EPERM) {
            errormsg->name = "EPERM";
            errormsg->msg = GETTEXT("Operation not permitted");
          }
          #endif
          #ifdef ENOENT
          if (errcode == ENOENT) {
            errormsg->name = "ENOENT";
            errormsg->msg = GETTEXT("No such file or directory");
          }
          #endif
          #ifdef ESRCH
          if (errcode == ESRCH) {
            errormsg->name = "ESRCH";
            errormsg->msg = GETTEXT("No such process");
          }
          #endif
          #ifdef EINTR
          if (errcode == EINTR) {
            errormsg->name = "EINTR";
            errormsg->msg = GETTEXT("Interrupted system call");
          }
          #endif
          #ifdef EIO
          if (errcode == EIO) {
            errormsg->name = "EIO";
            errormsg->msg = GETTEXT("I/O error");
          }
          #endif
          #ifdef ENXIO
          if (errcode == ENXIO) {
            errormsg->name = "ENXIO";
            errormsg->msg = GETTEXT("No such device or address");
          }
          #endif
          #ifdef E2BIG
          if (errcode == E2BIG) {
            errormsg->name = "E2BIG";
            errormsg->msg = GETTEXT("Arg list too long");
          }
          #endif
          #ifdef ENOEXEC
          if (errcode == ENOEXEC) {
            errormsg->name = "ENOEXEC";
            errormsg->msg = GETTEXT("Exec format error");
          }
          #endif
          #ifdef EBADF
          if (errcode == EBADF) {
            errormsg->name = "EBADF";
            errormsg->msg = GETTEXT("Bad file number");
          }
          #endif
          #ifdef ECHILD
          if (errcode == ECHILD) {
            errormsg->name = "ECHILD";
            errormsg->msg = GETTEXT("No child processes");
          }
          #endif
          #ifdef EAGAIN
          if (errcode == EAGAIN) {
            errormsg->name = "EAGAIN";
            errormsg->msg = GETTEXT("No more processes");
          }
          #endif
          #ifdef ENOMEM
          if (errcode == ENOMEM) {
            errormsg->name = "ENOMEM";
            errormsg->msg = GETTEXT("Not enough memory");
          }
          #endif
          #ifdef EACCES
          if (errcode == EACCES) {
            errormsg->name = "EACCES";
            errormsg->msg = GETTEXT("Permission denied");
          }
          #endif
          #ifdef EFAULT
          if (errcode == EFAULT) {
            errormsg->name = "EFAULT";
            errormsg->msg = GETTEXT("Bad address");
          }
          #endif
          #ifdef ENOTBLK
          if (errcode == ENOTBLK) {
            errormsg->name = "ENOTBLK";
            errormsg->msg = GETTEXT("Block device required");
          }
          #endif
          #ifdef EBUSY
          if (errcode == EBUSY) {
            errormsg->name = "EBUSY";
            errormsg->msg = GETTEXT("Device busy");
          }
          #endif
          #ifdef EEXIST
          if (errcode == EEXIST) {
            errormsg->name = "EEXIST";
            errormsg->msg = GETTEXT("File exists");
          }
          #endif
          #ifdef EXDEV
          if (errcode == EXDEV) {
            errormsg->name = "EXDEV";
            errormsg->msg = GETTEXT("Cross-device link");
          }
          #endif
          #ifdef ENODEV
          if (errcode == ENODEV) {
            errormsg->name = "ENODEV";
            errormsg->msg = GETTEXT("No such device");
          }
          #endif
          #ifdef ENOTDIR
          if (errcode == ENOTDIR) {
            errormsg->name = "ENOTDIR";
            errormsg->msg = GETTEXT("Not a directory");
          }
          #endif
          #ifdef EISDIR
          if (errcode == EISDIR) {
            errormsg->name = "EISDIR";
            errormsg->msg = GETTEXT("Is a directory");
          }
          #endif
          #ifdef EINVAL
          if (errcode == EINVAL) {
            errormsg->name = "EINVAL";
            errormsg->msg = GETTEXT("Invalid argument");
          }
          #endif
          #ifdef ENFILE
          if (errcode == ENFILE) {
            errormsg->name = "ENFILE";
            errormsg->msg = GETTEXT("File table overflow");
          }
          #endif
          #ifdef EMFILE
          if (errcode == EMFILE) {
            errormsg->name = "EMFILE";
            errormsg->msg = GETTEXT("Too many open files");
          }
          #endif
          #ifdef ENOTTY
          if (errcode == ENOTTY) {
            errormsg->name = "ENOTTY";
            errormsg->msg = GETTEXT("Inappropriate ioctl for device");
          }
          #endif
          #ifdef ETXTBSY
          if (errcode == ETXTBSY) {
            errormsg->name = "ETXTBSY";
            errormsg->msg = GETTEXT("Text file busy");
          }
          #endif
          #ifdef EFBIG
          if (errcode == EFBIG) {
            errormsg->name = "EFBIG";
            errormsg->msg = GETTEXT("File too large");
          }
          #endif
          #ifdef ENOSPC
          if (errcode == ENOSPC) {
            errormsg->name = "ENOSPC";
            errormsg->msg = GETTEXT("No space left on device");
          }
          #endif
          #ifdef ESPIPE
          if (errcode == ESPIPE) {
            errormsg->name = "ESPIPE";
            errormsg->msg = GETTEXT("Illegal seek");
          }
          #endif
          #ifdef EROFS
          if (errcode == EROFS) {
            errormsg->name = "EROFS";
            errormsg->msg = GETTEXT("Read-only file system");
          }
          #endif
          #ifdef EMLINK
          if (errcode == EMLINK) {
            errormsg->name = "EMLINK";
            errormsg->msg = GETTEXT("Too many links");
          }
          #endif
          #ifdef EPIPE
          if (errcode == EPIPE) {
            errormsg->name = "EPIPE";
            errormsg->msg = GETTEXT("Broken pipe, child process terminated or socket closed");
            # Note that these "translations" exploit that CLISP only catches
            # SIGPIPEs from subprocesses and sockets. Other pipes lead to a
            # deadly signal and never to this error message.
          }
          #endif
          # Errors in math functions:
          #ifdef EDOM
          if (errcode == EDOM) {
            errormsg->name = "EDOM";
            errormsg->msg = GETTEXT("Argument out of domain");
          }
          #endif
          #ifdef ERANGE
          if (errcode == ERANGE) {
            errormsg->name = "ERANGE";
            errormsg->msg = GETTEXT("Result too large");
          }
          #endif
          # Errors in multibyte functions:
          #ifdef EILSEQ
          if (errcode == EILSEQ && EILSEQ != EINVAL) {
            errormsg->name = "EILSEQ";
            errormsg->msg = GETTEXT("Invalid multibyte or wide character");
          }
          #endif
          # Errors related to non-blocking I/O and interrupt I/O:
          #ifdef EWOULDBLOCK
          if (errcode == EWOULDBLOCK) {
            errormsg->name = "EWOULDBLOCK";
            errormsg->msg = GETTEXT("Operation would block");
          }
          #endif
          #ifdef EINPROGRESS
          if (errcode == EINPROGRESS) {
            errormsg->name = "EINPROGRESS";
            errormsg->msg = GETTEXT("Operation now in progress");
          }
          #endif
          #ifdef EALREADY
          if (errcode == EALREADY) {
            errormsg->name = "EALREADY";
            errormsg->msg = GETTEXT("Operation already in progress");
          }
          #endif
          # Other common errors:
          #ifdef ELOOP
          if (errcode == ELOOP) {
            errormsg->name = "ELOOP";
            errormsg->msg = GETTEXT("Too many levels of symbolic links");
          }
          #endif
          #ifdef ENAMETOOLONG
          if (errcode == ENAMETOOLONG) {
            errormsg->name = "ENAMETOOLONG";
            errormsg->msg = GETTEXT("File name too long");
          }
          #endif
          #ifdef ENOTEMPTY
          if (errcode == ENOTEMPTY) {
            errormsg->name = "ENOTEMPTY";
            errormsg->msg = GETTEXT("Directory not empty");
          }
          #endif
          # Errors relating to Network File System (NFS):
          #ifdef ESTALE
          if (errcode == ESTALE) {
            errormsg->name = "ESTALE";
            errormsg->msg = GETTEXT("Stale NFS file handle");
          }
          #endif
          #ifdef EREMOTE
          if (errcode == EREMOTE) {
            errormsg->name = "EREMOTE";
            errormsg->msg = GETTEXT("Too many levels of remote in path");
          }
          #endif
          # Errors relating to sockets, IPC and networking:
          #ifdef ENOTSOCK
          if (errcode == ENOTSOCK) {
            errormsg->name = "ENOTSOCK";
            errormsg->msg = GETTEXT("Socket operation on non-socket");
          }
          #endif
          #ifdef EDESTADDRREQ
          if (errcode == EDESTADDRREQ) {
            errormsg->name = "EDESTADDRREQ";
            errormsg->msg = GETTEXT("Destination address required");
          }
          #endif
          #ifdef EMSGSIZE
          if (errcode == EMSGSIZE) {
            errormsg->name = "EMSGSIZE";
            errormsg->msg = GETTEXT("Message too long");
          }
          #endif
          #ifdef EPROTOTYPE
          if (errcode == EPROTOTYPE) {
            errormsg->name = "EPROTOTYPE";
            errormsg->msg = GETTEXT("Protocol wrong type for socket");
          }
          #endif
          #ifdef ENOPROTOOPT
          if (errcode == ENOPROTOOPT) {
            errormsg->name = "ENOPROTOOPT";
            errormsg->msg = GETTEXT("Option not supported by protocol");
          }
          #endif
          #ifdef EPROTONOSUPPORT
          if (errcode == EPROTONOSUPPORT) {
            errormsg->name = "EPROTONOSUPPORT";
            errormsg->msg = GETTEXT("Protocol not supported");
          }
          #endif
          #ifdef ESOCKTNOSUPPORT
          if (errcode == ESOCKTNOSUPPORT) {
            errormsg->name = "ESOCKTNOSUPPORT";
            errormsg->msg = GETTEXT("Socket type not supported");
          }
          #endif
          #ifdef EOPNOTSUPP
          if (errcode == EOPNOTSUPP) {
            errormsg->name = "EOPNOTSUPP";
            errormsg->msg = GETTEXT("Operation not supported on socket");
          }
          #endif
          #ifdef EPFNOSUPPORT
          if (errcode == EPFNOSUPPORT) {
            errormsg->name = "EPFNOSUPPORT";
            errormsg->msg = GETTEXT("Protocol family not supported");
          }
          #endif
          #ifdef EAFNOSUPPORT
          if (errcode == EAFNOSUPPORT) {
            errormsg->name = "EAFNOSUPPORT";
            errormsg->msg = GETTEXT("Address family not supported by protocol family");
          }
          #endif
          #ifdef EADDRINUSE
          if (errcode == EADDRINUSE) {
            errormsg->name = "EADDRINUSE";
            errormsg->msg = GETTEXT("Address already in use");
          }
          #endif
          #ifdef EADDRNOTAVAIL
          if (errcode == EADDRNOTAVAIL) {
            errormsg->name = "EADDRNOTAVAIL";
            errormsg->msg = GETTEXT("Can't assign requested address");
          }
          #endif
          #ifdef ENETDOWN
          if (errcode == ENETDOWN) {
            errormsg->name = "ENETDOWN";
            errormsg->msg = GETTEXT("Network is down");
          }
          #endif
          #ifdef ENETUNREACH
          if (errcode == ENETUNREACH) {
            errormsg->name = "ENETUNREACH";
            errormsg->msg = GETTEXT("Network is unreachable");
          }
          #endif
          #ifdef ENETRESET
          if (errcode == ENETRESET) {
            errormsg->name = "ENETRESET";
            errormsg->msg = GETTEXT("Network dropped connection on reset");
          }
          #endif
          #ifdef ECONNABORTED
          if (errcode == ECONNABORTED) {
            errormsg->name = "ECONNABORTED";
            errormsg->msg = GETTEXT("Software caused connection abort");
          }
          #endif
          #ifdef ECONNRESET
          if (errcode == ECONNRESET) {
            errormsg->name = "ECONNRESET";
            errormsg->msg = GETTEXT("Connection reset by peer");
          }
          #endif
          #ifdef ENOBUFS
          if (errcode == ENOBUFS) {
            errormsg->name = "ENOBUFS";
            errormsg->msg = GETTEXT("No buffer space available");
          }
          #endif
          #ifdef EISCONN
          if (errcode == EISCONN) {
            errormsg->name = "EISCONN";
            errormsg->msg = GETTEXT("Socket is already connected");
          }
          #endif
          #ifdef ENOTCONN
          if (errcode == ENOTCONN) {
            errormsg->name = "ENOTCONN";
            errormsg->msg = GETTEXT("Socket is not connected");
          }
          #endif
          #ifdef ESHUTDOWN
          if (errcode == ESHUTDOWN) {
            errormsg->name = "ESHUTDOWN";
            errormsg->msg = GETTEXT("Can't send after socket shutdown");
          }
          #endif
          #ifdef ETOOMANYREFS
          if (errcode == ETOOMANYREFS) {
            errormsg->name = "ETOOMANYREFS";
            errormsg->msg = GETTEXT("Too many references: can't splice");
          }
          #endif
          #ifdef ETIMEDOUT
          if (errcode == ETIMEDOUT) {
            errormsg->name = "ETIMEDOUT";
            errormsg->msg = GETTEXT("Connection timed out");
          }
          #endif
          #ifdef ECONNREFUSED
          if (errcode == ECONNREFUSED) {
            errormsg->name = "ECONNREFUSED";
            errormsg->msg = GETTEXT("Connection refused");
          }
          #endif
          #if 0
            errormsg->name = "";
            errormsg->msg = GETTEXT("Remote peer released connection");
          #endif
          #ifdef EHOSTDOWN
          if (errcode == EHOSTDOWN) {
            errormsg->name = "EHOSTDOWN";
            errormsg->msg = GETTEXT("Host is down");
          }
          #endif
          #ifdef EHOSTUNREACH
          if (errcode == EHOSTUNREACH) {
            errormsg->name = "EHOSTUNREACH";
            errormsg->msg = GETTEXT("Host is unreachable");
          }
          #endif
          #if 0
            errormsg->name = "";
            errormsg->msg = GETTEXT("Networking error");
          #endif
          # Quotas:
          #ifdef EPROCLIM
          if (errcode == EPROCLIM) {
            errormsg->name = "EPROCLIM";
            errormsg->msg = GETTEXT("Too many processes");
          }
          #endif
          #ifdef EUSERS
          if (errcode == EUSERS) {
            errormsg->name = "EUSERS";
            errormsg->msg = GETTEXT("Too many users");
          }
          #endif
          #ifdef EDQUOT
          if (errcode == EDQUOT) {
            errormsg->name = "EDQUOT";
            errormsg->msg = GETTEXT("Disk quota exceeded");
          }
          #endif
          # Errors relating to STREAMS:
          #ifdef ENOSTR
          if (errcode == ENOSTR) {
            errormsg->name = "ENOSTR";
            errormsg->msg = GETTEXT("Not a stream device");
          }
          #endif
          #ifdef ETIME
          if (errcode == ETIME) {
            errormsg->name = "ETIME";
            errormsg->msg = GETTEXT("Timer expired");
          }
          #endif
          #ifdef ENOSR
          if (errcode == ENOSR) {
            errormsg->name = "ENOSR";
            errormsg->msg = GETTEXT("Out of stream resources");
          }
          #endif
          #ifdef ENOMSG
          if (errcode == ENOMSG) {
            errormsg->name = "ENOMSG";
            errormsg->msg = GETTEXT("No message of desired type");
          }
          #endif
          #ifdef EBADMSG
          if (errcode == EBADMSG) {
            errormsg->name = "EBADMSG";
            errormsg->msg = GETTEXT("Not a data message");
          }
          #endif
          # Errors relating to SystemV IPC:
          #ifdef EIDRM
          if (errcode == EIDRM) {
            errormsg->name = "EIDRM";
            errormsg->msg = GETTEXT("Identifier removed");
          }
          #endif
          # Errors relating to SystemV record locking:
          #ifdef EDEADLK
          if (errcode == EDEADLK) {
            errormsg->name = "EDEADLK";
            errormsg->msg = GETTEXT("Resource deadlock would occur");
          }
          #endif
          #ifdef ENOLCK
          if (errcode == ENOLCK) {
            errormsg->name = "ENOLCK";
            errormsg->msg = GETTEXT("No record locks available");
          }
          #endif
          # Errors for Remote File System (RFS):
          #ifdef ENONET
          if (errcode == ENONET) {
            errormsg->name = "ENONET";
            errormsg->msg = GETTEXT("Machine is not on the network");
          }
          #endif
          #ifdef EREMOTE
          if (errcode == EREMOTE) {
            errormsg->name = "EREMOTE";
            errormsg->msg = GETTEXT("Object is remote");
          }
          #endif
          #ifdef ERREMOTE
          if (errcode == ERREMOTE) {
            errormsg->name = "ERREMOTE";
            errormsg->msg = GETTEXT("Object is remote");
          }
          #endif
          #ifdef ENOLINK
          if (errcode == ENOLINK) {
            errormsg->name = "ENOLINK";
            errormsg->msg = GETTEXT("Link has been severed");
          }
          #endif
          #ifdef EADV
          if (errcode == EADV) {
            errormsg->name = "EADV";
            errormsg->msg = GETTEXT("Advertise error");
          }
          #endif
          #ifdef ESRMNT
          if (errcode == ESRMNT) {
            errormsg->name = "ESRMNT";
            errormsg->msg = GETTEXT("Srmount error");
          }
          #endif
          #ifdef ECOMM
          if (errcode == ECOMM) {
            errormsg->name = "ECOMM";
            errormsg->msg = GETTEXT("Communication error on send");
          }
          #endif
          #ifdef EPROTO
          if (errcode == EPROTO) {
            errormsg->name = "EPROTO";
            errormsg->msg = GETTEXT("Protocol error");
          }
          #endif
          #ifdef EMULTIHOP
          if (errcode == EMULTIHOP) {
            errormsg->name = "EMULTIHOP";
            errormsg->msg = GETTEXT("Multihop attempted");
          }
          #endif
          #ifdef EDOTDOT
          if (errcode == EDOTDOT) {
            errormsg->name = "EDOTDOT";
            errormsg->msg = "";
          }
          #endif
          #ifdef EREMCHG
          if (errcode == EREMCHG) {
            errormsg->name = "EREMCHG";
            errormsg->msg = GETTEXT("Remote address changed");
          }
          #endif
          # POSIX errors:
          #ifdef ENOSYS
          if (errcode == ENOSYS) {
            errormsg->name = "ENOSYS";
            errormsg->msg = GETTEXT("Function not implemented");
          }
          #endif
          # Other:
          #ifdef EMSDOS # emx 0.8e - 0.8h
          if (errcode == EMSDOS) {
            errormsg->name = "EMSDOS";
            errormsg->msg = GETTEXT("Not supported under MS-DOS");
          }
          #endif
        # If no error message known, default to the system's one.
        if (errormsg->name == NULL)
          errormsg->name = "";
        if (errormsg->msg == NULL || errormsg->msg[0] == '\0') {
          errno = 0;
          errormsg->msg = strerror(errcode);
          if (errno != 0 || errormsg->msg == NULL)
            errormsg->msg = "";
        }
      }

  #ifdef GNU_GETTEXT
    # Now translate after calling get_errormsg().
    #undef clgettext
    #define translate(string)  clgettext(string)
  #else
    #define translate(string)  string
  #endif

    local void OS_error_internal (uintC errcode);
    local void OS_error_internal(errcode)
      var uintC errcode;
      {
        # Meldungbeginn ausgeben:
        #ifdef UNIX
        write_errorstring(GETTEXT("UNIX error "));
        #else
        write_errorstring(GETTEXT("UNIX library error "));
        #endif
        # Fehlernummer ausgeben:
        write_errorobject(fixnum(errcode));
        # Eigene Fehlermeldung ausgeben:
        var os_error_t errormsg;
        get_errormsg(errcode,&errormsg);
        errormsg.msg = translate(errormsg.msg);
        if (!(errormsg.name[0] == 0)) { # bekannter Name?
          write_errorasciz(" (");
          write_errorasciz(errormsg.name);
          write_errorasciz(")");
        }
        if (!(errormsg.msg[0] == 0)) { # nichtleere Meldung?
          write_errorasciz(": ");
          write_errorasciz(errormsg.msg);
        }
      }
    global void OS_error()
      {
        var uintC errcode; # positive Fehlernummer
        end_system_call(); # just in case
        begin_system_call();
        errcode = errno;
        errno = 0; # Fehlercode l�schen (f�rs n�chste Mal)
        end_system_call();
        clr_break_sem_4(); # keine UNIX-Operation mehr aktiv
        begin_error(); # Fehlermeldung anfangen
        if (!nullp(STACK_3)) # *ERROR-HANDLER* = NIL, SYS::*USE-CLCS* /= NIL ?
          STACK_3 = S(simple_os_error);
        OS_error_internal(errcode);
        end_error(args_end_pointer STACKop 7); # Fehlermeldung beenden
      }
    global void OS_file_error(pathname)
      var object pathname;
      {
        var uintC errcode; # positive Fehlernummer
        begin_system_call();
        errcode = errno;
        errno = 0; # Fehlercode l�schen (f�rs n�chste Mal)
        end_system_call();
        clr_break_sem_4(); # keine UNIX-Operation mehr aktiv
        pushSTACK(pathname); # Wert von PATHNAME f�r FILE-ERROR
        begin_error(); # Fehlermeldung anfangen
        if (!nullp(STACK_3)) # *ERROR-HANDLER* = NIL, SYS::*USE-CLCS* /= NIL ?
          STACK_3 = S(simple_file_error);
        OS_error_internal(errcode);
        end_error(args_end_pointer STACKop 7); # Fehlermeldung beenden
      }

  # Ausgabe eines Fehlers, direkt �bers Betriebssystem
  # errno_out(errorcode);
  # > int errorcode: Fehlercode
    global void errno_out (int errorcode);
    global void errno_out(errorcode)
      var int errorcode;
      {
        asciz_out(" errno = ");
        var os_error_t errormsg;
        get_errormsg(errorcode,&errormsg);
        errormsg.msg = translate(errormsg.msg);
        if (errormsg.name[0] != 0 || errormsg.msg[0] != 0) {
          if (errormsg.name[0] != 0) { # bekannter Name?
            asciz_out(errormsg.name);
          } else {
            dez_out(errorcode);
          }
          if (errormsg.msg[0] != 0) { # nichtleere Meldung?
            asciz_out(": "); asciz_out(errormsg.msg);
          }
        } else {
          dez_out(errorcode);
        }
        asciz_out("." NLstring);
      }

