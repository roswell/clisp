;;; Lisp wrappers for the Netica API
;;; <http://norsys.com/netica_c_api.htm>

(require "netica")

(defpackage "NETICA"
  (:export "*verbose*" "*env*" "*license*" "error-category" "error-message"
           "check-errors" "start-netica" "close-netica" "save-net"
           "make-net" "net-info" "make-node" "node-info"
           "get-beliefs" "enter-finding"))

(in-package "SYS")
(eval-when (compile load) (setf (package-lock "SYS") nil))
(pushnew :netica *features*)

;;; low level wrappers

(eval-when (compile eval)
  (defmacro make-node-wrapper (func &rest more-args)
    (let* ((fun (if (consp func) (first func) func))
           (orig (symbol-name fun)) (node (gensym orig)) (vec (gensym orig))
           (length-form (if (consp func)
                            (subst node '<node> (second func))
                            `(netica::GetNodeNumberStates_bn ,node)))
           (name (intern (subseq orig 0 (position #\_ orig)) "NETICA")))
      `(progn
         (export ',name "NETICA")
         (defun ,name (,node ,@more-args)
           ,(concatenate 'string "A low-level wrapper for " orig)
           (ffi:with-c-var (,vec 'ffi:c-pointer (,fun ,node ,@more-args))
             (ffi:cast ,vec `(ffi:c-ptr (ffi:c-array netica::prob_bn
                                                     ,,length-form)))))))))

(defun adjust-number-of-states (num-states type)
  (+ num-states
     (gethash type
              (load-time-value
               (let ((ht (make-hash-table)))
                 (setf (gethash netica::CONTINUOUS_TYPE ht) 1)
                 (setf (gethash netica::DISCRETE_TYPE ht) 0)
                 ht)))))

(make-node-wrapper netica::GetNodeBeliefs_bn)
(make-node-wrapper netica::GetNodeExpectedUtils_bn)
(make-node-wrapper netica::GetNodeLikelihood_bn)
(make-node-wrapper netica::GetNodeProbs_bn parent-states)
(make-node-wrapper (netica::GetNodeLevels_bn
                    (adjust-number-of-states
                     (netica::GetNodeNumberStates_bn <node>)
                     (netica::GetNodeType_bn <node>))))

;;; user interface variables
(defvar netica:*verbose* *standard-output* "the netica log stream")
(defvar netica:*env* nil "the current netica environment")
(defvar netica:*license* "" "the netica license key - ask norsys")

;;; helpers
(defun netica:error-category (err)
  "return the list of categories where the error belongs"
  (mapcan (lambda (c)
            (unless (zerop (netica::ErrorCategory_ns (symbol-value c) err))
              (list c)))
          '(netica::OUT_OF_MEMORY_CND
            netica::USER_ABORTED_CND
            netica::FROM_WRAPPER_CND
            netica::FROM_DEVELOPER_CND
            netica::INCONS_FINDING_CND)))

(defun netica:error-message (err)
  "Convert netica error to a string"
  (format nil "~s(~s)~@[ ~s~]: ~s~%"
          (ffi:enum-from-value 'netica::errseverity_ns
                               (netica::ErrorSeverity_ns err))
          (netica::ErrorNumber_ns err)
          (netica::error-category err)
          (netica::ErrorMessage_ns err)))

(defun netica:check-errors (&key ((:env netica:*env*) netica:*env*) (clear t)
                            (severity netica::NOTHING_ERR))
  "Check all errors of the given severity and optionally clear them."
  (let ((err nil))
    (loop (setq err (netica::GetError_ns netica:*env* severity err))
      (unless err (return))
      (if (>= (netica::ErrorSeverity_ns err) netica::ERROR_ERR)
          (cerror (if clear "clear and proceed" "show next error")
                  (netica:error-message err))
          (warn (netica:error-message err)))
      (when clear
        (netica::ClearError_ns err) (setq err nil)
        (format *error-output* "~&...cleared~%")))))

(defun netica:start-netica (&key ((:license netica:*license*) netica:*license*)
                            ((:verbose netica:*verbose*) netica:*verbose*))
  "Start netica, initialize it, and return the new environment.
Sets netica:*env* to this environment on success."
  (let ((env (netica::NewNeticaEnviron_ns netica:*license* nil nil))
        status message)
    (when netica:*verbose*
      (format netica:*verbose* "~&;; new environment: ~s~%" env))
    (multiple-value-setq (status env message) (netica::InitNetica_bn env))
    (when netica:*verbose*
      (format netica:*verbose* ";; init status=~s~%~a~%" status message))
    (multiple-value-setq (status message) (netica::GetNeticaVersion_bn env))
    (when netica:*verbose*
      (format netica:*verbose* ";; version=~s (~s)~%" status message))
    (setq status (netica::ArgumentChecking_ns netica::REGULAR_CHECK env))
    (when netica:*verbose*
      (format netica:*verbose* ";; checking level: ~s --> ~s~%"
              status netica::REGULAR_CHECK))
    (setq status (netica::MaxMemoryUsage_ns
                  (float netica::QUERY_CHECK 1d0) env))
    (when netica:*verbose*
      (format netica:*verbose* ";; memory usage: ~s bytes~%" status))
    (netica:check-errors :env env)
    (setq netica:*env* env)))

(defun netica:close-netica (&key (env netica:*env*)
                            ((:verbose netica:*verbose*) netica:*verbose*))
  "Terminate the netica session.
Sets netica:*env* to NIL when it was closed."
  (netica:check-errors)
  (multiple-value-bind (status message) (netica::CloseNetica_bn netica:*env*)
    (when netica:*verbose*
      (format netica:*verbose* "~&;; close status=~s~%~a~%" status message)))
  (when (eq env netica:*env*)
    (setq netica:*env* nil)))

(defun required-argument (f a) (error "~s: missing ~s argument" f a))

(defun netica:make-net (&key (name (symbol-name (gensym)))
                        (comment nil) (title nil)
                        ((:env netica:*env*) netica:*env*)
                        ((:verbose netica:*verbose*) netica:*verbose*))
  "Make a network with a given name and return it."
  (let ((net (netica::NewNet_bn name netica:*env*)))
    (when netica:*verbose*
      (format netica:*verbose* "~&;; new net ~s: ~s~%" name net))
    (netica:check-errors)
    (when comment
      (netica::SetNetComment_bn net comment)
      (netica:check-errors))
    (when title
      (netica::SetNetTitle_bn net title)
      (netica:check-errors))
    net))

(defun netica:net-info (net)
  "Print information about the net."
  (format t "~&net: ~s~%name: ~s~%" net (netica::GetNetName_bn net))
  (let ((title (netica::GetNetTitle_bn net)))
    (unless (zerop (length title))
      (format t "title: ~s~%" title)))
  (let ((comment (netica::GetNetComment_bn net)))
    (unless (zerop (length comment))
      (format t "comment: ~s~%" comment)))
  (let ((file-name (netica::GetNetFileName_bn net)))
    (unless (zerop (length file-name))
      (format t "file-name: ~s~%" file-name)))
  (let* ((nodes (netica::GetNetNodes_bn net))
         (count (netica::LengthNodeList_bn nodes)))
    (dotimes (ii count)
      (format t " * [~:d] " ii)
      (netica:node-info (netica::NthNode_bn nodes ii))))
  (netica:check-errors))

(defun netica:make-node (&key (name (symbol-name (gensym)))
                         (net (required-argument 'netica:make-node :net))
                         (kind netica::NATURE_NODE)
                         (levels nil) (states nil)
                         (num-states (if levels 0 (length states)))
                         (title nil) (comment nil)
                         (parents nil) (cpt nil)
                         ((:env netica:*env*) netica:*env*)
                         ((:verbose netica:*verbose*) netica:*verbose*))
  "Make a network node with the given parameters and return it.
The parameters are: name, net, kind, states (state name list),
levels (vector), number of states, parents list, cpt.
CPT (conditional probability table) is a list of conses:
 ((parent-state-vector . node-state-probability-vector) ...)
one cons for each combination of possible parent states,
where parent-state-vector is a vector of parent states,
 its length being (length parents);
and node-state-probability-vector is a vector of corresponding node state
 probabilities, its length being (length states).
When LEVELS is supplied, the node is continuous."
  (let ((node (netica::NewNode_bn name num-states net)))
    (when netica:*verbose*
      (format netica:*verbose* "~&;; new node ~s: ~s~%" name node))
    (netica:check-errors)
    (when (/= kind netica::NATURE_NODE)
      (netica::SetNodeKind_bn node kind)
      (netica:check-errors))
    (when levels
      (netica::SetNodeLevels_bn node (1- (length levels)) levels)
      (netica:check-errors))
    (loop :for state :in states :and idx :upfrom 0
      :do (if (consp state)
              (progn
                (netica::SetNodeStateName_bn node idx (car state))
                (netica::SetNodeStateTitle_bn node idx (cdr state)))
              (netica::SetNodeStateName_bn node idx state))
      (netica:check-errors))
    (when title
      (netica::SetNodeTitle_bn node title)
      (netica:check-errors))
    (when comment
      (netica::SetNodeComment_bn node comment)
      (netica:check-errors))
    (dolist (parent parents)
      (netica::AddLink_bn parent node)
      (netica:check-errors))
    (dolist (probs cpt)
      (netica::SetNodeProbs_bn node
                               (map 'vector #'netica::StateNamed_bn
                                    (car probs) parents)
                               (cdr probs))
      (netica:check-errors))
    (netica:check-errors)
    node))

(defun netica:node-info (node)
  "Print information about the node."
  (format t "~&node: ~s (net: ~s)~%name: ~s~%type: ~s~%" node
          (netica::GetNodeNet_bn node) (netica::GetNodeName_bn node)
          (ffi:enum-from-value 'netica::nodetype_bn
                               (netica::GetNodeType_bn node)))
  (let ((title (netica::GetNodeTitle_bn node)))
    (unless (zerop (length title))
      (format t "title: ~s~%" title)))
  (let ((count (netica::GetNodeNumberStates_bn node)))
    (format t "state count: ~s~%" count)
    (dotimes (state count)
      (format t "[~d] name: ~s  title: ~s~%" state
              (netica::GetNodeStateName_bn node state)
              (netica::GetNodeStateTitle_bn node state))))
  (let ((levels (netica::GetNodeLevels node)))
    (dotimes (ii (length levels))
      (format t "[~d] level: ~s~%" ii (aref levels ii))))
  (netica:check-errors))

(defun netica:get-beliefs (node &key
                           ((:env netica:*env*) netica:*env*)
                           ((:verbose netica:*verbose*) netica:*verbose*))
  "Get the belief vector for the node."
  (let ((beliefs (netica::GetNodeBeliefs node))
        (name (netica::GetNodeName_bn node)))
    (netica:check-errors)
    (when netica:*verbose*
      (loop :for belief :across beliefs :and index :upfrom 0 :do
        (format netica:*verbose* "~&;; ~a: P(~s)=~f~%" name
                (netica::GetNodeStateName_bn node index) belief))
      (netica:check-errors))
    beliefs))

(defun netica:enter-finding (net node state &key
                             ((:env netica:*env*) netica:*env*)
                             ((:verbose netica:*verbose*) netica:*verbose*))
  "Enter a finding by node and state names"
  (let* ((nd (netica::NodeNamed_bn node net))
         (st (netica::StateNamed_bn state nd)))
    (netica::EnterFinding_bn nd st)
    (netica:check-errors)
    (when netica:*verbose*
      (format netica:*verbose* "~&;; ~s: set to ~s~%" node state))))

(defun netica:save-net (file net &key
                        ((:env netica:*env*) netica:*env*)
                        ((:verbose netica:*verbose*) netica:*verbose*))
  "Save the network to the file."
  (let ((out (netica::NewStreamFile_ns
              (namestring (translate-logical-pathname
                           (merge-pathnames
                            file #.(make-pathname :type "dne"))))
              netica:*env* nil)))
    (when netica:*verbose*
      (format netica:*verbose* "~&;; new stream: ~s~&" out))
    (netica:check-errors)
    (netica::WriteNet_bn net out)
    (netica:check-errors)
    (when netica:*verbose*
      (format netica:*verbose* ";; saved ~s to ~s~%" net
              (netica::GetNetFileName_bn net)))))

(push "NETICA" ext:*system-package-list*)
(eval-when (compile load)
  (setf (ext:package-lock ext:*system-package-list*) t))
