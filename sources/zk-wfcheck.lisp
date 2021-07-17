
;;;======================================================================
;;;                                                                     |
;;;  Copyright (c) 2021, Sentot Kromodimoeljo, William Pase,            |
;;;  Mark Saaltink, Dan Craigen and Irwin Meisels.                      |
;;;  All Rights Reserved.                                               |
;;;                                                                     |
;;;  Redistribution and use in source and binary forms, with or without |
;;;  modification, are permitted provided the following conditions are  |
;;;  met:                                                               |
;;;                                                                     |
;;;  1. Redistributions of source code must retain the above copyright  |
;;;     notice, this list of conditions and the following disclaimer.   |
;;;  2. Redistributions in binary form must reproduce the above         |
;;;     copyright notice, this list of conditions and the following     |
;;;     disclaimer in the documentation and/or other materials provided |
;;;     with the distribution.                                          |
;;;                                                                     |
;;;  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND             |
;;;  CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES,        |
;;;  INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF           |
;;;  MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE           |
;;;  DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDERS AND            |
;;;  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,       |
;;;  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT   |
;;;  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF   |
;;;  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED    |
;;;  AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT        |
;;;  LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING     |
;;;  IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF     |
;;;  THE POSSIBILITY OF SUCH DAMAGE.                                    |
;;;                                                                     |
;;;======================================================================

(in-package "ZK")


;;; Tell the system to call wf-add-decl adding a declaration.

(eval-when (:load-toplevel)
  (pushnew 'wf-add-decl *zk-to-lisp-hooks*))

;;; Useful information.

;;; Function signatures.
;;; The following signature kinds are used:
;;; AXIOM, RULE, FORWARD ASSUMPTION  axiom (not really a signature, but ...)
;;; FUNCTION		function or ZF function
;;; LIBRARY-UNIT	library unit (not really a signature)

;;; Add a signature for a function in the initial theory. The
;;; formal-types-or-arity argument determines how the function arguments are
;;; checked, as follows:
;;;
;;; arity                  function
;;;			   information
;;; ---------------------  -------- -----------
;;; number >= 0            arity of function is number
;;; -1			   n-ary function

(defmacro add-function (name arity)
  (let (sig)
    (setq sig (make-wf-signature :kind 'function
				 :arity arity))
    `(put-event-property (get-event ',name) 'wf-signature ',sig)))

(eval-when (:load-toplevel)
  (unless *compiling-zk*

;;; Boolean functions.
  
  (add-function TRUE 0)
  (add-function FALSE 0)
  (add-function NOT 1)
  (add-function AND -1)
  (add-function OR -1)
  (add-function IMPLIES 2)
  
;;; Integer functions.
  
  (add-function + -1)
  (add-function - 2)
  (add-function * -1)
  (add-function DIV 2)
  (add-function REM 2)
  (add-function MOD 2)
  (add-function NEGATE 1)
  (add-function ABS 1)
    
;;; Elementary functions.
  
  (add-function ORD 1)
  (add-function SUCC 1)
  (add-function PRED 1)
  (add-function < 2)
  (add-function <= 2)
  (add-function > 2)
  (add-function >= 2)
  (add-function MIN 2)
  (add-function MAX 2)
  
  (add-function = 2)
  (add-function IF 3)
  
;;; Set functions.
  
  (add-function NULLSET 0)
  (add-function SETADD 2)
  (add-function UNIT 1)
  (add-function IN 2)
  (add-function SUBSET 2)
  (add-function UNION 2)
  (add-function INTER 2)
  (add-function DIFF 2)
  (add-function DELTA 2)
  (add-function POWERSET 1)
  (add-function CUP 1)
  (add-function MAKE-SET -1)
  (add-function CHOICE 1)
  
;;; Type functions.
  
  (add-function INT 0)
  (add-function BOOL 0)
    
;;; Miscellaneous functions.
  
  (add-function TYPE-OF 1)
  (add-function M< 2)
  (add-function RANGE 2)
  (add-function EPSILON-INDUCTION 1)
  
  ))

;;; Typing context - maps a name into a wf-variable.

(defvar *context*)

;;; Local vocabulary for storing function signatures.  It is a
;;; list of (name . wf-signature) pairs.

(defvar *local-vocabulary*)

;;; Global free variable flag - when this variable is lambda-bound to a non-nil
;;; value, free variables are allowed in expressions.

(defvar *free-variables-allowed*)


;;; Error flag - set to t when an error is reported.

(defvar *wf-error-flag*)

;;; Name of current event for error reporting.

(defvar *wf-event-name*)

;;; Vocabulary and context functions.

;;; Get information about a variable from the current context.

(defmacro get-variable (name)
  `(cdr (assoc-eq ,name *context*)))

;;; Generate an alist of (name . wf-variable) from a list of names
;;; or just a name. The only slot for wf-variable is the used slot.

(defmacro make-variables (names)
  `(mapcar #'(lambda (name)
	       (cons name
		     (make-wf-variable)))
	   (if (listp ,names) ,names (list ,names))))

;;; Add the given alist of wf-variables to context while the body is executed.

(defmacro with-updated-context (vars &body body)
  `(let ((*context* (append ,vars *context*)))
     ,@body))

;;; Add (name . data) to the local vocabulary while the body is executed.
;;; This is used to enable processing of recursive functions.

(defmacro with-updated-vocabulary (name data &body body)
  `(let ((*local-vocabulary* (cons (cons ,name ,data) *local-vocabulary*)))
     ,@body))

;;; Access macro for retrieving the argument list of a name, axiom, rule,
;;; frule or grule.

(defmacro get-event-args (event)
  `(funcall (intern (string-append (event-kind ,event) "-ARGS")
		    *zk-package*)
	    ,event))

;;; Retrieve a signature for a name from the local vocabulary or database.
;;; Axiom, rule, frule and grule signatures are created on the fly.

(defun get-signature (name &aux event)
  (or (cdr (assoc-eq name *local-vocabulary*))
      (and (setq event (get-event name))
	   (if (member-eq (event-type event) '(AXIOM RULE FRULE GRULE))
	       (make-wf-signature :kind (event-type event)
				  :arity (length (get-event-args event)))
	       (get-event-property event 'wf-signature)))
      (and (setq event (get-event (car (true-name name)))) ; pseudo events
           (eq (cdr (true-name name)) 'po)
           (make-wf-signature :kind 'axiom :arity 0))))


;;; Macros used in well-formedness checking.


;;; Check that the argument name has not been declared.

(defmacro new-declaration (name)
  `(when (get-signature ,name)
     (wf-error 'redeclaration ,name)))

;;; Check that none of the argument names have been declared.

(defmacro new-declarations (names)
  `(dolist (name ,names)
     (new-declaration name)))

;;; Check that the argument name is not in the typing context. The resulting
;;; error and its severity depend on the context in which the check is made.

(defun new-variable (name)
  (when (get-variable name)
    (wf-error 'variable-already-used name t)))	; warning

;;; Check that none of the argument names are in the typing context.

(defmacro new-variables (names)
  `(mapc #'(lambda (name) (new-variable name)) ,names))

;;; Check the argument list of wf-variables and report on those that were
;;; unused.

(defun check-unused-variables (which vars)
  (let ((unused-vars (mapcan #'(lambda (var)
				 (when (null (wf-variable-used (cdr var)))
				   (list (car var))))
			     vars)))
    (when unused-vars
      (wf-error 'variables-unused (list which unused-vars) t))))


;;; Allow free variables when checking an expression.

(defmacro with-free-variables (&body body)
  `(let ((*free-variables-allowed* t))
     ,@body))

;;; Create a system-generated name from the argument components.

(defun sysname (&rest args)
  (loop for x in (cdr args)
	appending (list system-separator-char x) into nlist
	finally (return (intern (apply #'string-append (cons (first args)
							     nlist))
				*zk-package*))))

;;; Top-level wf checking.

;;; WF check a ZK sexp.
;;; Returns one of the following values:
;;; :ERROR		               an error was encountered
;;; :OK				       no errors were encountered

(defun wf-zk-sexp (sexp)
  (let ((*context* nil)
	(*local-vocabulary* nil)
	(*wf-error-flag* nil)
	(*free-variables-allowed* nil)
	(*wf-event-name* (cond
			   ((member-eq (first sexp) *zk-declarations*)
			    (second sexp))
			   (t
			    (first sexp)))))
    (catch 'wf-error
      (funcall (get (first sexp) 'wf-function) sexp))
    (if *wf-error-flag*
	:ERROR
	:OK)))


;;; Function declarations, stubs, groups, and ZF function declarations.

;;; WF check a function declaration.

(defpropfun (function wf-function) (decl)
  (let (formals sig)
    (new-declaration (second decl))
    (setq formals (wf-variables (third decl)))
    (setq sig (make-wf-signature :kind 'FUNCTION :arity (length formals)))
    (with-updated-context formals
      (wf-annotations (fourth decl))
      (with-updated-vocabulary (second decl) sig
	(wf-expression (fifth decl))))
    (check-unused-variables "function formals" formals)))

;;; WF check a function stub.

(defpropfun (function-stub wf-function) (stub)
  (new-declaration (second stub))
  (wf-variables (third stub)))

;;; WF check a list of variables, essentially making sure there are
;;; no duplicates. This is done for function formal parameters, lists
;;; of variables in ZF bodies and lists of variables in quantifications.
;;; Returns an alist of (name . wf-variable) for the names in the list.

(defun wf-variables (vars)
  (let ((dups (duplicates vars)))
    (when dups
      (wf-error 'duplicate-variables dups))
    (make-variables vars)))

;;; WF check a ZF function declaration.

(defpropfun (zf-function wf-function) (decl)
  (let (formals)
    (new-declaration (second decl))
    (setq formals (wf-variables (third decl)))
    (with-updated-context formals
      (wf-zf-function-body (fourth decl)))
    (check-unused-variables "ZF function formals" formals)))


;;; Axioms.

;;; WF check an axiom.

(defpropfun (axiom wf-function) (decl)
  (let (formals)
    (new-declaration (second decl))
    (setq formals (wf-variables (third decl)))
    (with-updated-context formals
      (wf-expression (fourth decl)))
    (check-unused-variables "axiom formals" formals)))

;;; WF check a rewrite rule.

(defpropfun (rule wf-function) (decl)
  (let (formals)
    (new-declaration (second decl))
    (setq formals (wf-variables (third decl)))
    (with-updated-context formals
      (wf-expression (fourth decl)))
    (check-unused-variables "rule formals" formals)))

;;; WF check a forward rule.

(defpropfun (frule wf-function) (decl)
  (let (formals)
    (new-declaration (second decl))
    (setq formals (wf-variables (third decl)))
    (with-updated-context formals
      (wf-expression (fourth decl)))
    (check-unused-variables "frule formals" formals)))

;;; WF check an assumption rule.

(defpropfun (grule wf-function) (decl)
  (let (formals)
    (new-declaration (second decl))
    (setq formals (wf-variables (third decl)))
    (with-updated-context formals
      (wf-expression (fourth decl)))
    (check-unused-variables "grule formals" formals)))


;;; Annotations, ZF bodies, expressions, ranges, and identifier lists.

;;; WF check a list of annotations.

(defun wf-annotations (annotations)
  (dolist (annotation annotations)
    (case (first annotation)
      ((MEASURE)
       (wf-expression (second annotation))))))

(defun wf-zf-function-body (body)
  (case (first body)
    (MAP
      (loop for x in (cddr body)
	    appending (first x) into names
	    do (wf-expression (second x))
	    finally (new-variables names)
		    (let ((vars (wf-variables names)))
		      (with-updated-context vars
			(wf-expression (second body)))
		      (check-unused-variables "ZF body variables" vars))))
    (SELECT
      (let ((name (first (second body)))
	    vars)
	(new-variable name)
	(setq vars (make-variables name))
	(wf-expression (second (second body)))
	(with-updated-context vars
	  (wf-expression (third body)))
	(check-unused-variables "ZF body variables" vars)))
    (THAT
      (new-variable (second body))
      (let ((vars (make-variables (second body))))
	(with-updated-context vars
	  (wf-expression (third body)))
	(check-unused-variables "ZF body variables" vars)))))

;;; WF check an expression.

(defun wf-expression (expr)
  (cond
    ((symbolp expr)
     (if *free-variables-allowed*
	 (let ((sym (get-variable expr)))
	   (when sym
	     (setf (wf-variable-used sym) t)))
	 (let ((sym (get-variable expr)))
	   (unless sym
	     (wf-error 'invalid-free-variable-reference expr))
	   (setf (wf-variable-used sym) t))))
    ((integerp expr)
     nil)
    ((not (listp expr))
     (wf-error 'invalid-expression expr))
    ((member-eq (first expr) '(ALL SOME))
     (wf-quantification expr))
    (t
     (wf-function-application expr))))

(defun wf-quantification (quant)
  (let ((vars (wf-variables (second quant))))
    (with-updated-context vars
      (wf-expression (third quant)))
    (check-unused-variables "quantified variables" vars)))

(defun wf-function-application (appl)
  (let* ((name (first appl))
	 (sig (get-signature name)))
    (unless sig
      (wf-error 'name-not-declared name))
    (unless (eq (wf-signature-kind sig) 'FUNCTION)
      (wf-error 'apply-non-function name))
    (unless (or (< (wf-signature-arity sig) 0)
		(= (wf-signature-arity sig) (length (cdr appl))))
      (wf-error 'wrong-number-of-arguments appl))
    (mapc #'(lambda (x) (wf-expression x)) (cdr appl))))



;;; Commands.

;;; WF check a command which takes an identifier and optional expression

(defpropfun (apply wf-function) (cmd)
  (let ((sig (get-signature (second cmd))))
    (unless sig
      (wf-error 'name-not-declared (second cmd)))
    (unless (eq (wf-signature-kind sig) 'RULE)
      (wf-error 'not-a-rule-name (second cmd)))
    (when (third cmd)
      (with-free-variables
	(wf-expression (third cmd))))))

;;; WF check the delete-hypotheses command

(defpropfun ((delete-hypotheses) wf-function) (cmd)
  (with-free-variables
    (loop for hyp in (cdr cmd)
	  do (wf-expression hyp))))

;;; WF check a command which may take an expression.

(defpropfun ((equality-substitute induct label split suppose)
             wf-function)
  (cmd)
  (when (second cmd)
    (with-free-variables
      (wf-expression (second cmd)))))

;;; WF check a command which takes an expression or function name.

(defpropfun ((invoke print-rules-about rules-about) wf-function) (cmd)
  (if (symbolp (second cmd))
      (let ((sig (get-signature (second cmd))))
	(unless sig
	  (wf-error 'name-not-declared (second cmd)))
	(unless (eq (wf-signature-kind sig) `FUNCTION)
	  (wf-error 'not-a-function-name (second cmd))))
      (with-free-variables
	(wf-expression (second cmd)))))

;;; WF check an instantiate command.

(defpropfun (instantiate wf-function) (cmd)
  (with-free-variables
    (loop for val in (cdr cmd)
	  collecting (first val) into names
	  do (wf-expression (second val))
	  finally (let ((dups (duplicates names)))
		    (when dups
		      (wf-error 'duplicate-instantiations dups))))))

;;; WF check a command which may take the name of a declaration.

(defpropfun ((print-declaration print-proof print-proof-summary undo-back-to
	      undo-back-thru) wf-function) (cmd)
  (when (second cmd)
    (unless (get-signature (second cmd))
      (wf-error 'name-not-declared (second cmd)))))

;;; WF check a command which may take the name of a declaration or an
;;; expression.

(defpropfun (try wf-function) (cmd)
  (when (second cmd)
    (if (symbolp (second cmd))
	(unless (get-signature (second cmd))
	  (wf-error 'name-not-declared (second cmd)))
	(with-free-variables
	  (wf-expression (second cmd))))))

;;; WF check a prenex command.

(defpropfun (prenex wf-function) (cmd)
  (wf-variables (second cmd)))

;;; WF check an use command.

(defpropfun ((add use) wf-function) (cmd)
  (let* ((name (second cmd))
	 (sig (get-signature name))
	 formals)
    (unless sig
      (wf-error 'name-not-declared name))
    (unless (member-eq (wf-signature-kind sig)
		       `(AXIOM FRULE GRULE RULE FUNCTION))
      (wf-error 'not-a-function-or-axiom-name name))
    (setq formals
          (let ((kind (cdr (true-name name)))
                (event (get-event (car (true-name name)))))
            (cond
	     ((tag-p event)
	      (wf-error 'not-a-function-or-axiom-name name))	      
	     ((null kind)
	      (get-event-args event))
	     ((eq kind 'po)
	      (unique (list-of-free-variables-unexpanded
		       (event-formula event)))))))
    (with-free-variables
      (loop for val in (cddr cmd)
	    collecting (first val) into names
	    do (unless (member-eq (without-proof-logging
                                   (zk-internal-form (first val) nil))
                                  formals)
		 (wf-error 'not-a-formal (list (first val) name)))
	    (wf-expression (second val))
	    finally (let ((dups (duplicates names)))
		      (when dups
			(wf-error 'duplicate-instantiations dups)))))))

;;; WF check a command with no arguments, or with arguments for which syntax
;;; checking is sufficient.

(defpropfun ((delete edit load make print-library-status
              browse-begin browse-forward browse-down browse-up browse-back
              browse-print-formula
	      back back-thru back-to cases check-proof
	      conjunctive contradict disjunctive
              dump-log end-script
	      help next
              knuth-bendix log-on log-off
              print-formula print-history print-recent-declarations
	      clear-stats check-all-proofs print-stats
	      print-status print-working-directory
	      prove prove-by-cases prove-by-induction
	      prove-by-rearrange quit read rearrange reduce
	      rebrowse reset retry rewrite script set-library
	      set-working-directory simplify
	      trivial-rewrite trivial-simplify trivial-reduce undo)
	     wf-function)
  (cmd)
  (declare (ignore cmd)))



;;; WF check a with-subexpression command qualifier.

(defpropfun (with-subexpression wf-function) (cmd)
  (with-free-variables
    (wf-expression (second cmd)))
  (funcall (get (first (third cmd)) 'wf-function) (third cmd)))

(defpropfun ((with-enabled with-disabled) wf-function) (cmd)
  (mapcar #'(lambda (u) (unless (get-signature u)
			  (wf-error 'name-not-declared u)))
	  (second cmd))
  (funcall (get (first (third cmd)) 'wf-function) (third cmd)))

(defpropfun ((disabled with-instantiation without-instantiation
		       with-case-analysis without-case-analysis
		       with-normalization without-normalization)
	     wf-function)
	    (cmd)
  (funcall (get (first (second cmd)) 'wf-function) (second cmd)))


;;; Utility functions.

;;; Print the error message denoted by error-type.

(defun wf-error (error-type &optional object warning)
  (print-error error-type object *wf-event-name* warning)
  (unless warning
    (setq *wf-error-flag* t)
    (throw 'wf-error nil)))

;;; Functions for adding well-formedness information to the database.

(defun add-wf-info (name indicator info)
  (put-event-property (get-event name) indicator info))

;;; Add well-formedness information to the database for the argument
;;; declaration.  It is assumed that the declaration is well-formed.  If an
;;; expression must be checked (to get its type or to determine if it is
;;; manifest), it is checked in the null typing context.

(defun wf-add-decl (decl result)
  (when result
    (let ((add-function (get (first decl) 'wf-add-function)))
      (when add-function
	(let ((*context* nil)
	      (*local-vocabulary* nil)
	      (*free-variables-allowed* nil))
	  (funcall add-function decl))))))

;;; Add well-formedness information to the database for a function, ZF function
;;; declaration, or function stub.

(defpropfun ((function zf-function function-stub) wf-add-function) (decl)
  (add-wf-info (second decl) 'wf-signature
	       (make-wf-signature :kind 'FUNCTION
				  :arity (length (third decl)))))

;;; Add well-formedness information to the database for a load command.
;;; This is just a hack to allow undo, print-declaration, etc. to use a library
;;; object name.

(defpropfun (load wf-add-function) (cmd)
  (add-wf-info (second cmd)
	       'wf-signature
	       (make-wf-signature :kind 'LIBRARY-UNIT)))
