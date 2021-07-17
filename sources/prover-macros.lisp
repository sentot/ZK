
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


;;; =====================================================================
;;; Main macros for constructing prover commands.
;;; =====================================================================

(in-package "ZK")


;;; These are flags and parameters used by the prover.

(proclaim '(special *max-backchain-depth*
                    *simplifier-substitutes-equalities-flag*
                    *simplifier-instantiates-variables-flag*
                    *reduce-does-case-analysis-flag*
                    *reduce-does-quantifier-case-analysis-flag*
                    *reduce-applies-rules-flag* *reduce-applies-functions-flag*
                    *reduce-normalizes-flag*
                    *trace-prover-flag* *print-parser-warnings-flag*
                    *record-proof-logs-flag*))


;;; Variable to track command modifiers.

(defvar *current-modifiers* nil)

;;; The following macros are modifiers for prover commands.
;;; Typically they are called with-OPTION or without-OPTION.
;;; The body (which typically involves a call to reduce) is run with
;;; the option turned on or with the option turned off respectively.

;;; Run body with focus on a selected subexpression.

(defmacro with-subexpression ((expr) &body body)
  `(let ((*current-modifiers* (cons (cons :subexpression ,expr)
                                    *current-modifiers*)))
     . ,body))

;;; Run body with automatic instantiation in the simplifier
;;; turned on.

(defmacro with-instantiation (&body body)
  `(let ((*current-modifiers* (cons (cons :instantiate t)
                                       *current-modifiers*))
         (*simplifier-instantiates-variables-flag* t))
     . ,body))

;;; Run body with automatic instantiation in the simplifier
;;; turned off.

(defmacro without-instantiation (&body body)
  `(let ((*current-modifiers* (cons (cons :instantiate nil)
                                    *current-modifiers*))
         (*simplifier-instantiates-variables-flag* nil))
     . ,body))

;;; Run body with case analysis turned on in the reducer.

(defmacro with-case-analysis (&body body)
  `(let ((*current-modifiers* (cons (cons :case-analysis t)
                                    *current-modifiers*))
         (*reduce-does-case-analysis-flag* t)
         (*reduce-does-quantifier-case-analysis-flag* t))
     . ,body))

;;; Run body with case analysis turned off in the reducer.

(defmacro without-case-analysis (&body body)
  `(let ((*current-modifiers* (cons (cons :case-analysis nil)
                                    *current-modifiers*))
         (*reduce-does-case-analysis-flag* nil)
         (*reduce-does-quantifier-case-analysis-flag* nil))
     . ,body))

;;; Run body with "if" normalization turned on in the reducer.

(defmacro with-normalization (&body body)
  `(let ((*current-modifiers* (cons (cons :normalization t)
                                    *current-modifiers*))
         (*reduce-normalizes-flag* t))
     . ,body))

;;; Run body with "if" normalization turned off in the reducer.
;;; Without "if" normalization, propositional simplification is incomplete.

(defmacro without-normalization (&body body)
  `(let ((*current-modifiers* (cons (cons :normalization nil)
                                    *current-modifiers*))
         (*reduce-normalizes-flag* nil))
     . ,body))


;;; This is a modifier for declarations. The heuristics associated
;;; with a declaration (in body) is disabled by default.

(defmacro disabled (&body body)
  `(let ((*current-modifiers* (cons (cons :disabled t)
                                    *current-modifiers*)))
     . ,body))

;;; Run body with proof logging turned on.
;;; Proof logging allows proofs to be independently checked.
;;; Proof logs can also be used by a proof browser.

(defmacro with-proof-logging (&body body)
  `(let ((*record-proof-logs-flag* t))
     . ,body))

;;; Run body with proof logging turned off.

(defmacro without-proof-logging (&body body)
  `(let ((*record-proof-logs-flag* nil))
     . ,body))


(defun event-enabled-status (event)
  (let ((type (event-type event)))
    (cond ((eq type 'frule)
           (list (get 'frule 'enabled) event (frule-enabled event)))
          ((eq type 'grule)
           (list (get 'grule 'enabled) event (grule-enabled event)))
          ((eq type 'rule)
           (list (get 'rule 'enabled) event (rule-enabled event)))
          ((eq type 'ufunction)
           (list (get 'ufunction 'enabled) event (ufunction-enabled event))))))

(defun set-event-enabled (event enabled)
  (let ((enabled-slot (get (event-type event) 'enabled)))
    (when enabled-slot (funcall enabled-slot event enabled))))

;;; Run body with the specified events' heuristices enabled.

(defmacro with-enabled ((event-names) &body body)
  (let* ((events (gensym))
         (enabled-status (gensym)))
    `(let* ((*current-modifiers* (cons (cons :enable ,event-names)
                                       *current-modifiers*))
            (,events (mapcan #'(lambda (u)
                                 (group-event-list (get-event u)))
                                 ,event-names))
            (,enabled-status
               (remove-if #'null (mapcar #'event-enabled-status ,events))))
       (unwind-protect
           (progn (mapc #'(lambda (u) (set-event-enabled u t)) ,events)
                  . ,body)
         (mapc #'(lambda (u) (funcall (first u) (second u) (third u)))
               ,enabled-status)))))

;;; Run body with the specified events' heuristices disabled.

(defmacro with-disabled ((event-names) &body body)
  (let* ((events (gensym))
         (enabled-status (gensym)))
    `(let* ((*current-modifiers* (cons (cons :disable ,event-names)
                                       *current-modifiers*))
            (,events (mapcan #'(lambda (u) (group-event-list (get-event u)))
                             ,event-names))
            (,enabled-status
               (remove-if #'null (mapcar #'event-enabled-status ,events))))
       (unwind-protect
           (progn (mapc #'(lambda (u) (set-event-enabled u nil)) ,events)
                  . ,body)
         (mapc #'(lambda (u) (funcall (first u) (second u) (third u)))
               ,enabled-status)))))


;;; Run body with tracing and warnings turned off in the prover.
;;; This is used for adding database entries silently.

(defmacro with-prover-muzzled (&body body)
  `(let ((*trace-prover-flag* nil)
         (*print-parser-warnings-flag* nil))
     . ,body))

;;; Run body with the function definition disabled.

(defmacro with-function-disabled ((uf) &body body)
  (let ((tmp (gensym)))
    `(let ((,tmp (ufunction-enabled ,uf)))
       (unwind-protect (progn (setf (ufunction-enabled ,uf) nil) . ,body)
         (setf (ufunction-enabled ,uf) ,tmp)))))

;;; Run body with the given rule disabled.

(defmacro with-rule-disabled ((rule) &body body)
  (let ((tmp (gensym)))
    `(let ((,tmp (rule-enabled ,rule)))
       (unwind-protect (progn (setf (rule-enabled ,rule) nil) . ,body)
         (setf (rule-enabled ,rule) ,tmp)))))

;;; Run body with the event's heuristics disabled.

(defmacro with-event-disabled ((event) &body body)
  (let ((enabled-tmp (gensym))
        (enabled-slot (gensym)))
    `(let* ((,enabled-slot (get (event-type ,event) 'enabled))
            (,enabled-tmp (when ,enabled-slot (funcall ,enabled-slot ,event))))
       (unwind-protect
          (progn (when ,enabled-slot (funcall ,enabled-slot ,event nil))
                       . ,body)
          (when ,enabled-slot (funcall ,enabled-slot ,event ,enabled-tmp))))))


;;; ===== The help system variables =====

;;; help topic list and list of help alists - to be bound to specific values

(defvar *help-topic-list* nil)
(defvar *help-alists* nil)

;;; Lisp mode help alist.

(defvar *lisp-mode-help-alist* nil)
(proclaim '(special *lisp-mode-help-topic-list*))

;;; the print width normally used when printing help

(defparameter *help-maximum-print-width* 65)

;;; The following help names are reserved by the help system; they are the
;;; symbols representing the types of help available.  The print strings for
;;; them are also stored here.

(defparameter *help-types*
    '((prover-command "(Prover Command)")
      (error-code "(Error Code)")
      (extra-help "(Extra Help)")
      (proof-step "(Proof Step)")))

;;; ==========================================================
;;; Generic macros for defining commands and help
;;; ==========================================================

;;; Check that a new help entry has a valid symbol and type, and that
;;; the explanation is well-formed (is a list of printer directives).

(defun defhelp-check (symbol type explain help-alist)
  (cond ((assoc-eq symbol *help-types*)
         (error "The symbol '~A' is reserved by the help system." symbol))
        ((not (assoc-eq type *help-types*))
         (error "The symbol '~A' is not a help type." type))
        ((null explain)
         (if (assoc-eq symbol help-alist)
             (cond
              ((neq type (second (assoc-eq symbol help-alist)))
               (error "Attempt to disable help for '~A' with a different type."
                      symbol))
              (t (format t "~%Warning, the help for '~A' has been disabled."
                         symbol)))
           (error "Attempt to disable help for '~A' which is non-existent."
                  symbol)))
        ((not (explainp explain))
         (error "The explanation '~A' is not valid." explain))
        ((assoc-eq symbol help-alist)
         (cond
          ((neq type (second (assoc-eq symbol help-alist)))
           (error "Attempt to replace help for '~A' with a different type."
                  symbol))
               (t (format t "~%Warning, the help for '~A' has been replaced."
                          symbol))))))

;;; Macro for adding help to the database. By default, adds the help to the
;;; ZK help.

(defmacro defhelp (symbol type explain
                   &optional (help-alist '*lisp-mode-help-alist*))
  `(progn 'compile
          (defhelp-check ',symbol ',type ',explain ,help-alist)
          (push (list ',symbol ',type ',explain) ,help-alist)
          ',symbol))


;;; Check that a new error message entry is well-formed.

(defun deferror-check (symbol arglist message extra-help)
  symbol                                        ;checked by defhelp
  extra-help                                    ;checked by defhelp
  (cond ((or (atom arglist) (not (null (cdr arglist))))
         (error "The arglist for '~A' is not valid." symbol))
        ;; this check is a little dirty since we don't know
        ;; exactly what is going to be done with the argument
        ((not (explainp (eval (subst-equal nil (car arglist) message))))
         (error "The explanation '~A' is not valid." message))))

;;; Macro for adding a new error message entry. The help is
;;; intended to be an explanation of how to correct the error.
;;; By default, the entry is added to *lisp-mode-help-alist*.

(defmacro deferror (name arglist message extra-help
                    &optional (help-alist '*lisp-mode-help-alist*))
  `(progn 'compile
          (deferror-check ',name ',arglist ',message ',extra-help)
          (defpropfun (,name error) ,arglist ,@arglist ,message)
          (defhelp ,name error-code ,extra-help ,help-alist)
          ',name))


;;; In case the macro is used before *current-display* and *display-history*
;;; are declared.

(proclaim '(special *current-display* *display-history*))

;;; List of all ZK commands defined by defcmd.

(defvar *zk-commands* nil)

;;; Macro to define a prover command.  There are two forms.  The first is just
;;; like defun but requires a documentation string which is set with the
;;; function as well as being added to the ZK help database.  The second
;;; sets up a command, taking an optional formula argument, to transform the
;;; current formula.  If the formula argument is supplied then the current
;;; formula is set to that prior to the command being performed, otherwise it
;;; is called on the current formula.  After the command, the display and
;;; current formula are updated to the result. In both cases, the name of the
;;; defined command is added to *zk-commands*.

(defmacro defcmd (name args &body body)
  
  ;; simple error check to ensure documentation
  (unless (not (null (cdr body)))
    (error "Missing documentation or body for defcmd ~A." name))
  
  (if (neq (car (last args)) ':display)
      ;; this is the simple case where it is like defun
      `(progn 'compile
              (push ',name *zk-commands*)
              (defhelp ,name prover-command ((:syntax ,(cons name args))
                                             (:newline)
                                             (:newline)
                                             . ,(car body)))
              (defun ,name ,args . , (cdr body)))       ;turf explain
      
      ;; the case where it is actually a proof step command
      (let* ((result (gensym))
             (args (butlast args))
             (args-opt (remove-eq '&optional args))
             (arg-list (append args
                               (if (member-eq '&optional args)
                                   nil
                                   '(&optional))
                               '(event-or-formula))))
        `(progn 'compile
                (push ',name *zk-commands*)
                (defhelp ,name proof-step ((:syntax ,(cons name arg-list))
                                           (:newline)
                                           (:newline)
                                           . ,(car body)))
                (defun ,name ,arg-list
                  (when (if event-or-formula
                        (try event-or-formula)
                        *current-display*)
                    (let* ((*proof-log* nil)
                           (index (display-formula-index *current-display*))
                           (,result
                            (funcall (function
                                      (lambda ,(append args-opt '(display))
                                        . ,(cdr body)))
                                     . ,(append args-opt
                                         '(*current-display*)))))
                      
                      ;; successful commands update the user's display
                      (when (display-p ,result)
                        (setf (display-command ,result)
                              (list ',name . ,args-opt))
                        ;; process resulting formula
                        ;; (strip off quantifiers etc.)
                        (setf (display-formula ,result)
                              (post-process-formula ,result
                                                    *current-display*))
                        ;; set event and number
                        (setf (display-event ,result)
                              (display-event *current-display*))
                        (setf (display-number ,result)
                              (1+ (display-number *current-display*)))
                        ;; set up the caseof field, pop up if t
                        (cond ((eq (display-caseof ,result) t)
                               (setf (display-caseof ,result) nil))
                              ;; inherit caseof, unless set by command
                              ((null (display-caseof ,result))
                               (setf (display-caseof ,result)
                                     (display-caseof *current-display*))))
                        (setf (display-prover-flags ,result)
                              *current-modifiers*)
                        (setf (display-details ,result)
                              *proof-log*)
                        ;; the return indicates success/failure
                        (update-display ,result)))))))))
