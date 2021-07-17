
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


;;; Define the translation from ZK declarations to prover events.
;;; ---------------------------------------------------------------------



;;; Primitive Functions

;;; return the modifier function for a decl
(defmacro get-modifier (decl)
  `(get ,decl 'zk-modifier))

;;; return the translation function for a decl
(defmacro get-trans (decl)
  `(get ,decl 'zk-trans))

;;; return the output form function for a decl
(defmacro get-output (decl)
  `(get ,decl 'zk-output))



;;; Top Level Translation Functions

;;; List of functions to call after adding a declaration to the database.
;;; Each function in the list is called with the sexp form of the
;;; declaration.  Used by other parts of the ZK processing code (e.g.,
;;; the well-formedness checker) to add additional information to events.

(defvar *zk-to-lisp-hooks* nil)

;;; The top level function which takes an ZK declaration or command as
;;; input, generates the Lisp mode events, adds the events to the database,
;;; and calls the functions in *zk-to-lisp-hooks* to add other
;;; mode-specific information.
;;; If everything is successful, the name of the declaration is returned.
;;; Otherwise nil is returned and appropriate error messages are printed.

(defun zk-to-lisp (decl)
  (zk-to-lisp-aux decl))

(defun zk-to-lisp-aux (decl)
  (let ((modifier (get-modifier (car decl))))
    (if (null modifier)
	(zk-to-lisp-aux-aux decl)		; bare command
	(apply modifier (cdr decl)))))		; command has modifier

(defun zk-to-lisp-aux-aux (decl)
  (let* ((event-list (zk-decls-to-events decl))
         (result (cond ((atom event-list) event-list)	; command
                       (t (zk-add-events-to-database	; declaration
                           decl event-list)))))
    (loop for func in *zk-to-lisp-hooks*
	  do (funcall func decl result))
    result))

;;; Given a declaration, this function converts it to a list of events.
;;; Given a command, it will execute the command.
;;; Both are done using ``translation'' functions.

(defun zk-decls-to-events (decl)
  (let ((trans (or (get-trans (car decl))	;translation
		   (symbol-function (car decl)))))	;or default
    (when (null trans)
      (error "Missing translation function for '~A'." (car decl)))
    (apply trans (cdr decl))))



;;; Given a declaration and a list of events associated with the
;;; declaration, this function adds the events to the database.
;;; If the additions succeed, the proof obligation for the
;;; declaration is generated and the name declared is returned.
;;; Otherwise, nil is returned and the database is left in its original
;;; state.
;;; list-of-events is a list of pairs:
;;;   the first of a pair is an add-event function with its arguments,
;;;   the second of a pair is an event spec in ZK concrete syntax.
(defun zk-add-events-to-database (decl list-of-events)
  (let ((count 0)                       ;number of events added
        (result nil)                    ;name of declaration
        (name (group-name *history*)))  ;name to recover back to
    (unwind-protect
        (loop for pair in list-of-events
              unless (null (apply (caar pair) (cdar pair))) ; add event
              do (let ((event (get-event (second (car pair)))))
                   (setf (event-proof event) nil)
                   (setf (event-proven event) t)
                   (put-event-property event 'zk-event (cdr pair))
                   (put-event-property
                    event 'zk-modifiers
                    (append *current-modifiers*
                            (get-event-property event 'zk-modifiers)))
                   (incf count)))
      ;; if any failures have occured then recovery is required
      ;; otherwise the events added are folded to a single group
      ;; failures can be caused by aborts and/or erroneous events
      (with-abort-disabled
       (cond ((not (= count (length list-of-events)))
              (undo-back-to name))
             (t (fold-events count)
                (make-group-assumption (car *history*))
                ;; ***** if this is to be recursive then the next line
                ;;       must be moved to outside of the resursive call
                (zk-add-proof-obligations
                 (generate-proof-obligations decl))
                (setq result (second decl))))))
    result))                           ;success

(defun zk-log-entry (entry)
  (let ((type (car entry)))
    (cond ((and (or (eq type 'if-true) (eq type 'if-false) (eq type 'if-equal))
		(> (length entry) 2))
	   (list type (second entry) (zk-internal-variables (third entry)) t))
	  ((and (eq type 'remove-universal) (> (length entry) 2))
	   (list type (second entry)
		 (mapcar #'zk-internal-variables (third entry)) t))
	  ((eq type 'rename-universal)
	   (list type (second entry) (zk-internal-variables (third entry))
		 (zk-internal-variables (fourth entry))))
	  ((or (eq type 'induct) (eq type 'look-up))
	   (list type (second entry) (zk-internal-variables (third entry))))
	  ((eq type 'instantiate-universal)
	   (if (= (length entry) 3)
	       (list type (second entry) (zk-internal-variables (third entry)))
	     (list type (second entry)
		   (zk-internal-variables (third entry)) t)))
	  (t entry))))
	  

;;; add an alist of names and proof obligations to the database
;;; each proof obligation is added to the associated named event
;;; ***** NOTE: need to save the raw obligation and simplification log,
;;; ***** so that try can stuff them in the log.
(defun zk-add-proof-obligations (proof-obligations)
  (let ((ponames
         (loop for (name raw-obligation log simple-obligation)
               in proof-obligations
               for event = (get-event name)
               for event-type = (event-type event)
               ;; no error checking here as reasonable recovery is not possible
               do (let* ((*proof-log* nil)
                         (vars1 (mapcar #'zk-internal-variables
                                        (unique-symbol
                                         (zk-list-of-free-variables
                                          raw-obligation))))
                         (internal-obligation
                          (zk-internal-form simple-obligation
					    (mapcar #'(lambda (u) u 2) vars1)))
                         (vars2 (unique-symbol
				 (list-of-free-variables-unexpanded
				  internal-obligation))))
                    ;; append log and patch index
                    (setq *proof-log*
			  (mapcar #'zk-log-entry (append *proof-log* log)))
                    ;; must log removal of quantifications that disappear
                    (let ((i nil))
                      (loop for var in vars1
                            do
                            (cond ((member-eq var vars2)
				   (push 2 i))
                                  (t (push-proof-log 'remove-universal i)
                                     (push-proof-log 'is-boolean i t)))))
                    (setf (event-formula event) internal-obligation)
                    (setf (event-rawpo event) raw-obligation)
                    (setf (event-details event) *proof-log*)
                    (setf (event-proof event) nil)	;initially no proof
                    ;; if the proof obligation is true then this is assumption
                    (setf (event-proven event) (true-p internal-obligation))
                    ;; set the access number to the number of the access event
                    (setf (event-access event) (event-number event)))
               collect name)))
    (setf (event-ponames (group-event (car *history*))) ponames)))

(defun append-conversion-log (conversion-log log offset-index)
  (cond ((null conversion-log) log)
        (t (let ((entry (car conversion-log)))
             (cons (cons (car entry)
                         (cons (append (cadr entry) offset-index)
                               (cddr entry)))
                   (append-conversion-log (cdr conversion-log)
                                          log offset-index))))))



;;; ZK Axiom Translation
;;; Each produce a list of events in ZK concrete syntax.

(defpropfun (axiom zk-trans) (an args expr)
  (zk-axiom an args expr))

(defun zk-axiom (an args expr)
  `(((add-axiom ,an ,args ,expr) . (axiom ,an ,args ,expr))))

(defpropfun (rule zk-trans) (an args expr)
  (zk-rule an args expr))

(defun zk-rule (an args expr)
  `(((add-rule ,an ,args ,expr) . (rule ,an ,args ,expr))))

;;; the next routine is for generated disabled rules

(defun zk-disabled-rule (an args expr)
  `(((add-disabled-rule ,an ,args ,expr) . (rule ,an ,args ,expr))))

(defun add-disabled-rule (an args expr)
  (let* ((*proof-log* nil)
         (internal-expr (zk-internal-form expr (index-args args))))
    (when
     (disabled (rule an (mapcar #'zk-internal-variables args) internal-expr))
     (setf (event-details (get-event an)) *proof-log*)
     (put-event-property (get-event an)
                         'zk-modifiers
                         (cons (cons :disabled t) nil)))))

(defpropfun (frule zk-trans) (an args expr)
  (zk-frule an args expr))

(defun zk-frule (an args expr)
  `(((add-frule ,an ,args ,expr) . (frule ,an ,args ,expr))))


(defpropfun (grule zk-trans) (an args expr)
  (zk-grule an args expr))

(defun zk-grule (an args expr)
  `(((add-grule ,an ,args ,expr) . (grule ,an ,args ,expr))))




;;; ZK Function Translation

;;; for a function stub we just generate a name event
(defpropfun (function-stub zk-trans) (fn parameter-list)
  (zk-function-stub fn parameter-list))

(defun zk-function-stub (fn parameter-list)
  `(((add-function-stub ,fn ,parameter-list) .
     (function-stub ,fn ,parameter-list))))

;;; for a function with body we just generate a name event
(defpropfun (function zk-trans) (fn parameter-list measure expr)
  (zk-function-decl fn parameter-list (second (assoc-eq 'measure measure))
                    expr))

(defun zk-function-decl (fn parameter-list measure expr)
  `(((add-ufunction ,fn ,parameter-list ,measure ,expr) .
     (function ,fn ,parameter-list ,(and measure `((measure ,measure)))
               ,expr))))



;;; ZF function declaration
(defpropfun (zf-function zk-trans) (fn parameter-list zf-body)
  (cond ((eq (car zf-body) 'map)
	 (zk-zf-map-function fn parameter-list
			     (second zf-body)
			     (cddr zf-body)
			     zf-body))
	((eq (car zf-body) 'select)
	 (zk-zf-select-function fn parameter-list
				(first (second zf-body))
				(second (second zf-body))
				(third zf-body)
				zf-body))
	((eq (car zf-body) 'that)
	 (zk-zf-that-function fn parameter-list
			      (second zf-body)
			      (third zf-body)
			      zf-body))
	(t (error "Invalid function in ZK to Lisp mode translator '~A'."
                  (car zf-body)))))

(defun zk-bindings (descriptions)
  (loop for description in descriptions
	append (loop for var in (first description)
		     collect (cons var (second description)))))

(defun zk-zf-map-function (fn parameter-list body binding-list zf-body)
  (let* ((bindings (zk-bindings binding-list))
	 (binding-names (mapcar #'car bindings))
	 (vn (unclash (car binding-names)
                      (append parameter-list
                              binding-names
                              (unique-symbol (list-of-all-variables body))))))
    `(((add-zf-function ,fn ,parameter-list ,zf-body) .
       (zf-function ,fn ,parameter-list (map ,body . ,binding-list)))
      ,@(zk-disabled-rule
         (genname fn ".DEFINITION") `(,vn . ,parameter-list)
         `(= (in ,vn (,fn . ,parameter-list))
             (some ,binding-names
                   ,(make-conjunction
                     `(,@(loop for binding in bindings
                               collect `(in ,(car binding) ,(cdr binding)))
                         (= ,vn ,body)))))))))

(defun zk-zf-select-function (fn parameter-list vn set condition zf-body)
  `(((add-zf-function ,fn ,parameter-list ,zf-body) .
     (zf-function ,fn ,parameter-list (select (,vn ,set) ,condition)))
    ,@(zk-rule (genname fn ".DEFINITION") `(,vn . ,parameter-list)
	       `(= (in ,vn (,fn . ,parameter-list))
		   (and (in ,vn ,set)
			,condition)))))

(defun zk-zf-that-function (fn parameter-list vn body zf-body)
  `(((add-zf-function ,fn ,parameter-list ,zf-body) .
     (zf-function ,fn ,parameter-list (that ,vn ,body)))
    ,@(zk-axiom (genname fn ".DEFINITION") parameter-list
		`(= ,(subst-eq `(,fn . ,parameter-list)
			       vn
			       (zk-rename-quantified-variables
				body parameter-list))
		    (true)))))



;;; ZK Command Translations

;;; Only those translations which require changes are defined.
;;; All others simply default to the Lisp mode command of the same name.
;;; *command-name-translations* is defined in zk-header.lisp.

(defpropfun (back-thru zk-trans) (&optional command)
  (back-thru (sublis-symbol *command-name-translations* command)))

(defpropfun (back-to zk-trans) (&optional command)
  (back-to (sublis-symbol *command-name-translations* command)))

(defpropfun (load zk-trans) (id)
  `(((uload ,id) . (load ,id))))

(defpropfun (help zk-trans) (&optional identifier)
  (help identifier))

(defpropfun (delete-hypotheses zk-trans) (&rest hyps)
  (delete-hypotheses (without-proof-logging
                      (mapcar #'(lambda (u) (zk-internal-form u nil))
                              hyps))))

(defpropfun (equality-substitute zk-trans) (&optional expr)
  (if expr
      (equality-substitute (without-proof-logging (zk-internal-form expr nil)))
    (equality-substitute)))

(defpropfun (induct zk-trans) (&optional expr)
  (if expr
      (induct (without-proof-logging (zk-internal-form expr nil)))
    (induct)))

(defpropfun (instantiate zk-trans) (&rest instantiations)
  (instantiate (without-proof-logging
                (mapcar #'(lambda (u) (make-= (zk-internal-variables (first u))
                                              (zk-internal-form (second u)
                                                                nil)))
                        instantiations))))

(defpropfun (invoke zk-trans) (expr)
  (if (symbolp expr)
      (invoke expr)
    (invoke (without-proof-logging (zk-internal-form expr nil)))))

(defpropfun (label zk-trans) (expr)
  (label (without-proof-logging (zk-internal-form expr nil))))

(defpropfun (next zk-trans) ()
  (nextf))



(defpropfun (print-declaration zk-trans) (identifier)
  (print-event identifier))

(defpropfun (print-proof zk-trans) (&optional identifier)
  (print-proof identifier 2))

(defpropfun (print-proof-summary zk-trans) (&optional identifier)
  (print-proof identifier 0))

(defpropfun (print-recent-declarations zk-trans) ()
  (print-history :last 8))

(defpropfun (print-rules-about zk-trans) (expression)
  (print-rules (if (symbolp expression)
                   expression
                 (without-proof-logging (zk-internal-form expression nil)))
               t))

(defpropfun (reduce zk-trans) ()
  (reduce))

(defpropfun (rules-about zk-trans) (expression)
  (print-rules (if (symbolp  expression)
                   expression
                 (without-proof-logging (zk-internal-form expression nil)))))

(defpropfun (split zk-trans) (expr)
  (split (without-proof-logging (zk-internal-form expr nil))))

(defpropfun (suppose zk-trans) (expr)
  (suppose (without-proof-logging (zk-internal-form expr nil))))

(defpropfun (apply zk-trans) (identifier &optional expr)
  (applyf identifier
          (unless (null expr)
            (without-proof-logging (zk-internal-form expr nil)))))

(defpropfun (add zk-trans) (identifier &rest instantiations)
  (add identifier
       (without-proof-logging
        (mapcar #'(lambda (u) (make-= (zk-internal-variables (first u))
                                      (zk-internal-form (second u) nil)))
                instantiations))))

(defpropfun (prenex zk-trans) (&optional variables)
  (cond ((null variables) (prenex))
        (t (prenex (mapcar #'zk-internal-variables variables)))))

(defpropfun (use zk-trans) (identifier &rest instantiations)
  (assume identifier
          (without-proof-logging
           (mapcar #'(lambda (u) (make-= (zk-internal-variables (first u))
                                         (zk-internal-form (second u) nil)))
                   instantiations))))

(defpropfun (try zk-trans) (expr)
  (if (symbolp expr)
      (try expr)
    (try (without-proof-logging (zk-internal-form expr nil)))))



;;; ZK Printing of Event Structures

;;; returns the printable form of event-struct
;;; this is bound to *format-event* by ZK mode
(defun zk-format-event (event-struct)
  (zk-format-modifiers
    (reverse (get-event-property event-struct 'zk-modifiers))
    (or (get-event-property event-struct 'zk-event)
	(funcall (get (event-type event-struct) 'zk-event) event-struct))))

(defun zk-format-modifiers (modifiers expr)
  (cond ((null modifiers) expr)
	(t (let ((modifier (caar modifiers))
		 (value (cdar modifiers)))
	     (cond ((eq modifier :subexpression)
		    `(with-subexpression
		       ,value ,(zk-format-modifiers (cdr modifiers) expr)))
		   ((eq modifier :instantiate)
		    (if (null value)
			`(without-instantiation
			   ,(zk-format-modifiers (cdr modifiers) expr))
			`(with-instantiation
			   ,(zk-format-modifiers (cdr modifiers) expr))))
		   ((eq modifier :case-analysis)
		    (if (null value)
			`(without-case-analysis
			   ,(zk-format-modifiers (cdr modifiers) expr))
		      `(with-case-analysis
			,(zk-format-modifiers (cdr modifiers) expr))))
		   ((eq modifier :normalization)
		    (if (null value)
			`(without-normalization
			   ,(zk-format-modifiers (cdr modifiers) expr))
		      `(with-normalization
			,(zk-format-modifiers (cdr modifiers) expr))))
		   ((eq modifier :disable)
		    `(with-disabled
		      ,value ,(zk-format-modifiers (cdr modifiers) expr)))
		   ((eq modifier :enable)
		    `(with-enabled
		      ,value ,(zk-format-modifiers (cdr modifiers) expr)))
		   ((eq modifier :disabled)
		    `(disabled ,(zk-format-modifiers (cdr modifiers) expr)))
		   (t (zk-format-modifiers (cdr modifiers) expr)))))))

;;; returns the declared name of an event
;;; this is bound to *format-event-name* by ZK mode
(defun zk-format-event-name (event)
  (second (get-event-property event 'zk-event)))

(defpropfun (tag zk-event) (tag)
  `(tag ,(tag-name tag)))

(defpropfun (axiom zk-event) (axiom)
  `(axiom ,(axiom-name axiom) ,(axiom-args axiom) ,(axiom-formula axiom)))

(defpropfun (rule zk-event) (rule)
  `(rule ,(rule-name rule) ,(rule-args rule) ,(rule-formula rule)))

(defpropfun (frule zk-event) (frule)
  `(frule ,(frule-name frule) ,(frule-args frule) ,(frule-formula frule)))

(defpropfun (grule zk-event) (grule)
  `(grule ,(grule-name grule) ,(grule-args grule) ,(grule-formula grule)))

(defpropfun (ufunction zk-event) (uf)
  `(function ,(ufunction-name uf) ,(ufunction-args uf)
	     ,(if (ufunction-measure uf)
		  `((measure ,(ufunction-measure uf))) nil)
	     ,(ufunction-body uf)))

(defpropfun (function-stub zk-event) (stub)
  `(function-stub ,(function-stub-name stub) ,(function-stub-args stub)))

(defpropfun (zf-function zk-event) (zf)
  `(zf-function ,(zf-function-name zf) ,(zf-function-args zf)
		,(zf-function-body zf)))

(defpropfun (uload zk-event) (uload)
  `(load ,(uload-name uload)))


;;; ZK Printer

;;; Arrange for ZK formatting to be done when body is executed.

(defmacro with-zk-formatting (&body body)
  `(let ((*format-event* #'zk-format-event)
	 (*format-event-name* #'zk-format-event-name)
	 (*format-display* #'zk-format-display)
	 (*format-output* #'zk-output-form))
     ,@body))

;;; ZK formatting of display structures

;;; returns the printable form of display-struct
;;; this is bound to *format-display* by ZK mode

(defun zk-format-display (display-struct)
  (zk-format-display-aux (lisp-format-display display-struct)))

(defun zk-format-display-aux (cmd)
  (case (first cmd)
    ((with-subexpression with-disabled with-enabled)
     `(,(first cmd) ,(second (car (second cmd)))
	,(zk-format-display-aux (third cmd))))
    ((with-instantiation without-instantiation
       with-case-analysis without-case-analysis
       with-normalization without-normalization
      disabled)
     `(,(first cmd) ,(zk-format-display-aux (second cmd))))
    (t
     (setq cmd (cons (car cmd) (mapcar #'unquote (cdr cmd))))
     (let ((display (get (first cmd) 'zk-display)))
       (if display
	   (apply display (cdr cmd))
	 cmd)))))

(defpropfun (closef zk-display) ()
  `(close))

(defpropfun (delete-hypotheses zk-display) (hyps)
  `(delete-hypotheses . ,hyps))

(defpropfun (equality-substitute zk-display) (expr)
  (if (null expr)
      `(equality-substitute)
      `(equality-substitute ,expr)))

(defpropfun (induct zk-display) (expr)
  (if (null expr)
      `(induct)
      `(induct ,expr)))

(defpropfun (instantiate zk-display) (instantiations)
  `(instantiate . ,(mapcar #'cdr instantiations)))

(defpropfun (nextf zk-display) ()
  `(next))

#|
(defpropfun (reduce zk-display) ()
  `(reduce))
|#

(defpropfun (applyf zk-display) (identifier expr)
  `(apply ,identifier . ,(when expr (list expr))))

(defpropfun (prenex zk-display) (variables)
  `(prenex . ,(when variables (list variables))))

(defpropfun (add zk-display) (identifier instantiations)
  `(add ,identifier . ,(mapcar #'cdr
			       instantiations)))

(defpropfun (assume zk-display) (identifier instantiations)
  `(use ,identifier . ,(mapcar #'cdr
			       instantiations)))



;;; ZK Additional Conversions

(defparameter *variable-prefix-string* ")")


;;; **** create bool-p if there are free variables

(defun zk-internal-form (formula index)
  (let* ((vars (unique (list-of-free-variables-unexpanded formula)))
	 (bool-p (and vars
		      (make-context-for-bool-p
		       (make-all (last vars) *true*)
		       (cdr index)))))
    (zk-internal-variables
     (zk-internal-make-set
      (zk-internal-expand formula index bool-p)
      index))))

(defun zk-internal-variable-list (vars)
  (mapcar #'(lambda (x) (or (and (variable-p x) x)
                            (input-variable-p
                             (genname *variable-prefix-string* x))))
          vars))

;;; Don't need to log this either.
;;; This conversion needs to be done last!!!
(defun zk-internal-variables (formula)
  (cond ((variable-p formula) formula)
	((atom formula)
	 (if (symbolp formula)
	     (let ((variable (genname *variable-prefix-string* formula)))
	       (input-variable-p variable)
	       variable)
	     formula))
        ((all-p formula)
         (make-all (mapcar #'zk-internal-variables (all-vars formula))
                   (zk-internal-variables (all-expr formula))))
        ((some-p formula)
         (make-some (mapcar #'zk-internal-variables (some-vars formula))
                    (zk-internal-variables (some-expr formula))))
	(t (cons (car formula)
                 (mapcar #'zk-internal-variables (cdr formula))))))

(defun zk-internal-expand (formula index bool-p)
  (cond ((atom formula) formula)
	((and (and-p formula) (null (cdr formula)))
         (log-and-0 index)
         *true*)
        ((and (and-p formula) (null (cddr formula)))
         (let ((e (zk-internal-expand
		   (cadr formula) (cons 1 index)
		   (make-context-for-bool-p formula index))))
           (log-and-1 index)
           (cond ((or bool-p (bool-p e))
		  (log-remove-coercion-for-boolean-or-bool-p e index bool-p)
                  e)
                 (t (push-proof-log 'is-boolean (if-left-index))
		    (push-proof-log 'syntax index t)
                    (make-and e *true*)))))
	((and (or-p formula) (null (cdr formula)))
         (log-or-0 index)
         *false*)
        ((and (or-p formula) (null (cddr formula)))
         (let ((e (zk-internal-expand
		   (cadr formula) (cons 1 index)
		   (make-context-for-bool-p formula index))))
           (log-or-1 index)
           (cond ((or bool-p (bool-p e))
		  (log-remove-coercion-for-boolean-or-bool-p e index bool-p)
                  e)
                 (t (push-proof-log 'is-boolean (if-right-index))
		    (push-proof-log 'syntax index t)
                    (make-or e *false*)))))
	((and (+-p formula) (null (cdr formula)))
         (push-proof-log 'syntax index)
         (push-proof-log 'compute index)
	 0)
        ((and (+-p formula) (null (cddr formula)))
         (let ((e (zk-internal-expand (cadr formula) (cons 1 index) nil)))
           (push-proof-log 'syntax index)
           (make-+ e 0)))
	((and (*-p formula) (null (cdr formula)))
         (push-proof-log 'syntax index)
         (push-proof-log 'compute index)
	 1)
        ((and (*-p formula) (null (cddr formula)))
         (let ((e (zk-internal-expand (cadr formula) (cons 1 index) nil)))
           (push-proof-log 'syntax index)
           (make-* e 1)))
        ((or (all-p formula) (some-p formula))
         (let ((e (zk-internal-expand (all-expr formula)
				      (all-expr-index)
				      (make-context-for-bool-p formula index))))
           (list (first formula) (second formula) e)))
        ((if-p formula)
         (let ((test (zk-internal-expand
		      (if-test formula) (if-test-index)
		      (make-context-for-bool-p formula index)))
               (left (zk-internal-expand (if-left formula)
                                              (if-left-index)
                                              bool-p))
               (right (zk-internal-expand (if-right formula)
                                               (if-right-index)
                                               bool-p)))
           (make-if test left right)))
        (t (cons (car formula)
                 (loop for e in (cdr formula)
                       for i = 1 then (+ i 1)
                       collect (zk-internal-expand
                                e
                                (cons i index)
				(make-context-for-bool-p formula index)))))))



(defun zk-internal-make-set (formula index)
  (cond ((atom formula) formula)
        ((or (all-p formula) (some-p formula))
         (let ((e (zk-internal-make-set (all-expr formula) (all-expr-index))))
           (list (first formula) (second formula) e)))
        (t (let ((arguments (loop for e in (cdr formula)
                                  for i = 1 then (+ i 1)
                                  collect (zk-internal-make-set
                                           e (cons i index)))))
             (cond ((eq (car formula) 'make-set)
                    (push-proof-log 'syntax index)
                    (zk-internal-make-set-aux arguments))
                   (t (cons (car formula) arguments)))))))

(defun zk-internal-make-set-aux (elements)
  (cond ((null elements) `(nullset))
	(t `(setadd ,(car elements)
                    ,(zk-internal-make-set-aux (cdr elements))))))



;;; Convert Lisp mode sexps in a list of printer directives, or a single
;;; Lisp mode sexp, to ZK output form.

(defun zk-output-form (sexp)
  (cond
   ((atom sexp)
    (zk-output-variables sexp))
   ((symbolp (car sexp))		; single sexp
    (zk-output-sexp sexp))
   ((member-eq (caar sexp) *printer-directives*)	; directive list
    (mapcar #'zk-output-directive sexp))
   (t
    (error "invalid form ~A to zk-output-form" sexp))))

;;; Convert a Lisp mode sexp which is known to be an expression (not a command
;;; or list of variables) to ZK output form.

(defsubst zk-output-expr (exp)
  (zk-output-variables exp))

;;; Convert a Lisp mode sexp to ZK output form. The sexp may be an event (in
;;; Lisp mode output form), a command, or a formula.

(defun zk-output-sexp (sexp &aux fn)
  (cond
   ((atom sexp)
    (zk-output-variables sexp))
   ((setq fn (get-output (car sexp)))
    ;; special-cased command
    (funcall fn (mapcar #'unquote sexp)))
   ((get (car sexp) 'zk-modifier)
    ;; with-xxx, etc.
    (cons (car sexp) (mapcar #'zk-output-sexp (cdr sexp))))
   ((member-eq (or (cdr (assoc-eq (car sexp) *command-name-translations*))
		   (car sexp))
	       *zk-commands*)
    ;; a Lisp mode command that does not require special treatment
    (cons (zk-output-command-name (car sexp))
	  (mapcar #'(lambda (x)
		      (zk-output-expr (unquote x)))
		  (cdr sexp))))
   (t
    ;; an expression
    (zk-output-expr sexp))))


;; If argument is a quoted sexp, remove the quote.

(defun unquote (x)
  (if (and (consp x) (eq (car x) 'quote))
      (second x)
    x))

;;; Convert a Lisp mode command name to the corresponding ZK command name.

(defun zk-output-command-name (n)
  (or (car (rassoc-eq n *command-name-translations*)) n))

;;; Convert Lisp mode sexps in the data for a print directive to ZK output form.

(defun zk-output-directive (d)
  (let ((fn (get-output (car d))))
    (if fn (funcall fn d) d)))

;;; Convert Lisp mode variable names, to ZK output form. The argument may be a
;;; single name or a list.

(defun zk-output-variables (formula)
  (cond ((atom formula)
	 (if (variable-p formula)
	     (genname (substring formula 1))
	     formula))
	(t (mapcar #'zk-output-variables formula))))

;;; Output translation functions for printer directives; functions are required
;;; only for directives that might have data to be translated (formulas,
;;; events, commands, and command names).

(defpropfun (:formula zk-output) (d)
  `(:formula ,(zk-output-expr (second d))))

(defpropfun (:formula-list zk-output) (d)
  `(:formula-list ,(mapcar #'zk-output-expr (second d))))

(defpropfun (:event-name zk-output) (d)
  `(:event-name ,(zk-output-variables (second d))))

(defpropfun (:event-name-list zk-output) (d)
  `(:event-name-list ,(zk-output-variables (second d))))

(defpropfun (:event zk-output) (d)
  `(:event ,(zk-output-sexp (second d))))

(defpropfun (:command zk-output) (d)
  `(:command ,(zk-output-sexp (second d))))

(defpropfun (:command-list zk-output) (d)
  `(:command-list ,(mapcar #'zk-output-sexp (second d))))

(defpropfun (:command-name zk-output) (d)
  `(:command-name ,(zk-output-command-name (second d))))

(defpropfun (:command-name-list zk-output) (d)
  `(:command-name-list ,(mapcar #'zk-output-command-name (second d))))

;;; Output translation functions for Lisp mode events and commands; only those
;;; commands that require special treatment, or that have arguments which are
;;; lists of symbols need translation functions.

(defpropfun (axiom zk-output) (axiom)
  `(axiom ,(second axiom) ,(zk-output-variables (third axiom))
	  ,(zk-output-expr (fourth axiom))))

(defpropfun (rule zk-output) (rule)
  `(rule ,(second rule) ,(zk-output-variables (third rule))
	  ,(zk-output-expr (fourth rule))))

(defpropfun (frule zk-output) (frule)
  `(frule ,(second frule) ,(zk-output-variables (third frule))
	  ,(zk-output-expr (fourth frule))))

(defpropfun (grule zk-output) (grule)
  `(grule ,(second grule) ,(zk-output-variables (third grule))
	  ,(zk-output-expr (fourth grule))))

(defpropfun (ufunction zk-output) (uf)
  `(function ,(second uf) ,(zk-output-variables (third uf))
	     ,(if (fourth uf) `((measure ,(zk-output-expr (fourth uf)))) nil)
	 ,(zk-output-expr (fifth uf))))

(defpropfun (function-stub zk-output) (stub)
  `(function-stub ,(second stub) ,(zk-output-variables (third stub))))

(defpropfun (zf-function zk-output) (zf)
  `(zf-function ,(second zf) ,(zk-output-variables (third zf))
		,(fourth zf)))

(defpropfun (instantiate zk-output) (cmd)
  (cond
   ((consp (car (second cmd)))		; Lisp mode syntax
    `(instantiate . ,(zk-output-instantiations (mapcar #'cdr (second cmd)))))
   (t					; ZK syntax
    `(instantiate . ,(zk-output-instantiations (cdr cmd))))))

(defpropfun ((assume use) zk-output) (cmd)
  (cond
   ((null (third cmd))
    `(use ,(second cmd)))
   ((consp (car (third cmd)))		; Lisp mode syntax
    `(use ,(second cmd) .
	  ,(zk-output-instantiations (mapcar #'cdr (third cmd)))))
   (t					; ZK syntax
    `(use ,(second cmd) . ,(zk-output-instantiations (cddr cmd))))))

(defun zk-output-instantiations (instantiations)
  (mapcar #'(lambda (x)
	      (list (zk-output-variables (first x))
		    (zk-output-expr (second x))))
	  instantiations))

(defpropfun ((with-enabled with-disabled) zk-output) (cmd)
  `(,(first cmd) ,(zk-output-variables (second cmd)) .
		 ,(mapcar #'zk-output-sexp (cddr cmd))))

(defpropfun (with-subexpression zk-output) (cmd)
  `(with-subexpression ,(zk-output-expr (second cmd)) .
		       ,(mapcar #'zk-output-sexp (cddr cmd))))


;;; The add functions for events.
;;; They now must do some input conversions (and log them!!!)

(defun add-tag (tn)
  (tag tn))

(defun add-axiom (fn args expr)
  (let ((*proof-log* nil))
    (when (axiom fn (mapcar #'zk-internal-variables args)
                (zk-internal-form expr (index-args args)))
      (setf (event-details (get-event fn)) *proof-log*)
      fn)))

(defun add-rule (rn args expr)
  (let ((*proof-log* nil))
    (when (rule rn (mapcar #'zk-internal-variables args)
                (zk-internal-form expr (index-args args)))
      (setf (event-details (get-event rn)) *proof-log*)
      (setf (rule-internal-details (get-event rn))
            (append (rule-internal-details (get-event rn)) *proof-log*))
      rn)))

(defun add-frule (fn args expr)
  (let ((*proof-log* nil))
    (when (frule fn (mapcar #'zk-internal-variables args)
                 (zk-internal-form expr (index-args args)))
      (setf (event-details (get-event fn)) *proof-log*)
      (setf (frule-internal-details (get-event fn))
            (append (frule-internal-details (get-event fn)) *proof-log*))
      fn)))

(defun add-grule (gn args expr)
  (let ((*proof-log* nil))
    (when (grule gn (mapcar #'zk-internal-variables args)
                 (zk-internal-form expr (index-args args)))
      (setf (event-details (get-event gn)) *proof-log*)
      (setf (grule-internal-details (get-event gn))
            (append (grule-internal-details (get-event gn)) *proof-log*))
      gn)))

(defun add-ufunction (nn args &optional measure body)
  (let ((*proof-log* nil))
    (when (ufunction nn (mapcar #'zk-internal-variables args)
                (unless (null measure)
                  (without-proof-logging (zk-internal-form measure nil)))
                (unless (null body)
                  (zk-internal-form body (cons 2 (index-args args)))))
      (setf (ufunction-assume-details (get-event nn)) *proof-log*)
      (internal-form (ufunction-body (get-event nn)) (cons 2 (index-args args)))
      (setf (ufunction-body-details (get-event nn)) *proof-log*)
      nn)))

(defun add-function-stub (nn args)
  (when (function-stub nn (mapcar #'zk-internal-variables args))
    nn))

(defun add-zf-function (nn args body)
  (when (zf-function nn (mapcar #'zk-internal-variables args) body)
    nn))


;;; ========================= Command Modifiers =========================


;;; Function that returns the command with its modifiers stripped off.

(defun strip-modifiers (cmd)
  (cond ((or (atom cmd) (not (get-modifier (car cmd)))) cmd)
	(t (strip-modifiers (car (last cmd))))))

;;; Define the modifiers.  Macros for the modifiers are defined
;;; in ``header.lisp''.

;;; Proof Step Modifiers

(defpropfun (with-subexpression zk-modifier) (expr cmd)
  (with-subexpression-function expr cmd))

(defun with-subexpression-function (expr cmd)
  (with-subexpression ((without-proof-logging (zk-internal-form expr nil)))
    (zk-to-lisp-aux cmd)))


(defpropfun (with-disabled zk-modifier) (events cmd)
  (with-disabled-function events cmd))

(defun with-disabled-function (events cmd)
  (with-disabled (events) (zk-to-lisp-aux cmd)))


(defpropfun (with-enabled zk-modifier) (events cmd)
  (with-enabled-function events cmd))

(defun with-enabled-function (events cmd)
  (with-enabled (events) (zk-to-lisp-aux cmd)))


(defpropfun (with-instantiation zk-modifier) (cmd)
  (with-instantiation-function cmd))

(defun with-instantiation-function (cmd)
  (with-instantiation (zk-to-lisp-aux cmd)))


(defpropfun (without-instantiation zk-modifier) (cmd)
  (without-instantiation-function cmd))

(defun without-instantiation-function (cmd)
  (without-instantiation (zk-to-lisp-aux cmd)))



;;; Proof Step Modifiers - continued

(defpropfun (with-case-analysis zk-modifier) (cmd)
  (with-case-analysis-function cmd))

(defun with-case-analysis-function (cmd)
  (with-case-analysis (zk-to-lisp-aux cmd)))


(defpropfun (without-case-analysis zk-modifier) (cmd)
  (without-case-analysis-function cmd))

(defun without-case-analysis-function (cmd)
  (without-case-analysis (zk-to-lisp-aux cmd)))

(defpropfun (with-normalization zk-modifier) (cmd)
  (with-normalization-function cmd))

(defun with-normalization-function (cmd)
  (with-normalization (zk-to-lisp-aux cmd)))


(defpropfun (without-normalization zk-modifier) (cmd)
  (without-normalization-function cmd))

(defun without-normalization-function (cmd)
  (without-normalization (zk-to-lisp-aux cmd)))


;;; Declaration Modifiers

(defpropfun (disabled zk-modifier) (cmd)
  (disabled-function cmd))

(defun disabled-function (cmd)
  (disabled (zk-to-lisp-aux cmd)))

;;; Functions that manipulate ZK expressions.

(defun zk-rename-quantified-variables (formula clash-list)
  (zk-rename-quantified-variables-aux formula clash-list nil))

(defun zk-rename-quantified-variables-aux (formula clash-list substs)
  (cond ((all-p formula)
         (let ((clashes (intersection-eq (all-vars formula) clash-list))
               (revised-clash-list (union-var-names (all-vars formula)
                                                    clash-list)))
           (cond ((null clashes)
                  (make-all (all-vars formula)
                            (zk-rename-quantified-variables-aux
                             (all-expr formula) revised-clash-list substs)))
                 (t (let ((new-substs
                           (create-renames clashes revised-clash-list)))
                      (make-all (sublis-symbol new-substs (all-vars formula))
                                (zk-rename-quantified-variables-aux
                                 (all-expr formula)
                                 (union-var-names (mapcar #'cdr new-substs)
                                                  revised-clash-list)
                                 (append new-substs substs))))))))
        ((some-p formula)
         (let ((clashes (intersection-eq (some-vars formula) clash-list))
               (revised-clash-list (union-var-names (some-vars formula)
                                                    clash-list)))
           (cond ((null clashes)
                  (make-some (some-vars formula)
                             (zk-rename-quantified-variables-aux
                              (some-expr formula) revised-clash-list substs)))
                 (t (let ((new-substs
                           (create-renames clashes revised-clash-list)))
                      (make-some (sublis-symbol new-substs (some-vars formula))
                                 (zk-rename-quantified-variables-aux
                                  (some-expr formula)
                                  (union-var-names (mapcar #'cdr new-substs)
                                                   revised-clash-list)
                                  (append new-substs substs))))))))
	((integerp formula) formula)
        ((atom formula) (binding-of formula substs))
        (t (cons (car formula)
                 (loop for expr in (cdr formula)
                       collect (zk-rename-quantified-variables-aux
                                expr clash-list substs))))))

(defun union-var-names (vars1 vars2)
  (unique-symbol (append vars1 vars2)))

(defun create-renames (clashes clash-list)
  (cond ((null clashes) nil)
        (t (let* ((oldvar (car clashes))
                  (stripvar (strip-off-extension oldvar))
                  (newvar
                   (loop for i = 0 then (+ i 1)
                         for var = (intern (format nil "~A~A~A"
                                                   stripvar
                                                   *variable-separator-string*
                                                   i)
					   *zk-package*)
                         until (not (member-eq var clash-list)) ;unused?
                         finally (return var))))
             (cons (cons oldvar newvar)
                   (create-renames (cdr clashes) (cons newvar clash-list)))))))

(defun unclash (oldvar clash-list)
  (let ((stripvar (strip-off-extension oldvar)))
    (loop for i = 0 then (+ i 1)
          for var = (intern (format nil "~A~A~A"
                                    stripvar
                                    *variable-separator-string*
                                    i)
			    *zk-package*)
          until (not (member-eq var clash-list)) ;unused?
          finally (return var))))

(defun strip-off-extension (var-name)
  (let ((var-string (string var-name)))
    (let ((index (string-search= "$" var-string t)))
      (cond ((null index) var-name)
            (t (let ((extension (substring var-string (+ index 1))))
                 (cond ((every #'digit-char-p extension)
                        (intern (substring var-string 0 index)
				*zk-package*))
                       (t var-name))))))))

(defun zk-list-of-free-variables (formula)
  (zk-list-of-free-variables-aux formula nil))

(defun zk-list-of-free-variables-aux (formula bound)
  (cond ((all-p formula)
         (zk-list-of-free-variables-aux (all-expr formula)
                                           (append (all-vars formula) bound)))
        ((some-p formula)
         (zk-list-of-free-variables-aux (some-expr formula)
                                           (append (some-vars formula) bound)))
        ((listp formula)
         (mapcan #'(lambda (u)
                     (zk-list-of-free-variables-aux u bound))
                 (cdr formula)))
        ((and (symbolp formula) (not (member-eq formula bound)))
         (cons formula nil))))




;;; Code to fix POs for div, mod, rem and epsilon-induction

(defparameter *names-with-pos-to-be-fixed*
  '(div mod rem epsilon-induction))

(defun zk-fix-pos ()
  (loop for name in *names-with-pos-to-be-fixed*
        do (let* ((event (get-event name))
                  (decl (strip-modifiers (zk-format-event event))))
             (setq decl
                   (list (first decl) (second decl)
                         (mapcar #'zk-variables (third decl))
                         `((measure ,(zk-form
                                      (second (first (fourth decl))))))
                         (zk-form (fifth decl))))
             (setf (event-formula event)
                   (zk-internal-form
                    (fourth (first (generate-proof-obligations decl))) nil)))))

(defun zk-form (formula)
  (zk-variables formula))

(defun zk-variables (formula)
  (cond ((atom formula)
	 (if (symbolp formula)
             (let ((str (string formula)))
               (if (equal (substring
                           str 0 (string-length *variable-prefix-string*))
                          *variable-prefix-string*)
                   (intern (substring str
				      (string-length *variable-prefix-string*))
			   *zk-package*)
                 formula))
           formula))
	(t (cons (car formula)
                 (mapcar #'zk-variables (cdr formula))))))
