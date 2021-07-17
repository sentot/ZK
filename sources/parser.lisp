
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

;;; =================== Event Level Parsing =================

;;; Event level parsing focus on things having to do with internal
;;; mechanisms, while ZK parsing focus on the notation.

;;; ===== Important Note
;;; At the internal level, variable names and function names are in
;;; a single namespace. This is for efficiency reasons. At the
;;; ZK (Verdi) level, variable names are in a separate namespace
;;; from function names. This difference is handled in the ZK to
;;; internal form translation by prepending variable names with
;;; ")" and having ")" to be one of the characters not allowed in
;;; function names.


;;; Global symbols and macros.

;;; Set to the name of event being parsed.
(defvar *parse-event-name* nil)

;;; Set to non-nil by parse-error.
(defvar *parse-error-flag* nil)

;;; Enable/disable parser warnings.
(defvar *print-parser-warnings-flag* t)

;;; Cover macro to wrap around calls to parsing functions.
;;; Returns non-nil if and only if these is no parser error.
(defmacro without-errors ((event-name) &body body)
  `(let ((*parse-error-flag* nil)
	 (*parse-event-name* ,event-name))
     ,@body (not *parse-error-flag*)))

;;; ==================== Printing Error Messages ====================

;;; Function for printing error codes.
(defun print-error-codes ()
  (let ((error-codes nil))
    (dolist (help *help-alists*)
      (when (eq (second help) 'error-code)
	(push (first help) error-codes)))	;collect codes
    (mapc #'(lambda (u) (printer `((:help-name ,u) (:punctuation ":")
				   . ,(funcall (get u 'error) nil))))
	  (sort (unique-symbol error-codes) #'alphalessp))
    nil))

;;; Function for printing parsing error or warning.
;;; It sets the *parse-error-flag* unless it's a warning.
(defun parse-error (error-type object &optional warning)
  (print-error error-type object *parse-event-name* warning)
  (unless warning (setq *parse-error-flag* t))
  nil)
 
;;; ==================== End of Printing Error Messages ====================


;;; ==================== Converting to Internal Form ====================

;;; The internal form of a formula has all logical connectives converted
;;; into IF form, all expandable functions expanded and all quantifications
;;; expanded.

;;; Conversion to internal form does not check for well-formedness.

;;; First phase simply expands function applications and quantifications.
(defun internal-form-phase-1 (formula index)
  (expand-formula formula index))

;;; Second phase expands boolean operations into IF form.
(defun internal-form-phase-2 (formula index)
  (expand-constants (if-form formula index) index))

;;; Combine phase 1 and phase 2.
(defun internal-form (formula index)
  (internal-form-phase-2 (internal-form-phase-1 formula index) index))

;;; Expand constants (function applications with no arguments).
(defun expand-constants (formula index)
  (cond ((atom formula) formula)
        (t (let ((formula (loop for expr in formula
                                for number = 0 then (+ number 1)
                                collect (expand-constants
                                         expr (cons number index)))))
             (cond
              ((symbolp (car formula))
               (let ((event (get-event (car formula))))
                 (cond
                  ((and (ufunction-p event)
                        (null (ufunction-args event))
                        (ufunction-enabled event)
                        (not (event-inaccessible-p event))
                        (not (null (ufunction-internal-body event))))
                   (log-use-axiom index (internal-name (ufunction-name event)))
                   (let ((renamed (conditionally-rename-quantified-variables
                                    (ufunction-body-variables event)
                                    (ufunction-internal-body event)
                                    (cons 2 (if-test-index)))))
                     (log-rewrite
                      (make-if (make-= formula renamed) formula *true*)
                      nil
                      index)
                     (log-unrenames (ufunction-internal-body event) renamed
                                    (cons 2 (if-test-index)))
                     (push-proof-log 'use-axiom (if-test-index)
                                     (internal-name (ufunction-name event)) t)
                     (push-proof-log 'if-true index)
                     renamed))
                  (t formula))))
              (t formula))))))

;;; =============== End of Converting to Internal Form ===============


;;; ==================== Formula Parsing ====================

;;; Formula parsing combines conversion to internal form with
;;; checking for well-formedness.

;;; Phase 1 of formula parsing expands a formula and checks the expanded
;;; formula for well-formedness. If well-formed, the expanded formula is
;;; returned. Otherwise nil is returned.
(defun parse-formula-phase-1 (formula)
  (let ((expanded (internal-form-phase-1 formula nil)))
    (when (without-errors (nil)
	    (formula-check nil
			   (list-of-free-variables expanded)
			   expanded))
      expanded)))

;;; Phase 2 simply performs phase 2 of converting to internal form.
;;; All well-formedness checking is performed in phase 1.
(defun parse-formula-phase-2 (formula)
  (internal-form-phase-2 formula nil))

;;; Combine phase 1 and phase 2.
(defun parse-formula (formula)
  (without-proof-logging
   (parse-formula-phase-2 (parse-formula-phase-1 formula))))

;;; Check a formula in expanded form for well-formedness.
;;; If refp is non-nil then issue warnings for unreferenced variables.
;;; The returned value is (BOOL), (INT) or T.
(defun formula-check (refp variables expanded)
  (formula-check-phase-1 expanded)
  (quantifier-check variables expanded)
  (check-variables refp variables expanded)
  (formula-check-phase-2 expanded))

;;; Phase 1. Check to make sure symbols in variable positions can be
;;; made into variables and symbols in function positions are in fact
;;; declared functions (names).  Symbols in variable positions that
;;; are not already variables are made into variables.
(defun formula-check-phase-1 (expanded)
  (dolist (symbol (unique-symbol (list-of-potential-vars expanded)))
    (when (not (input-variable-p symbol))
      (parse-error 'symbol-declared symbol)))
  (dolist (symbol (unique-symbol (list-of-potential-names expanded)))
    (let ((event (get-event symbol)))
      (when (or (null event)
		(not (or (ufunction-p event)
			 (function-stub-p event)
			 (zf-function-p event))))
	(parse-error 'symbol-undeclared symbol)))))

;;; Phase 2 ensures that arities match. It returns (BOOL) if the
;;; expanded formula is determined to produce values only in (BOOL),
;;; (INT) if the expanded formula is determined to produce values only
;;; in (INT), and T otherwise.
(defun formula-check-phase-2 (expanded)
  (cond ((atom expanded) (type-of-any expanded))
	((or (all-p expanded) (some-p expanded))
	 (cond ((> (length expanded) 3)
		(parse-error 'quantification-syntax expanded))
               (t (formula-check-phase-2 (all-expr expanded))
		  *bool-type*)))
	(t (let ((event (and (symbolp (car expanded))
			     (get-event (car expanded))))
		 (arg-types (mapcar #'formula-check-phase-2 (cdr expanded))))
	     (cond  ((or (null event) (not (function-event-p event)))
		     ;; *** This probably never happens because phase 1
		     ;; already catches the error.
		     (parse-error 'apply-non-function (car expanded))
		     *univ-type*)
		    ((not (= (length arg-types)
			     (length
			      (cond ((ufunction-p event) (ufunction-args event))
				    ((function-stub-p event)
				     (function-stub-args event))
				    (t (zf-function-args event))))))
		     (parse-error 'wrong-number-of-arguments expanded)
		     *univ-type*)
		    (t (or (and (ufunction-p event) (ufunction-type event))
			   (and (function-stub-p event)
				(function-stub-type event))
			   *univ-type*)))))))

(defun list-of-potential-vars (expanded)
  (list-of-potential-vars-aux expanded nil))

(defun list-of-potential-vars-aux (expanded result)
  (cond ((symbolp expanded) (cons expanded result))
	((atom expanded) result)
        ;; Special treatment for all and some
	((all-p expanded)
	 (let ((var (all-var expanded)))
           (list-of-potential-vars-aux
             (all-expr expanded)
             (if (symbolp var) (cons var result) result))))
        ((some-p expanded)
	 (let ((var (some-var expanded)))
           (list-of-potential-vars-aux
             (some-expr expanded)
             (if (symbolp var) (cons var result) result))))
	((atom (car expanded))
	 (list-of-potential-vars-list (cdr expanded) result))
	(t (list-of-potential-vars-aux
	     (car expanded)
	     (list-of-potential-vars-list (cdr expanded) result)))))

(defun list-of-potential-vars-list (expanded-list result)
  (cond ((null expanded-list) result)
	(t (list-of-potential-vars-aux
	     (car expanded-list)
	     (list-of-potential-vars-list (cdr expanded-list) result)))))

(defun list-of-potential-names (expanded)
  (list-of-potential-names-aux expanded nil))

(defun list-of-potential-names-aux (expanded result)
  (cond ((atom expanded) result)
        ;; Special treatment for all and some
        ((all-p expanded)
         (list-of-potential-names-aux (all-expr expanded) result))
        ((some-p expanded)
         (list-of-potential-names-aux (some-expr expanded) result))
	((symbolp (car expanded))
	 (cons (car expanded)
	       (list-of-potential-names-list (cdr expanded) result)))
	((atom (car expanded))
	 (list-of-potential-names-list (cdr expanded) result))
	(t (list-of-potential-names-list expanded result))))

(defun list-of-potential-names-list (expanded-list result)
  (cond ((null expanded-list) result)
	(t (list-of-potential-names-aux
	     (car expanded-list)
	     (list-of-potential-names-list (cdr expanded-list) result)))))


;;; Check for variable capture and non-variables in quantified variable
;;; positions.
(defun quantifier-check (variables expanded)
  (cond ((atom expanded) nil)
	((all-p expanded)
	 (unless (variable-p (all-var expanded))
	   (parse-error 'parameter-not-variable (all-var expanded)))
	 (when (member-eq (all-var expanded) variables)
	   (parse-error 'variable-capture (all-var expanded)))
	 (quantifier-check (cons (all-var expanded) variables)
			   (all-expr expanded)))
	((some-p expanded)
	 (unless (variable-p (some-var expanded))
	   (parse-error 'parameter-not-variable (some-var expanded)))
	 (when (member-eq (some-var expanded) variables)
	   (parse-error 'variable-capture (some-var expanded)))
	 (quantifier-check (cons (some-var expanded) variables)
			   (some-expr expanded)))
	(t (quantifier-check variables (car expanded))
	   (quantifier-check variables (cdr expanded)))))

;;; Check for free variables that are not in arglist.
;;; If refp is non-nil then warn about unreferenced variables.
(defun check-variables (refp arglist expanded)
  (when (or (null arglist) (consp arglist))	;arglist has to be a list
    (let ((variables (list-of-free-variables expanded)))
      (let ((free-vars (remove-if #'(lambda (u) (member-eq u arglist))
				  variables)))
	(unless (null free-vars)
	  (parse-error 'variable-free (unique-symbol free-vars))))
      (when (not (null refp))			;optional warnings
	(let ((unref-vars (remove-if #'(lambda (u)
					 (member-eq u variables))
				     arglist)))
	  (unless (null unref-vars)		;any unreferenced variables?
	    (parse-error 'variables-unused (unique-symbol unref-vars) t)))))))

;;; ==================== End of Formula Parsing ====================


;;; ==================== Event Parsing ====================

;;; Ensure that event-name is an unused legal symbol.
(defun check-event (event-name)
  (update-proof-status)
  (reset-display)
  (cond ((not (symbolp event-name)) (parse-error 'event-not-symbol event-name))
	((get-event event-name) (parse-error 'redeclaration event-name))))

;;; Check arglist to ensure it is a list of variables with no duplicates.
(defun check-arglist (event-name arglist)
  (cond ((not (or (null arglist) (consp arglist)))
	 (parse-error 'parameter-not-list arglist))
	(t (unless (= (length (unique-symbol arglist)) (length arglist))
	     (parse-error 'duplicate-variables arglist))
	   (dolist (arg arglist)
	     (unless (and (neq arg event-name) (input-variable-p arg))
	       (parse-error 'parameter-not-variable arg))))))

;;; ---------- TAGS

;;; Tags are used to reserve symbols and as markers in the event history.
(defcmd tag (event-name)
  ((:string "Adds event-name as a tag event to the database.  Tags are useful
arguments to")
   (:command-name undo-back-to)
   (:string "and")
   (:command-name undo-back-thru)
   (:punctuation ".")
   (:string "A")
   (:command-name tag)
   (:string "command may also be used as a simple way to prevent the use of")
   (:command-argument event-name)
   (:punctuation "."))
  (when (without-errors (event-name) (check-event event-name))
    (funcall (get 'tag 'add)
	     (make-tag :name event-name
		       :kind 'tag
		       :prop nil
		       :formula *true*
		       :proof nil		;an assumption
		       :proven t))		;indicated here
    event-name))

;;; ---------- AXIOMS

;;; Function to create axiom events.
(defun create-axiom (event-name arglist formula kind prove assume)
  (let ((parsed-axiom (parse-axiom event-name arglist formula)))
    (when parsed-axiom
      (setf (axiom-kind parsed-axiom) kind
	    (axiom-proof parsed-axiom) nil
	    (axiom-proven parsed-axiom) assume)
      (funcall (get 'axiom 'add) parsed-axiom)
      (when prove (prove event-name))
      event-name)))

;;; Event-level command to create axiom events.
(defcmd axiom (event-name arglist formula)
  ((:string "Introduces a new axiom to the theorem prover database. The")
   (:command-argument arglist)
   (:string "is a list of
variables which occur free within the formula; these variables are
considered to be universally quantified.  Although the prover
does not force the user to prove an axiom, it does remember whether
or not it has been proven.  The")
   (:command-argument event-name)
   (:string "is displayed, provided
the addition of the axiom succeeded."))
  (create-axiom event-name arglist formula 'axiom nil nil))

;;; Parsing routine to ensure an event-level axiom command is well-formed.
(defun parse-axiom (event-name arglist formula)
  (without-proof-logging
   (let ((expanded (internal-form-phase-1 formula nil)))
     (when (without-errors (event-name)
                           (check-event event-name)
                           (check-arglist event-name arglist)
                           (formula-check t arglist expanded))
       (make-axiom :name event-name
                   :kind 'axiom
                   :args arglist
                   :formula formula
                   :proof nil
                   :proven nil)))))


;;; ---------- RULES

;;; Function to create rule events.
(defun create-rule (event-name arglist formula kind prove assume)
  (let ((parsed-rule (parse-rule event-name arglist formula)))
    (when parsed-rule
      (setf (rule-kind parsed-rule) kind
	    (rule-proof parsed-rule) nil
	    (rule-proven parsed-rule) assume)
      (funcall (get 'rule 'add) parsed-rule)
      (when prove (prove event-name))
      event-name)))

;;; Event-level command to create rule events.
(defcmd rule (event-name arglist formula)
  ((:string "Adds")
   (:command-argument event-name)
   (:string "as a rewrite rule to the prover database.  If any
errors are found in the rule then the event is not added.  The")
   (:command-argument arglist)
   (:string "consists of variables which are universally quantified
over the formula.  Rewrite rules may be applied automatically by
the command")
   (:command-name rewrite)
   (:string "and other commands which are based on")
   (:command-name rewrite)
   (:punctuation "."))
  (create-rule event-name arglist formula 'rule nil nil))

;;; Function to ensure event-level RULE commands are well-formed.
(defun parse-rule (event-name arglist formula)
  (let ((rule (parse-rule-phase-1 event-name arglist formula)))
    (unless (null rule)
      (parse-rule-phase-2 rule))))

;;; Phase 1. Mostly syntactic. Produces a rule struct if successful.
(defun parse-rule-phase-1 (event-name arglist formula)
  (let* ((*proof-log* nil)
         (index (index-args arglist))
         (expanded (internal-form-phase-1 formula index)))
    (when (without-errors (event-name)
	    (check-event event-name)
	    (check-arglist event-name arglist)
	    (formula-check t arglist expanded)
	    (check-rule-conclusion expanded))
      (let ((substitutions
	     ;; Make the order of the variables the same as
	     ;; universal quantification for INTERNAL axiom.
	     (rename-variable-list
	      (unique (if (null (extract-subgoal expanded))
			  (list-of-free-variables expanded)
			(append (list-of-free-variables
				 (=-left (extract-conclusion expanded)))
				(list-of-free-variables expanded))))))
            (subgoal (extract-subgoal expanded))
            (conclusion (extract-conclusion expanded))
            (conclusion-index (if (implies-p expanded) (cons 2 index) index)))
        (unless (null subgoal)
          (setq subgoal (sublis-symbol substitutions
				       (internal-form-phase-2
					subgoal (implies-left-index)))))
        (let* ((orig-pattern (internal-form-phase-2
                              (=-left conclusion) (cons 1 conclusion-index)))
               (pattern (sublis-symbol substitutions orig-pattern))
               (orig-value (internal-form-phase-2
                            (=-right conclusion) (cons 2 conclusion-index)))
               (value (sublis-symbol substitutions orig-value)))
          (when (implies-p expanded)
            (push-proof-log 'syntax index)
	    ;; (if cond (if (= lhs rhs) (TRUE) (FALSE)) (TRUE))
	    ;; Remove (BOOL) coercion on (= lhs rhs).
            (push-proof-log 'is-boolean (if-left-index) t)
            (log-true-to-= orig-pattern (if-right-index))
            (push-proof-log 'case-analysis index 0 t)
            (push-proof-log 'if-equal (=-left-index)))
          (make-rule :name event-name
                     :kind 'rule
                     :args arglist
                     :formula formula
                     :renames substitutions
                     :subgoal subgoal
                     :pattern pattern
                     :value value
                     :internal-details *proof-log*
                     :proof nil
                     :proven nil			;must be proven
                     :enabled (not (cdr (assoc-eq :disabled
                                                  *current-modifiers*)))))))))

(defun check-rule-conclusion (formula)
  (unless (=-p (extract-conclusion formula))
    (parse-error 'rule-invalid-conclusion (extract-conclusion formula))))

;;; Phase 2. More elaboate check. Note that phase 1 already produced a
;;; rule struct.
(defun parse-rule-phase-2 (rule)
  (if (without-errors ((rule-name rule))
	(check-rule-subgoal rule)
	(check-rule-pattern rule)
	(check-rule-variables rule)
	(check-rule-looping rule)
	(check-rule-subgoaling rule))
      (let ((subgoal (if (true-p (rule-subgoal rule)) nil (rule-subgoal rule))))
	(setf (rule-subgoal rule) subgoal
	      (rule-subbound rule)
	      (unique-symbol (list-of-bound-variables subgoal))
	      (rule-valbound rule)
	      (unique-symbol (list-of-bound-variables (rule-value rule)))
	      (rule-conditional rule)
	      (unless (null subgoal)
		;; conditional or conditional with instantitation
		(or (rule-to-be-instantiated-variables
		     subgoal (rule-pattern rule))
		    t))
	      (rule-permutative rule)
	      (permutative-formulas-p (rule-pattern rule)
				      (rule-value rule))
	      ;; fancier indexing scheme in the future?
	      (rule-index rule) (index-of (rule-pattern rule)))
	rule)
      (progn (setf (rule-enabled rule) nil)	;errors turn it off
	     nil)))


;;; Functions to extract the subgoal, pattern and value.

;;; Subgoal is the hypothesis of an implication.
;;; Returns nil if no subgoal.
(defun extract-subgoal (formula)
  (if (implies-p formula) (implies-left formula) nil))

;;; Conclusion is the conclusion of an implication or
;;; the entire formula if not an implication.
(defun extract-conclusion (formula)
  (if (implies-p formula) (implies-right formula) formula))

;;; Given that conclusion is an equality, the pattern is the lhs of
;;; the equality. Should never be called if conclusion is not an equality.
(defun extract-pattern (formula)
  (=-left (extract-conclusion formula)))

;;; Given that conclusion is an equality, the value is the rhs of
;;; the equality. Should never be called if conclusion is not an equality.
(defun extract-value (formula)
  (=-right (extract-conclusion formula)))

;;; Return variables that must be instantiated in subgoals.
(defun rule-to-be-instantiated-variables (subgoal pattern)
  (let ((variables (set-difference-equal
		    (unique-symbol (list-of-free-variables subgoal))
		    (list-of-free-variables pattern))))
    (if (null variables) nil (list variables))))	;list of



;;; Functions for checking the required properties of rules.

;;; Rule with a subgoal of (FALSE) can never be applied.
(defun check-rule-subgoal (rule)
  (when (false-p (rule-subgoal rule))
    (parse-error 'rule-false-condition (rule-name rule))))

;;; Check rule pattern to disallow rewriting of IFs, ALLs and SOMEs.
(defun check-rule-pattern (rule)
  (check-pattern (rule-pattern rule)))

(defun check-pattern (pattern)
  (without-proof-logging
   (cond ((atom pattern)
	  (parse-error 'pattern-not-function-application pattern))
         (t (unless (constant-p (car pattern))
	      ;; *** This probably never happens.
              (parse-error 'pattern-not-function-application
			   (output-form pattern nil)))
            (when (calls-p 'if pattern)
	      ;; Rewriting of IF expressions disallowed.
              (parse-error 'pattern-connective (output-form pattern nil)))
            (when (calls-any-p '(all some) pattern)
	      ;; Rewriting of quantification disallowed.
              (parse-error 'pattern-quantifier (output-form pattern nil)))))))

;;; Each variable in rule-variables must be bound in the conditions or pattern.
(defun check-rule-variables (rule)
  (let* ((bound-vars (append (list-of-free-variables (rule-subgoal rule))
			     (list-of-free-variables (rule-pattern rule))))
	 (unbound-vars (unique-symbol (remove-if #'(lambda (u)
                                              (member-eq u bound-vars))
					  (list-of-free-variables
                                           (rule-value rule))))))
    (when unbound-vars (parse-error 'variable-unbound
                                    (without-proof-logging
                                     (mapcar #'(lambda (u) (output-form u nil))
                                             unbound-vars))))))


;;; Parse time rule looping checks.

(defvar *check-all-rules-flag* nil)

;;; Check if rule loops (RHS matches LHS) to prevent infinite looping.
(defun check-rule-looping (rule)
  ;; Permutative rules are allowed (lrpo> check is used bdefore
  ;; application to prevent infinite looping).
  (unless (permutative-formulas-p (rule-pattern rule) (rule-value rule))
    ;; Simple check.
    (multiple-value-bind
     (substitutions success)
     (match-pattern-subformula (rule-pattern rule) (rule-value rule))
     substitutions
     (cond (success
	    ;; Looping. If rule is conditional then just issue a WARNING.
	    ;; Otherwise it is a hard ERROR.
	    (parse-error 'rule-loops (rule-name rule) (rule-subgoal rule)))
	   (*check-all-rules-flag*
	    ;; A more thorough looping check.
	    (reset-deductive-database)
	    (with-egraph-protected
	     (every #'assume-true (list-of-conjuncts (rule-subgoal rule)))
	     (multiple-value-bind
	      (substitutions success)
	      (match-pattern-subformula
	       (rule-pattern rule)
	       (reduce-formula-in-context (rule-value rule) nil))
	      substitutions
	      (when success
		;; Conditional -> WARNING, unconditional -> ERROR.
		(parse-error 'rule-loops (rule-name rule)
			     (rule-subgoal rule))))))))))

;;; Check if rule can apply to subgoal.
(defun check-rule-subgoaling (rule)
  (when (rule-subgoal rule)			;only if there are some
    (let ((conjuncts-of-condition (list-of-conjuncts (rule-subgoal rule))))
      ;; first do the simple self subgoal check
      (cond ((some #'(lambda (u) (multiple-value-bind (substitutions success)
						      (match-pattern-subformula
						       (rule-pattern rule) u)
				   substitutions
				   success))
		   conjuncts-of-condition)
	     ;; Only a WARNING here.
	     (parse-error 'rule-condition-loops (rule-name rule) t))
	    ;; A more thorough check.
	    ((and *check-all-rules-flag*
		  (progn (reset-deductive-database)
			 (with-egraph-protected
			  (some #'(lambda (u)
				    (multiple-value-bind
				     (substitutions success)
				     (match-pattern-subformula
				      (rule-pattern rule)
				      (reduce-formula-in-context
				       u nil)) ;*****
				     (assume-true u)	;assume for next proof
				     substitutions
				     success))
				;; just the simple check after a
				;; prove with assumptions
				conjuncts-of-condition))))
	     (parse-error 'rule-condition-loops (rule-name rule) t))))))

;;; Ensure rule is reducing according to lrpo>.
(defun check-rule-reducing (rule)
  (let ((vars (mapcar #'cdr (rule-renames rule)))
	(left (rule-pattern rule))
	(right (rule-value rule)))
    (unless (lrpo> left right vars)
      (parse-error 'rule-not-reducing (rule-name rule) t))))


;;; ---------- FRULES

;;; Function to create frule events.
(defun create-frule (event-name arglist formula kind prove assume)
  (let ((parsed-frule (parse-frule event-name arglist formula)))
    (when parsed-frule
      (setf (frule-kind parsed-frule) kind
	    (frule-proof parsed-frule) nil
	    (frule-proven parsed-frule) assume)
      (funcall (get 'frule 'add) parsed-frule)
      (when prove (prove event-name))
      event-name)))

;;; Event-level command to create frule events.
(defcmd frule (event-name arglist formula)
  ((:string "Adds")
   (:command-argument event-name)
   (:string "as a forward rule to the prover database.  The")
   (:command-argument arglist)
   (:string "consists of variables which are universally quantified
over the")
   (:command-argument formula)
   (:punctuation ".")
   (:string "Forward rules are applied automatically by
the")
   (:command-name simplify)
   (:string "command and other commands which are based on")
   (:command-name simplify)
   (:punctuation "."))
  (create-frule event-name arglist formula 'frule nil nil))


;;; Function to ensure event-level frule command is well-formed.
(defun parse-frule (event-name arglist formula)
   (let* ((*proof-log* nil)
          (expanded (without-proof-logging
                     (internal-form-phase-1 formula nil)))
          (subgoal (extract-subgoal formula))
          (value (extract-conclusion formula))
          (index (index-args arglist)))
     (when (without-errors (event-name)
                           (check-event event-name)
                           (check-arglist event-name arglist)
                           (formula-check t arglist expanded)
                           (check-frule-subgoal subgoal)
                           (check-frule-value value)
                           (check-frule-variables subgoal value))
       (let ((pattern
              (if (not-p subgoal)
                  (internal-form (not-expr subgoal) (list* 1 1 index))
                (internal-form subgoal (implies-left-index))))
	     ;; Make the order of the variables the same as
	     ;; universal quantification for INTERNAL axiom.
             (substitutions
	      (rename-variable-list
	       (unique (list-of-free-variables expanded))))
             (signed-conjuncts
              (list-of-signed-conjuncts
               (really-flatten-ands value (implies-right-index)))))
         (setq signed-conjuncts
               (loop for entry in signed-conjuncts
                     for i = 1 then (+ i 1)
                     collect (cons (sublis-symbol
                                    substitutions
                                    (internal-form
                                     (car entry)
                                     (if (= (length signed-conjuncts) 1)
                                         (implies-right-index)
                                       (cons i (implies-right-index)))))
                                   (cdr entry))))
         (when *record-proof-logs-flag*
           (push-proof-log 'syntax index)
           (when (not-p subgoal)
	     (push-proof-log 'syntax (if-test-index)))
           ;; (IF cond (IF concl (TRUE) (FALSE)) (TRUE))
           (log-convert-signed-conjunction
	    (mapcar #'car signed-conjuncts)
            (mapcar #'cdr signed-conjuncts) (cons 1 (if-left-index)))
           (cond ((= (length signed-conjuncts) 1)
                  ;; (IF cond (IF concl (TRUE) (FALSE)) (TRUE))
                  (when (cdr (car signed-conjuncts))
                    (push-proof-log 'case-analysis (if-left-index) 1)
                    (push-proof-log 'if-false (cons 2 (if-left-index)))
                    (push-proof-log 'if-true (cons 3 (if-left-index)))))
                 (t
                  ;; (IF cond (IF conjuncts (TRUE) (FALSE)) (TRUE))
                  (log-remove-bool-coercion-from-conjuncts
                   signed-conjuncts (if-left-index)))))
         (make-frule :name event-name
                     :kind 'frule
                     :args arglist
                     :formula formula
                     :renames substitutions
                     :pattern (sublis-symbol substitutions pattern)
                     :values signed-conjuncts
                     :internal-details *proof-log*
                     :negate (not-p subgoal)
                     :index (index-of pattern)
                     :proof nil
                     :proven nil        ;must be proven
                     :enabled (not (cdr (assoc-eq :disabled
                                                  *current-modifiers*))))))))


;;; Check the frule subgoal, which is to become the frule pattern.
(defun check-frule-subgoal (subgoal)
  (unless (null subgoal)
    (let ((pattern (without-proof-logging
                    (internal-form
                     (if (not-p subgoal) (not-expr subgoal) subgoal)
                     nil))))
      (check-pattern pattern))))

;;; The frule variables must be bound in the pattern.
(defun check-frule-variables (subgoal value)
  (let ((unbound (set-difference-equal
                  (list-of-free-variables-unexpanded value)
                  (list-of-free-variables-unexpanded subgoal))))
    (when unbound (parse-error 'variable-unbound unbound))))

;;; The frule conclusion becomes a list of conjuncts.
;;; Make sure each conjunct contains no quantifiers, IFs,
;;; and boolean connectives.
(defun check-frule-value (value)
  (without-proof-logging
   (when (some #'(lambda (u) (calls-any-p '(all some) ; if)
                                          (internal-form (car u) nil)))
               (list-of-signed-conjuncts
                (unexpand-formula value nil)))
     (parse-error 'frule-invalid-conclusion value))))



;;; Code to convert a conjunction into a list of conjunct - sign pairs.
(defun list-of-signed-conjuncts (formula)
  (if (and-p formula)
      (mapcar #'(lambda (u)
		  (if (not-p u) (cons (not-expr u) t) (cons u nil)))
	      (cdr formula))
      (if (not-p formula)
	  (list (cons (not-expr formula) t))
	  (list (cons formula nil)))))


;;; ---------- GRULES

;;; Function to create grule events.
(defun create-grule (event-name arglist formula kind prove assume)
  (let ((parsed-grule (parse-grule event-name arglist formula)))
    (when parsed-grule
      (setf (grule-kind parsed-grule) kind
	    (grule-proof parsed-grule) nil
	    (grule-proven parsed-grule) assume)
      (funcall (get 'grule 'add) parsed-grule)
      (when prove (prove event-name))
      event-name)))

;;; Event-level command to create grule events.
(defcmd grule (event-name arglist formula)
  ((:string "Adds")
   (:command-argument event-name)
   (:string "as an assumption rule to the prover database.  The")
   (:command-argument arglist)
   (:string "consists of variables which are universally quantified
over the")
   (:command-argument formula)
   (:punctuation ".")
   (:string "Assumption rules are applied automatically by
the")
   (:command-name simplify)
   (:string "command and other commands which are based on")
   (:command-name simplify)
   (:punctuation "."))
  (create-grule event-name arglist formula 'grule nil nil))



;;; Function to ensure event-level grule command is well-formed.
(defun parse-grule (event-name arglist formula)
  (let* ((*proof-log* nil)
         (expanded (without-proof-logging (internal-form-phase-1 formula nil)))
	 ;; Make the order of the variables the same as
	 ;; universal quantification for INTERNAL axiom.
         (substitutions
	  (rename-variable-list
	       (unique (list-of-free-variables expanded))))
         (index (index-args arglist))
         (subgoal (extract-subgoal formula))
         (subgoal-index (if (null subgoal) index (implies-left-index)))
         (value (extract-conclusion formula))
         (value-index (if (null subgoal) index (implies-right-index)))
         (assumption (if (not-p value) (not-expr value) value))
         (assumption-index (if (not-p value) (cons 1 value-index) value-index))
         (internal-assumption (internal-form assumption assumption-index)))
     (when (without-errors (event-name)
                           (check-event event-name)
                           (check-arglist event-name arglist)
                           (formula-check t arglist expanded)
                           (check-grule-subgoal subgoal)
                           (check-grule-assumption internal-assumption))
       (when (without-errors (event-name)
                             (check-grule-variables
                              subgoal (extract-grule-pattern value) formula))
         (let* ((pattern (extract-grule-pattern internal-assumption))
                (subgoals (make-list-of-subgoals
                           (sublis-symbol substitutions subgoal)
                           (sublis-symbol substitutions pattern)
                           subgoal-index)))
           (unless (or (null subgoals)
                       (null *record-proof-logs-flag*))
             (push-proof-log 'syntax index)
             (log-convert-signed-conjunction
	      (mapcar #'car subgoals)
              (mapcar #'second subgoals) (if-test-index)))
           (when (and *record-proof-logs-flag* (not-p value))
             (cond ((null subgoals)
		    (push-proof-log 'syntax index))
                   (t
                    ;; (if condition (if (not expr) (true) (false)) (true))
		    (push-proof-log 'syntax (cons 1 (if-left-index)))
                    (push-proof-log 'case-analysis (if-left-index) 1)
                    (push-proof-log 'if-false (cons 2 (if-left-index)))
                    (push-proof-log 'if-true (cons 3 (if-left-index))))))
           (make-grule :name event-name
                       :kind 'grule
                       :args arglist
                       :formula formula
                       :renames substitutions
                       :subgoals subgoals
                       :pattern (sublis-symbol substitutions pattern)
                       :value (cons (sublis-symbol substitutions
						   internal-assumption)
                                    (not-p value))
                       :index (index-of pattern)
                       :internal-details *proof-log*
                       :proof nil
                       :proven nil      ;must be proven
                       :enabled (not (cdr (assoc-eq
                                           :disabled
                                           *current-modifiers*)))))))))


;;; This is an inefficient conversion since it is of the order of
;;; the square of the number of conjuncts. Probably doesn't matter
;;; since number of conjuncts is small.
(defun log-convert-signed-conjunction (conjuncts signs index)
  (cond ((= (length signs) 1)
         (unless (null (first signs))
	   (push-proof-log 'syntax index)))
        ((> (length signs) 2)
         (push-proof-log 'syntax index)
         ;; (and s1 (and s2 ... sn))
         (unless (null (first signs))
	   (push-proof-log 'syntax (and-left-index)))
         (log-convert-signed-conjunction
	  (cdr conjuncts) (cdr signs) (and-right-index))
         (push-proof-log 'syntax index)
         ;; (if s1 (if rest (true) (false)) (false))
         (log-remove-bool-coercion-from-conjuncts
          (cdr signs) (if-left-index)))
        (t
         (unless (null (first signs))
	   (push-proof-log 'syntax (and-left-index)))
         (unless (null (second signs))
	   (push-proof-log 'syntax (and-right-index)))
         (push-proof-log 'syntax index))))

(defun log-remove-bool-coercion-from-conjuncts (signs index)
  (cond ((null signs)
         ;; (if (true) (true) (false))
         (push-proof-log 'if-true index))
        (t
         ;; (if (if a ... (false)) (true) (false))
         (push-proof-log 'case-analysis index 1)
         ;; (if a (if ... (true) (false)) (if (false) (true) (false)))
         (push-proof-log 'if-false (if-right-index))
         (log-remove-bool-coercion-from-conjuncts
          (cdr signs) (if-left-index)))))


;;; A simple pattern is a function application with zero or more
;;; unique variables as its arguments.
(defun simple-pattern-p (pattern)
  (and (not (atom pattern))
       (every #'variable-p (cdr pattern))
       (equal (unique-symbol (cdr pattern)) (cdr pattern))))

;;; Extract pattern gets the first simple pattern from an expression
;;; when scanned from left to right.
(defun extract-grule-pattern (value)
  (cond ((atom value) nil)
	((simple-pattern-p value) value)
	(t (some #'extract-grule-pattern value))))

;;; Converts a conjunction into a list of triples (atomic-formula - sense
;;; - variables)
;;; Each triple represents a subgoal with the sense indicating whether the
;;; formula is to be affirmed or refuted, and the variables are those that may
;;; be instantiated.
(defun make-list-of-subgoals (subgoal pattern index)
  (unless (null subgoal)
    (let ((signed-subgoals (list-of-signed-conjuncts
                            (really-flatten-ands subgoal index)))
	  (vars (set-difference-eq
		  (unique-symbol (list-of-free-variables-unexpanded subgoal))
		  (unique-symbol (list-of-free-variables pattern)))))
      (cond ((and-p subgoal)
             (loop for u in signed-subgoals
                   for i = 1 then (+ i 1)
                   collect (prog1 (list (internal-form (car u)
                                                       (if (cdr u)
                                                           (list* 1 i index)
                                                         (cons i index)))
                                        (cdr u)
                                        (intersection-eq
                                         vars
                                         (unique-symbol (list-of-free-variables
                                                  (car u)))))
                             (setq vars
                                   (set-difference-eq
                                    vars
                                    (intersection-eq
                                     vars
                                     (unique-symbol
                                      (list-of-free-variables (car u)))))))))
            ;; special case if subgoal is not a conjunction
            (t
             (list (list (internal-form (caar signed-subgoals)
                                        (if (cdar signed-subgoals)
                                            (cons 1 index)
                                          index))
                         (cdar signed-subgoals)
                         (intersection-eq
                          vars (unique-symbol (list-of-free-variables
                                        (caar signed-subgoals)))))))))))


;;; Functions for checking the required properties of grules.

;;; Subgoal must be one of a restricted form.
(defun check-grule-subgoal (subgoal)
  (cond ((null subgoal) t)
	((false-p subgoal) (parse-error 'grule-false-condition subgoal))
	(t (without-proof-logging
            (let ((subgoals (list-of-signed-conjuncts
                             (really-flatten-ands subgoal nil))))
              (dolist (s subgoals)
                (let ((pattern (internal-form (car s) nil)))
                  (cond ((atom pattern)		; **** allow atomic subgoals?
                         (unless (constant-p pattern)
                           (parse-error 'grule-invalid-condition pattern)))
                        (t (unless (and (constant-p (car pattern))
                                        (not (calls-any-p '(if all some)
                                                          pattern)))
                             (parse-error 'grule-invalid-condition
                                          (output-form pattern nil))))))))))))

(defun check-grule-assumption (internal-assumption)
  (unless (and (extract-grule-pattern internal-assumption)
	       (not (calls-any-p '(all some if) internal-assumption)))
    (parse-error 'grule-invalid-conclusion internal-assumption)))

;;; a grules variables must be bound in the conditions or pattern
(defun check-grule-variables (subgoal pattern formula)
  (let ((unbound (set-difference-equal
		   (set-difference-equal
		     (list-of-free-variables-unexpanded formula)
		     (list-of-free-variables pattern))
		   (list-of-free-variables-unexpanded subgoal))))
    (when unbound (parse-error 'variable-unbound unbound))))


;;; ---------- FUNCTIONS

(defcmd function-stub (event-name arglist)
  ((:string "Adds a function symbol without a definition to the
theorem prover.  For a function without the user must supply the")
   (:command-argument event-name)
   (:string "and")
   (:command-argument arglist)
   (:punctuation "."))
  (create-function-stub event-name arglist))
  
(defun create-function-stub (event-name arglist)
  (when (without-errors (event-name)
	  (check-event event-name)
	  (check-arglist event-name arglist))
    (funcall (get 'function-stub 'add)
	     (make-function-stub :name event-name
				 :kind 'function-stub
				 :args arglist
				 :formula *true*))
    event-name))

(defcmd zf-function (event-name arglist body)
  ((:string "Adds a zf-function symbol without a definition to the
theorem prover. The user must supply the")
   (:command-argument event-name)
   (:punctuation ",")
   (:command-argument arglist)
   (:string "and")
   (:command-argument body)
   (:punctuation "."))
  (create-zf-function event-name arglist body))
  
(defun create-zf-function (event-name arglist body)
  (when (without-errors (event-name)
	  (check-event event-name)
	  (check-arglist event-name arglist))
    (funcall (get 'zf-function 'add)
	     (make-zf-function :name event-name
			       :kind 'zf-function
			       :args arglist
			       :body body
			       :formula *true*))
    event-name))

  
;;; Name events are used to represent FUNCTION-STUBs, FUNCTIONs
;;; and ZF-FUNCTIONS.

;;; Function to create name events.
(defun create-ufunction (event-name args measure body kind prove assume)
      (defined-function event-name args measure body kind
        prove assume))

;;; Event-level command to create name events.
(defcmd ufunction (event-name arglist &optional measure body)
  ((:string "Adds a function symbol with or without a definition to the
theorem prover.  For a function without a definition, the user
must supply the")
   (:command-argument event-name)
   (:punctuation ",")
   (:command-argument arglist)
   (:string "and")
   (:command-argument return-type)
   (:punctuation ".")
   (:string "The signature
of the function is a mapping from the argument types to the
return type.  To introduce a function with a definition, the user
need only add the")
   (:command-argument body)
   (:punctuation ".")
   (:string "The")
   (:command-argument measure)
   (:string "is an
expression of type")
   (:event-name ordinal)
   (:string "used for recursive functions.  If
the")
   (:command-argument pre)
   (:string "is omitted then it is equivalent to specifying
the pre as")
   (:event-name true)
   (:punctuation ".")
   (:string "Functions with definitions may be invoked by")
   (:command-name invoke)
   (:string "and")
   (:command-name reduce)
   (:punctuation ",")
   (:string "and commands which are based on them."))
  (create-ufunction event-name arglist measure body 'ufunction nil nil))


;;; The functions for the declaration of prover functions.
;;; They install the definition in the namebase after doing some checking.

;;; Function to create ufunction events. The events are used to
;;; represent FUNCTIONs and can be recursive, in which case it requires
;;; a MEASURE.
(defun defined-function
    (event-name arglist measure body kind prove assume)
  (let ((parsed-name (parse-ufunction event-name arglist nil measure body)))
    (when parsed-name
      (setf (ufunction-kind parsed-name) kind
	    (ufunction-proof parsed-name) nil
	    (ufunction-proven parsed-name)
	    (or (ufunction-proven parsed-name) assume))
      (funcall (get 'ufunction 'add) parsed-name)
      (when (eq (ufunction-type parsed-name) *univ-type*)
	(setf (ufunction-type parsed-name) (type-of-body parsed-name body)))
      (when prove (prove event-name))
      event-name)))

;;; Function to ensure event-level ufunction commands are well-formed.
(defun parse-ufunction (event-name arglist return-type measure body)
  (without-proof-logging
   (let ((name (parse-ufunction-phase-1
                event-name arglist return-type measure body)))
     (unless (or (null name) (null (parse-ufunction-phase-2 name)))
       name))))

;;; Phase 1. Mostly syntactic checks. When successful returns a
;;; name struct.
(defun parse-ufunction-phase-1 (event-name arglist return-type measure body)
  (let ((expanded-measure (internal-form-phase-1 measure nil))
	(expanded-body (internal-form-phase-1 body nil)))
    (when (without-errors (event-name)
	    (check-event event-name)
	    (check-arglist event-name arglist)
	    (check-name-measure event-name arglist measure
				expanded-measure expanded-body)
	    (when (null (get-event nil))	;only in initial database
	      (check-name-body event-name arglist expanded-body)))
      (make-ufunction
       :name event-name
       :kind 'name
       :args arglist
       :type (cond ((null return-type) *univ-type*)
		   (t return-type))
       :measure measure
       :body body
       :internal-measure (internal-form-phase-2 expanded-measure nil)
       :internal-body (internal-form-phase-2 expanded-body nil)
       :formula *false*
       :proof nil
       :proven nil
       :enabled (not (cdr (assoc-eq :disabled *current-modifiers*)))))))

;;; Check the supplied measure.
(defun check-name-measure
    (event-name arglist measure expanded-measure expanded-body)
  (cond ((null measure)
	 (when (calls-p event-name expanded-body)
	   (parse-error 'no-measure event-name)))
	(t (formula-check nil arglist expanded-measure))))



;;; Phase 2. A more thorough analysis mainly for recursive functions
;;; and/or computability.
(defun parse-ufunction-phase-2 (name)
  (let* ((machine (machine-of-formula (ufunction-name name)
				      (ufunction-body name)))
	 (calls (unique-symbol (list-of-applied-functions
				(ufunction-internal-body name))))
	 (recursive (if (member-eq (ufunction-name name) calls) t nil)))
    (setf (ufunction-unchangeables name)
	  (unchangeables-for-function (ufunction-name name)
				      (ufunction-args name)
				      (ufunction-internal-body name))
	  (ufunction-measured-subset name)
	  (mapcar #'(lambda (u)
		      (if (occurs-in u (ufunction-measure name))
			  t
			nil))
		  (ufunction-args name))
	  (ufunction-body-variables name)
	  (unique-symbol (list-of-bound-variables
			  (ufunction-internal-body name)))
	  (ufunction-machine name) machine
	  (ufunction-recursive name) recursive
	  (ufunction-computable name)
	  (every #'(lambda (u)
		     (or (eq u (ufunction-name name))
			 (let ((event (get-event u)))
			   (or (and (ufunction-p event)
				    (ufunction-computable event))
			       (and (function-stub-p event)
				    (function-stub-computable event))))))
		 calls))
    name))

;;; Functions for finding unchangeable arguments for recursive functions.
(defun unchangeables-for-function (function arguments formula)
  (unchangeables-in-arguments
   arguments (mapcar #'cdr (list-of-calls function formula))))

(defun unchangeables-in-arguments (args args-list)
  (unchangeables-in-arguments-aux args
				  args-list
				  (make-list (length args) :initial-element t)))

(defun unchangeables-in-arguments-aux (args args-list result)
  (if (null args-list)
      result
    (unchangeables-in-arguments-aux
     args (cdr args-list)
     (mapcar #'(lambda (u v w) (and u (equal v w)))
	     result args (car args-list)))))



;;; Functions for finding the Boyer-Moore style induction machine of a
;;; recursive function.
(defun machine-of-formula (function formula)
  (machine-recursively
   function
   (rename-quantified-variables (expand-formula formula nil) nil)
   nil))

(defun machine-recursively (function formula assumptions)
  (cond ((calls-p function formula)
         (cond ((if-p formula)
                (if (calls-p function (if-test formula))
                    (let ((hypothesis (machine-recursively-aux function
                                                               formula)))
                      `((,(reverse assumptions)
                         ,hypothesis)))
                  (append (machine-recursively function
                                               (if-left formula)
                                               (cons (if-test formula)
                                                     assumptions))
                          (machine-recursively function
                                               (if-right formula)
                                               (cons (without-proof-logging
                                                      (negate (if-test formula)
                                                              nil
                                                              nil))
                                                     assumptions)))))
               (t
                (let ((hypothesis (machine-recursively-aux function formula)))
                  `((,(reverse assumptions)
                     ,hypothesis))))))
        (t (list (list (reverse assumptions) nil nil)))))

(defun machine-recursively-aux (function formula)
  (cond ((atom formula) *true*)
	((if-p formula)
	 (make-simplified-and
	   (machine-recursively-aux function (if-test formula))
	   (make-simplified-if (if-test formula)
			       (machine-recursively-aux function
                                                        (if-left formula))
			       (machine-recursively-aux function
                                                        (if-right formula)))))
	((or (all-p formula) (some-p formula))
         (let ((unquant (machine-recursively-aux function (all-expr formula))))
           (if (true-p unquant)
               *true*
             (make-series-of-quantification
              'all (all-vars formula) unquant))))
	((eq (car formula) function)
         (make-conjunction
          (cons (list* *induction-pattern* (cdr formula))
                (remove-if #'true-p
                           (mapcar #'(lambda (u)
                                       (machine-recursively-aux function u))
                                   (cdr formula))))))
	(t (make-conjunction
	     (remove-if #'true-p
			(mapcar #'(lambda (u)
                                    (machine-recursively-aux function u))
				(cdr formula)))))))

;;; Check the given expanded body of a name.
(defun check-name-body (event-name arglist expanded-body)
  (when (and (symbolp event-name)
	     (null (get-event event-name))	;no name clash
	     (or (null arglist) (consp arglist))
	     (every #'symbolp arglist))		;args must be symbols
    (let ((name (make-ufunction :name event-name :args arglist
			   :type *univ-type*)))
      (unwind-protect
	  ;; Temporarily add the name to avoid an undeclared error
	  ;; for recursive functions.
	  (progn (funcall (get 'ufunction 'add) name)
		 (formula-check nil arglist expanded-body))
	(funcall (get 'ufunction 'del) name)))))

;;; Function to discover type prescription.
(defun type-of-body (event body)
  (cond ((if-p body)
         (let ((left-type (type-of-body event (if-left body)))
               (right-type (type-of-body event (if-right body))))
           (cond ((equal left-type right-type) left-type)
                 ((null left-type) right-type)
                 ((null right-type) left-type)
                 (t *univ-type*))))
	((or (all-p body) (some-p body)) *bool-type*)
        ((consp body)
         (cond ((eq (car body) (ufunction-name event)) nil) ; deferred
               ((get-event (car body))
		(let ((ev (get-event (car body))))
		  (cond ((ufunction-p ev) (ufunction-type ev))
			((function-stub-p ev) (function-stub-type ev))
			(t *univ-type*))))
               (t *univ-type*)))
        ((integerp body) *int-type*)
        (t *univ-type*)))

;;; This is only called when generating log files via dump-log
;;; (implemented in the file generate-log.lisp).
(defun log-type-prescription (event)
  ;; Start with (all ... (= (type-of (f ...)) type) ... )
  (let ((index (index-args (ufunction-args event)))
	(name (ufunction-name event))
        (axiom (definition-name (ufunction-name event)))
        (args (ufunction-args event))
        (type (ufunction-type event)))
    (cond ((and (ufunction-recursive event)
		(equal (type-of-any (ufunction-body event)) *univ-type*))
	   ;; Need induction
           (update-proof-status)
           (reset-display) ; needed to enable getting induction template
           (let* ((formula `(= (type-of ,(cons name args)) ,type))
		  (term (cons name args))
		  (template (third (get-induction-template-for-term term args)))
		  (machine (machine-from-template template args))
		  (measured-expressions
		   (mapcar #'(lambda (u v) (and u v))
			   (ufunction-measured-subset event) args))
		  (measured-positions
		   (mapcar #'(lambda (u) (occurs-in u measured-expressions))
			   args))
		  (measured-quants (measured-quants-in-machine
				    machine measured-positions))
		  (measure (ufunction-measure event)))
             (log-induction
              formula args machine term measure measured-quants nil)
             ;; (all ... (implies hyp (= (type-of (f ...)) type)) ... )
	     (log-use-axiom (list* 1 1 (implies-right-index)) axiom)
	     (log-rewrite (make-if (get-axiom axiom) (cons name args) *true*)
                          (mapcar #'make-= args args)
			  (list* 1 1 (implies-right-index)))
	     (push-proof-log 'use-axiom (list* 1 1 1 (implies-right-index))
			     axiom t)
	     (push-proof-log 'if-true (list* 1 1 (implies-right-index)))
	     ;; (all ... (implies hyp (= (type-of body) type)) ...)
	     (push-proof-log 'syntax index)
	     (log-type-prescription-recursive
	      name (if-form-machine machine) (ufunction-body event) index)))
	  (t
           (log-use-axiom (cons 1 (=-left-index)) axiom)
           (log-rewrite (make-if (get-axiom axiom) (cons name args) *true*)
                        (mapcar #'make-= args args)
                        (cons 1 (=-left-index)))
           (push-proof-log 'use-axiom (list* 1 1 (=-left-index)) axiom t)
           (push-proof-log 'if-true (cons 1 (=-left-index)))
           ;; (all ... (= (type-of body) type) ... )
           (log-type-of-expr (ufunction-body event) (=-left-index))
           (push-proof-log 'compute index)))
    (log-remove-universally-quantified-true (length args) nil)))

;;; This part must mimic type-of-body and synchronize with machine.
(defun log-type-prescription-recursive (name machine body index)
  ;; (if hyp (if (= (type-of body) type) (true) (false)) (true))
  (cond ((if-p machine)
         ;; both hyp and body are if expressions
         (push-proof-log 'case-analysis (list* 1 1 (if-left-index)) 1)
         (push-proof-log 'case-analysis index 1)
         ;; (if t
         ;;   (if hyp-l
         ;;     (if (= (if t (type-of l) (type-of r)) type) (true) (false))
         ;;     (true))
         ;;   (if hyp-r
         ;;     (if (= (if t (type-of l) (type-of r)) type) (true) (false))
         ;;     (true)))
         (push-proof-log 'look-up (list* 1 1 1 2 (if-left-index)) *true*)
         (push-proof-log 'if-true (list* 1 1 2 (if-left-index)))
         (log-type-prescription-recursive
          name (if-left machine) (if-left body) (if-left-index))
         (log-double-negate-test
          `(type-of ,(if-left body)) `(type-of ,(if-right body))
          (list* 1 1 2 (if-right-index)))
         (push-proof-log 'look-up (list* 1 1 1 1 2 (if-right-index)) *true*)
         (push-proof-log 'if-true (list* 1 1 1 2 (if-right-index)))
         (push-proof-log 'if-false (list* 1 1 2 (if-right-index)))
         (log-type-prescription-recursive
          name (if-right machine) (if-right body) (if-right-index))
         (push-proof-log 'if-equal index))
        ((and (consp body) (eq (car body) name))
         (push-proof-log 'look-up (cons 1 (if-left-index)) *true*)
         (push-proof-log 'if-true (if-left-index))
         (push-proof-log 'if-equal index))
	((not (equal (type-of-any body) *univ-type*))
	 (log-type-of-expr body (list* 1 1 (if-left-index)))
	 (push-proof-log 'compute (cons 1 (if-left-index)))
	 (push-proof-log 'if-true (if-left-index))
	 (push-proof-log 'if-equal index))
	(t
	 ;; Can this ever happen? ***
	 (push-proof-log 'marker (list* 1 1 (if-left-index))
			 (list 'cant-log-type-prescription body)))))

(defun log-remove-universally-quantified-true (n index)
  (unless (zerop n)
    (log-remove-universally-quantified-true (- n 1) (all-expr-index))
    (push-proof-log 'remove-universal index)
    (push-proof-log 'if-true index)))
