
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


;;; ==================== Knuth-Bendix Algorithm ====================


;;; Implementation of the Knuth-Bendix algorithm to obtain a
;;; converging set of rewrite rules.


;;; --------------- Unification

;;; The unifier assumes functions are used consistently with the same
;;; arity. Thus it can only be used on expressions which have been
;;; converted into internal form.

;;; The main functions of the unifier.

;;; Return a substitution list and success indicator if successful.
;;; The success indicator is non-nil if unification succeeds.
(defun unify-expressions (expr-1 expr-2 vars one-way-p)
  (multiple-value-bind (substitutions success)
      (catch 'exit-unify
	(values (unify-expressions-aux expr-1 expr-2 vars nil one-way-p) t))
    (values substitutions success)))

;;; The workhorse for unification. Returns an alist of substitutions
;;; or does a throw of exit-unify.
(defun unify-expressions-aux (expr-1 expr-2 vars substitutions one-way-p)
  (cond ((or (atom expr-1) (atom expr-2))
	 (cond ((equal expr-1 expr-2) substitutions)
	       ((member-eq expr-1 vars)
		(unify-var expr-1 expr-2 vars substitutions))
	       ((and (not one-way-p) (member-eq expr-2 vars))
		(unify-var expr-2 expr-1 vars substitutions))
	       (t (throw 'exit-unify (values nil nil)))))
	(t (unify-args
	    (cdr expr-1) (cdr expr-2) vars
	    (unify-expressions-aux
	     (car expr-1) (car expr-2) vars substitutions one-way-p)
	    one-way-p))))

;;; Unify two lists of arguments of function applications. We can
;;; assume that args-1 and args-2 have the same length because of
;;; the assumption at the top level.
(defun unify-args (args-1 args-2 vars substitutions one-way-p)
  (if (null args-1)
      ;; Done (args-1 and args-2 are null at the same time).
      substitutions
    (unify-args
     (cdr args-1) (cdr args-2) vars
     (unify-expressions-aux
      (car args-1) (car args-2) vars substitutions one-way-p)
     one-way-p)))

;;; Unify a variable var with an expression expr. If var is in the
;;; substitution list then must unify the expr with the substitution
;;; for var. Otherwise do an occurs check.
(defun unify-var (var expr vars substitutions)
  (let ((tmp (assoc-eq var substitutions)))
    (if tmp
	(unify-expressions-aux (cdr tmp) expr vars substitutions nil)
	(let ((tmp (sublis-eq substitutions expr)))
	  (if (occurs-in var tmp)
	      (throw 'exit-unify (values nil nil))
	      (cons (cons var tmp) substitutions))))))



;;; --------------- Superposition

;;; Compute superpositions of a pattern with an expression. It returns
;;; a list of pairs, each consisting of a subexpression that unifies
;;; with the pattern dotted with the unifier (substitutions).

(defun superposition (pattern formula)
  (superposition-aux
   pattern formula
   (unique (append (list-of-free-variables pattern)
		   (list-of-free-variables formula)))
   nil))

(defun superposition-aux (pattern formula vars result)
  (cond ((atom formula) result)
	(t (multiple-value-bind (substitutions success)
	       (unify-expressions pattern formula vars nil)
	     (superposition-args
	       pattern
	       formula
	       vars
	       (if success
		   (cons (cons formula substitutions) result)
		   result))))))

(defun superposition-args (pattern args vars result)
  (cond ((null args) result)
	(t (superposition-args
	     pattern
	     (cdr args)
	     vars
	     (superposition-aux pattern (car args) vars result)))))




;;; --------------- Data Structures


;;; Structure for Conditional Equation.

(defstruct (equation (:type list) :named
		     (:constructor make-equation (condition left right))
		     :predicate)
  condition left right)


;;; FIFO queues used by Knuth-Bendix.

(defvar *possibly-reductive* nil)
(defvar *non-reductive* nil)
(defvar *unmarked-rules* nil)
(defvar *marked-rules* nil)


;;; Index for generated rules (incremented by one after a rule is generated).

(defvar *generated-rule-number* 0)




;;; --------------- Utility Functions


;;; Unique list of free variables in a conditional equation.
(defun list-of-free-variables-in-equation (equation)
  (unique (append (list-of-free-variables (equation-condition equation))
		  (list-of-free-variables (equation-left equation))
		  (list-of-free-variables (equation-right equation)))))


;;; Convert rule subgoal into a list of conjuncts.
(defun subgoal-to-list-of-conjuncts (subgoal)
  (if (null subgoal)
      nil
      (list-of-conjuncts subgoal)))

;;; See if output forms of expr1 and expr2 are equal.
(defun output-form-equal (expr1 expr2)
  (without-proof-logging
   (equal (output-form expr1 nil) (output-form expr2 nil))))

;;; Print non-reductive equations.
(defun print-non-reductive ()
  (cond ((null (car *non-reductive*))
	 (printer `((:newline)
		    (:string "There are no non-reductive equations!"))))
	(t (printer `((:newline)
		      (:string "The non-reductive equations are:")))
	   (dolist (equation (car *non-reductive*))
	     (print-equation equation)))))

;;; Print possibly reductive equations.
(defun print-possibly-reductive ()
  (cond ((null (car *possibly-reductive*))
	 (printer `((:newline)
		    (:string "There are no possibly-reductive equations!"))))
	(t (printer `((:newline)
		      (:string "The possibly reductive equations are:")))
	   (dolist (equation (car *possibly-reductive*))
	     (print-equation equation)))))

;;; Print equation.
(defun print-equation (equation)
  (without-proof-logging
   (printer `((:newline)
              (:formula ,(output-form
			  (if (null (equation-condition equation))
			      (make-= (equation-left equation)
				      (equation-right equation))
                            (make-implies
                             (make-conjunction
                              (equation-condition equation))
                             (make-= (equation-left equation)
                                     (equation-right equation))))
                          nil))))))

;;; Make a new equation (with fresh free variables).
(defun make-new-equation (condition left right)
  (let* ((vars (unique (append (list-of-free-variables condition)
			       (list-of-free-variables left)
			       (list-of-free-variables right))))
	 (substitutions (mapcar #'(lambda (u) (cons u (genvar u))) vars)))
    (make-equation (sublis-eq substitutions condition)
		   (sublis-eq substitutions left)
		   (sublis-eq substitutions right))))



;;; --------------- Subsumption

(defun equation-subsumed-in-fifo (equation fifo)
  (some #'(lambda (u) (equation-subsumes u equation))
	(car fifo)))

(defun equation-subsumes (equation1 equation2)
  (and (= (length (equation-condition equation1))
	  (length (equation-condition equation2)))
       (let ((vars (list-of-free-variables-in-equation equation1)))
	 (multiple-value-bind (substitutions success)
	     (catch 'exit-unify
	       (values (unify-args
			 (list* (equation-left equation1)
				(equation-right equation1)
				(equation-condition equation1))
			 (list* (equation-left equation2)
				(equation-right equation2)
				(equation-condition equation2))
			 vars
			 nil
			 t)
		       t))
	   substitutions
	   success))))

;;; Remove non-reductive equations subsumed by the given equation.
(defun equation-back-subsumption (equation)
  (let ((non-reductive nil))
    (loop while *non-reductive*
	  for next = (pop-fifo *non-reductive*)
	  do (unless (equation-subsumes equation next)
	       (push-fifo next non-reductive)))
    (setq *non-reductive* non-reductive)))
  
;;; Equality test allowing the renaming of quantified variables.
(defun equal-with-renaming (expr1 expr2)
  (cond ((atom expr1) (equal expr1 expr2))
	((atom expr2) nil)
	((all-p expr1)
	 (and (all-p expr2)
	      (equal-with-renaming (all-expr expr1)
				   (subst-eq (all-var expr1)
					     (all-var expr2)
					     (all-expr expr2)))))
	((some-p expr1)
	 (and (some-p expr2)
	      (equal-with-renaming (some-expr expr1)
				   (subst-eq (some-var expr1)
					     (some-var expr2)
					     (some-expr expr2)))))
	(t (every #'equal-with-renaming expr1 expr2))))

;;; Return non-nil if (lrpo> left right) and left does not contain
;;; any quantifiers.
(defun ok-as-rewrite (left right vars)
  (and (not (contains-quantifier left))
       (not (calls-p 'if left))
       (lrpo> left right vars)))



;;; --------------- Initialization


;;; Clear the data structures for Knuth-Bendix.

(defun clear-knuth-bendix ()
  (setq *possibly-reductive* nil
	*non-reductive* nil
	*unmarked-rules* nil
	*marked-rules* nil
	*generated-rule-number* 0))

;;; Initialize the data structures for Knuth-Bendix.

(defun initialize-knuth-bendix ()
  (clear-knuth-bendix)
  (without-proof-logging
   (dolist (event (flatten (user-history)))
     (when (rule-p event)
       (push-fifo event *unmarked-rules*))
     (when (and (axiom-p event) (=-p (axiom-formula event)))
       (push-fifo (make-new-equation
                   nil
                   (internal-form (=-left (axiom-formula event)) nil)
                   (internal-form (=-right (axiom-formula event)) nil))
                  *possibly-reductive*))
     (when (and (axiom-p event)
                (implies-p (axiom-formula event))
                (=-p (implies-right (axiom-formula event))))
       (let ((equation (make-new-equation
			(list-of-conjuncts
			  (internal-form
			    (implies-left (axiom-formula event)) nil))
			(internal-form
                         (=-left (implies-right (axiom-formula event))) nil)
			(internal-form
                         (=-right (implies-right (axiom-formula event))) nil))))
	(push-fifo equation *possibly-reductive*)))))
  (update-proof-status)
  (reset-display))



;;; --------------- Main Routine

;;; The Knuth-Bendix procedure.  It keeps running while there are
;;; possibly reductive equations or unmarked rules.
(defun run-knuth-bendix ()
  (catch 'kb-failure
    (loop while (or *possibly-reductive* *unmarked-rules*)
	  do (kb-process-equations) (kb-process-rule))
    (printer `((:newline)
	       (:string "Knuth Bendix Succeeded!")
	       (:newline)))
    (print-non-reductive)
    (printer `((:newline) (:newline)
               (:string "The rule set is:")
               (:newline)))
    (dolist (rule (car *marked-rules*))
      (print-event (rule-name rule)))))

;;; For each possibly reductive equation, decide whether it is trivial,
;;; it is to be made a rewrite rule, or it is a non-reductive equation.
(defun kb-process-equations ()
  (loop while *possibly-reductive*
	for equation = (kb-rewrite-equation
			 (pop-fifo *possibly-reductive*))
	for vars = (list-of-free-variables-in-equation equation)
	do (let ((condition (equation-condition equation))
		 (left (equation-left equation))
		 (right (equation-right equation)))
	     (unless (or (equal-with-renaming left right)
			 (some #'false-p (equation-condition equation)))
	       (cond ((and (ok-as-rewrite left right vars)
			   (every #'(lambda (u) (ok-as-rewrite left u vars))
				  condition))
		      (kb-make-new-rule equation))
		     ((and (ok-as-rewrite right left vars)
			   (every #'(lambda (u) (ok-as-rewrite right u vars))
				  condition))
		      (kb-make-new-rule equation))
		     ((if-p left)
		      (split-equation-left condition left right))
		     ((if-p right)
		      (split-equation-right condition left right))
		     ((null condition)
		      (printer
		       `((:newline)
			 (:string "The following non-reductive equation
is unconditional:")))
		      (print-equation equation)
		      (printer `((:newline)
				 (:string "Knuth-Bendix fails!")))
		      (throw 'kb-failure nil))
		     ((not (equation-subsumed-in-fifo equation
                                                      *non-reductive*))
		      (equation-back-subsumption equation)
		      (kb-process-superpositions-with-equation
			equation)
		      (printer `((:newline)
				 (:string "Adding non-reductive equation")))
		      (print-equation equation)
		      (push-fifo equation *non-reductive*)))))))

(defun split-equation-left (condition left right)
  (push-fifo (make-new-equation
	       (append condition (list (if-test left)))
	       (if-left left)
	       right)
	     *possibly-reductive*)
  (push-fifo (make-new-equation
	       (append condition
                       (list (make-if (if-test left) *false* *true*)))
	       (if-right left)
	       right)
	     *possibly-reductive*))

(defun split-equation-right (condition left right)
  (push-fifo (make-new-equation
	       (append condition (list (if-test right)))
	       left
	       (if-left right))
	     *possibly-reductive*)
  (push-fifo (make-new-equation
	       (append condition
                       (list (make-if (if-test right) *false* *true*)))
	       left
	       (if-right right))
	     *possibly-reductive*))



;;; Rewrite an equation using the full power of the rewriter,
;;; where existing rules, frule and grules are used (equations
;;; are not yet rules).
(defun kb-rewrite-equation (equation)
  (reset-deductive-database)
  (with-egraph-protected
   (without-proof-logging
    (let* ((condition (kb-rewrite-condition
			(equation-condition equation)))
	   (left (rewrite-formula-in-context
		   (equation-left equation) nil))
	   (right (rewrite-formula-in-context
		    (equation-right equation) nil)))
      (cond ((and (if-p left) (if-p right))
	     (let ((conclusion (rewrite-formula-in-context
				 (make-= (equation-left equation)
					 (equation-right equation))
                                 nil)))
	       (if (true-p conclusion)
		   (make-equation condition *true* *true*)
		   (make-equation condition right left))))
	    ((ok-as-rewrite
	       right left (list-of-free-variables-in-equation equation))
	     (make-equation condition right left))
	    (t (make-equation condition left right)))))))

(defun kb-rewrite-condition (condition)
  (unless (null condition)
    (let ((car-condition (rewrite-formula-in-context (car condition) nil)))
      (cond ((true-p car-condition) (kb-rewrite-condition (cdr condition)))
	    (t (assume-true car-condition)
	       (cons car-condition (kb-rewrite-condition (cdr condition))))))))

;;; Process an unmarked rule. This includes processing critical pairs,
;;; superpositions.
(defun kb-process-rule ()
  (unless (null *unmarked-rules*)
    (let ((rule (pop-fifo *unmarked-rules*)))
      (kb-process-critical-pairs rule)
      (kb-process-superpositions-with-rule rule)
      (push-fifo rule *marked-rules*))))

(defun kb-generate-new-name ()
  (let ((new-name (intern
                   (string-append "KB"
                                  (format nil "~A" *generated-rule-number*))
		   *zk-package*)))
    (unless (null (get-event new-name))	; make sure new name not used
      (loop until (null (get-event new-name))
	    do (incf *generated-rule-number*)
	    (setq new-name
		  (intern
                   (string-append
                    "KB"
                    (format nil "~A" *generated-rule-number*))
		   *zk-package*))))
    new-name))

(defun kb-create-new-rule (equation)
  (let* ((formula
          (without-proof-logging
           (output-form
            (if (null (equation-condition equation))
                (make-= (equation-left equation)
                        (equation-right equation))
              (make-implies (make-conjunction
                             (equation-condition equation))
                            (make-= (equation-left equation)
                                    (equation-right equation))))
            nil)))
	 (args (unique (list-of-free-variables
                        (without-proof-logging (internal-form formula nil)))))
	 (rule-name (rule (kb-generate-new-name) args formula)))
    (when (null rule-name)
      (error "Bad rewrite rule generated by KB for ~A" formula))
    (get-event rule-name)))

(defun kb-make-new-rule (equation)
  (let ((rule (kb-create-new-rule equation))
	(marked-rules nil)
	(unmarked-rules nil))
    (push-fifo rule unmarked-rules)
    (loop while *marked-rules*
	  for rule = (pop-fifo *marked-rules*)
	  for equation = (make-new-equation
			   (subgoal-to-list-of-conjuncts (rule-subgoal rule))
			   (rule-pattern rule)
			   (rule-value rule))
	  for normalized-equation = (with-disabled ((list (event-name rule)))
				      (kb-rewrite-equation equation))
	  do (if (not (output-form-equal (equation-left equation)
                                         (equation-left normalized-equation)))
		 (unless (or (some #'false-p
                                   (equation-condition normalized-equation))
			     (equation-subsumed-in-fifo normalized-equation
							*possibly-reductive*))
		   (push-fifo normalized-equation *possibly-reductive*))
		 (if (and (output-form-equal
                           (equation-condition equation)
                           (equation-condition normalized-equation))
			  (output-form-equal
                           (equation-right equation)
                           (equation-right normalized-equation)))
		     (push-fifo rule marked-rules)
		     (push-fifo (kb-create-new-rule normalized-equation)
                                marked-rules))))
    (loop while *unmarked-rules*
	  for rule = (pop-fifo *unmarked-rules*)
	  for equation = (make-new-equation
			   (subgoal-to-list-of-conjuncts (rule-subgoal rule))
			   (rule-pattern rule)
			   (rule-value rule))
	  for normalized-equation = (with-disabled ((list (event-name rule)))
				      (kb-rewrite-equation equation))
	  do (if (not (output-form-equal (equation-left equation)
                                         (equation-left normalized-equation)))
		 (unless (or (some #'false-p
                                   (equation-condition normalized-equation))
			     (equation-subsumed-in-fifo normalized-equation
							*possibly-reductive*))
		   (push-fifo normalized-equation *possibly-reductive*))
		 (if (and (output-form-equal
                           (equation-condition equation)
                           (equation-condition normalized-equation))
			  (output-form-equal
                           (equation-right equation)
                           (equation-right normalized-equation)))
		     (push-fifo rule unmarked-rules)
		     (push-fifo (kb-create-new-rule normalized-equation)
                                unmarked-rules))))
    (setq *marked-rules* marked-rules
	  *unmarked-rules* unmarked-rules)))

;;; Check superpositions of equation against marked rules to generate
;;; possibly reductive equations.
(defun kb-process-superpositions-with-equation (equation)
  (let ((formula (car (equation-condition equation)))
	(rest (cdr (equation-condition equation))))
    (dolist (rule (car *marked-rules*))
      (dolist (super (superposition (rule-pattern rule) formula))
	;; Recall (car super) is expression that unifies with rule pattern,
	;; (cdr super) is the unifier (substitutions).
	(let ((condition
		(sublis-eq (cdr super)
			   (append (subgoal-to-list-of-conjuncts
                                    (rule-subgoal rule))
				   (list (subst-equal (rule-value rule)
						      (car super)
						      formula))
				   rest))))
	  (unless (some #'false-p condition)
	    (let ((equation (make-new-equation
			      condition
			      (sublis-eq (cdr super)
					 (equation-left equation))
			      (sublis-eq (cdr super)
					 (equation-right equation)))))
	      (unless (equation-subsumed-in-fifo equation *possibly-reductive*)
		(push-fifo equation *possibly-reductive*)))))))))

;;; For each non-reductive equation, check superposition of first subgoal
;;; against the given rule's pattern.
(defun kb-process-superpositions-with-rule (rule)
  (let ((pattern (rule-pattern rule))
	(subgoal (subgoal-to-list-of-conjuncts (rule-subgoal rule)))
	(value (rule-value rule)))
    (dolist (equation (car *non-reductive*))
      (let ((formula (first (equation-condition equation)))
	    (rest (cdr (equation-condition equation))))
	(dolist (super (superposition pattern formula))
	  (let ((condition (sublis-eq (cdr super)
				      (append subgoal
					      (list (subst-equal value
								 (car super)
								 formula))
					      rest))))
	    (unless (some #'false-p condition)
	      (let ((equation (make-new-equation
				condition
				(sublis-eq (cdr super)
					   (equation-left equation))
				(sublis-eq (cdr super)
					   (equation-right equation)))))
		(unless (equation-subsumed-in-fifo equation
                                                   *possibly-reductive*)
		  (push-fifo equation *possibly-reductive*))))))))))

(defun kb-compute-superpositions-left (pleft left pright right condition)
  (dolist (super (superposition pleft left))
    (unless (some #'false-p (sublis-eq (cdr super) condition))
      (let ((equation
	      (make-new-equation
		(sublis-eq (cdr super) condition)
		(sublis-eq (cdr super) (subst-equal pright (car super) left))
		(sublis-eq (cdr super) right))))
	(unless (equation-subsumed-in-fifo equation *possibly-reductive*)
	  (push-fifo equation *possibly-reductive*))))))

;;; Check rule against marked and unmarked rules for critical pairs.
(defun kb-process-critical-pairs (rule)
   (let ((current-label (event-number rule)))
    (dolist (marked-rule (car *marked-rules*))
      (unless (> (event-number marked-rule) current-label)
	(kb-compute-superpositions-left
	  (rule-pattern rule)
	  (rule-pattern marked-rule)
	  (rule-value rule)
	  (rule-value marked-rule)
	  (append (subgoal-to-list-of-conjuncts (rule-subgoal marked-rule))
		  (subgoal-to-list-of-conjuncts (rule-subgoal rule))))
	(kb-compute-superpositions-left
	  (rule-pattern marked-rule)
	  (rule-pattern rule)
	  (rule-value marked-rule)
	  (rule-value rule)
	  (append (subgoal-to-list-of-conjuncts (rule-subgoal rule))
		  (subgoal-to-list-of-conjuncts (rule-subgoal marked-rule))))))
    (dolist (unmarked-rule (car *unmarked-rules*))
      (unless (> (event-number unmarked-rule) current-label)
	(kb-compute-superpositions-left
	  (rule-pattern rule)
	  (rule-pattern unmarked-rule)
	  (rule-value rule)
	  (rule-value unmarked-rule)
	  (append (subgoal-to-list-of-conjuncts (rule-subgoal unmarked-rule))
		  (subgoal-to-list-of-conjuncts (rule-subgoal rule))))
	(kb-compute-superpositions-left
	  (rule-pattern unmarked-rule)
	  (rule-pattern rule)
	  (rule-value unmarked-rule)
	  (rule-value rule)
	  (append (subgoal-to-list-of-conjuncts (rule-subgoal rule))
		  (subgoal-to-list-of-conjuncts
                   (rule-subgoal unmarked-rule))))))))

;;; Command to run Knuth-Bendix.

(defcmd knuth-bendix ()
  ((:string "Run the Knuth-Bendix procedure on the current theory
(minus the initial theory)."))
  (initialize-knuth-bendix)
  (run-knuth-bendix))
