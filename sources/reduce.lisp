
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


;;; ========================== The Reducer ============================
;;;
;;; The reducer is the workhorse of the theorem prover. It performs,
;;; in an innermost first fashion, simplification, rewriting and
;;; invocation of functions, in that order. At its core, the reducer
;;; reduces propositional formulas, represented internally in IF form.
;;;
;;; The simplifier uses a "deductive database" to implement a
;;; Nelson-Oppen style of "cooperating decision procedures". It deals
;;; with equalities and integer relations rather well. Many decision
;;; procedures for the "constructor-accessor" types of theories
;;; can be encoded using the "frule" and "grule" facility. The
;;; simplifier also performs instantiations of quantified expressions,
;;; applying the "one-point" rule and some resolution-style reasoning,
;;; although it doesn't try very hard for efficiency reasons.
;;;
;;; The rewriter performs unconditional and conditional rewriting,
;;; performed "innermost first" using an evaluation strategy
;;; attributed to Gallier and Book. Permutative rules are handled
;;; using lexicographic ordering to ensure termination.
;;;
;;; Invocation of functions (the replacement of function calls by their
;;; definitions) are performed using heuristics mainly those developed
;;; by Boyer and Moore for recursive functions.
;;;
;;; The formula fed to the reducer is assumed to already be in IF form
;;; (all logical connectives replaced by their IF equivalents).
;;; Quantified variables have been uniquely renamed to avoid expensive
;;; operations such as distinguishing free vs bound occurrence if
;;; variable names are not distinct.
;;;
;;; In summary, the reducer works by traversing the formula, performing
;;; simplification, rewriting and function invocations on subexpressions,
;;; performing case analysis when necessary, and making use of contextual
;;; assumptions based on the IF structure of the formula.
;;; ___________________________________________________________________________



;;; ========== Flags for controlling what the reducer performs.

;;; Simplification is always performed.

;;; When non-nil, perform rewriting.
(defvar *reduce-applies-rules-flag* t)

;;; When non-nil, perform function invocations.
(defvar *reduce-applies-functions-flag* t)

;;; Maximum depth limit for reduction (recursive call limit).
(defvar *maximum-level-of-reduction* 128.)

;;; Maximum depth of subgoaling.
(defvar *maximum-level-of-subgoaling* 8.)

;;; If non-nil then fully evaluate recursive function calls which
;;; produce (INT) or (BOOL) values (subject to depth limit).
(defvar *reduce-evaluates-values-flag* t)

;;; If non-nil then the reducer does case analysis (moving "IF"s
;;; out of function calls).
(defvar *reduce-does-case-analysis-flag* t)

;;; If non-nil then the reducer does quantifier case analysis
;;; (moving IFs out of quantification if logically sound).
(defvar *reduce-does-quantifier-case-analysis-flag* t)

;;; If non-nil then when the reducer encounters a quantified
;;; formula, it tries to move out inner quantifiers that become the
;;; same kind at that level.
(defvar *reduce-collects-quantifiers-flag* t)

;;; Enable/disable cache. Cache is disabled when proof logging is
;;; enabled.
(defvar *reduce-caches-all-results-flag* t)

;;; If non-nil, move IFs out of IF tests (a special kind of case
;;; analysis).
(defvar *reduce-normalizes-flag* t)

;;; =========== End of flags.


;;; =========== Additional Variables

;;; Variables used in the heuristics for recursive functions. Each
;;; is a list of expressions.
(defvar *assumed-expressions* nil)
(defvar *seen-expressions* nil)

;;; Variable to maintain the list of subgoals which are being worked on by
;;; the reducer. Each subgoal is represented as a pair consisting of
;;; an expression and a list of substitutions.
(defvar *current-subgoal-list* nil)

;;; Variable used to maintain various statistics.
(defvar *reduce-statistics* (make-stat))

;;; =========== End of Additional Variables


;;; =============== Macros ===============

;;; --- Macros for use with continuations

(defmacro recur-left (instantiations index continuations)
  `(eq-reduce-formula
    (caar ,continuations) (third (car ,continuations)) nil ,instantiations
    (if (null (cdr ,continuations))
        (cons 2 (cdr ,index))
      (list* 1 2 (cdr ,index)))
    (cdr ,continuations)))

(defmacro recur-right (instantiations index continuations)
  `(eq-reduce-formula
    (second (car ,continuations)) (third (car ,continuations)) nil
    ,instantiations
    (if (null (cdr ,continuations))
        (cons 3 (cdr ,index))
      (list* 1 3 (cdr ,index)))
    (cdr ,continuations)))

;;; Perform body and keep processing continuations until there are
;;; no more continuations.

(defmacro apply-while-continue (body)
  `(multiple-value-bind
    (continue fcn args)
    (catch 'reduce-cont
      (values nil ,body nil))
    (loop while continue
	  do (progn
               (multiple-value-setq
                (continue fcn args)
                (catch 'reduce-cont
                  (values nil (apply fcn args) nil)))))
    fcn))

;;; Perform body and keep processing continuations until there are
;;; no more continuations or until we hit the specified continuation
;;; (in effect a marker in the stack).

(defmacro apply-while-continue-with-suspend ((cont) body)
  `(let ((entry-continuation ,cont))
     (multiple-value-bind
      (continue fcn args)
      (catch 'reduce-cont
        (values nil ,body nil))
      (loop while (and continue (neq (sixth args) (cdr entry-continuation)))
            do (progn
                 (multiple-value-setq
                  (continue fcn args)
                  (catch 'reduce-cont
                    (values nil (apply fcn args) nil)))))
      (values continue fcn args))))

;;; =============== End of Macros ===============


;;; ============ Top Level for the Reducer

;;; The top level reducer is the main traversal routine.
;;; The formula to be reduced is assumed to be in IF form.
;;; If predicate is non-nil then we are interested only in whether
;;; the formula can be reduced to (TRUE) or (FALSE) depending on
;;; the predicate, returning t is so and nil otherwise. The
;;; substitutions list is used as part of the Gallier-Book scheme.
(defun eq-reduce-formula (formula substitutions predicate instantiations index
                                  &optional (continuations nil))
  (push-proof-log 'marker index
                  (list 'reduce 'start *maximum-level-of-reduction*))
  (let ((result
         (let ((*maximum-level-of-reduction*
                (1- *maximum-level-of-reduction*)))
           (cond ((< *maximum-level-of-reduction* 0)
		  ;; depth limit
                  (cond ((or (not *reduce-normalizes-flag*)
                             (null continuations)
                             predicate)
                         (result-of
                          (sublis-eq substitutions formula) predicate
                          instantiations))
                        (t
                         (make-if-from-continuations
                          (sublis-eq substitutions formula)
                          continuations
                          (if (null continuations) index (cdr index))))))
                 ((literal-p formula)
		  ;; literals don't reduce
                  (let ((*maximum-level-of-reduction*
                         (1+ *maximum-level-of-reduction*)))
                    (cond ((null continuations)
                           (result-of formula predicate instantiations))
                          (t
                           (eq-reduce-reduced-formula-continuations
                            formula instantiations index continuations)))))
                 ((constant-p formula)
                  (eq-apply-anything-formula
                   formula predicate instantiations index continuations))
                 ((atom formula)
		  ;; could be a bound variable
                  (let ((result
                         (result-of
                          (eq-lookup (binding-of formula substitutions formula)
                                     index
				     (make-context-for-bool-p-continuations
				      continuations index)
				     )
                          predicate
                          instantiations)) 
                        (*maximum-level-of-reduction*
                         (1+ *maximum-level-of-reduction*)))
                    (cond ((null continuations) result)
                          (t
                           (eq-reduce-reduced-formula-continuations
                            result instantiations index continuations)))))
                 ((if-p formula)
		  ;; if expression, the main traversal construct
                  (cond
                   ((or (not *reduce-normalizes-flag*)
                        predicate)
                    (eq-reduce-if-formula-without-normalization
                     formula substitutions predicate instantiations index))
                   ((null continuations)
                    ;; reduce the test with initial continuation
                    (apply-while-continue
                     (eq-reduce-formula
                      (if-test formula) substitutions nil
                      instantiations (if-test-index)
                      (list (list (if-left formula) (if-right formula)
                                  substitutions index)))))
                   (t
                    ;; since there is continuation, must be an IF
                    ;; within an "if" test, "normalize" and save
                    ;; the new branches as additional continuation.
                    (incf (stat-normalization *reduce-statistics*))
                    (push-proof-log 'case-analysis (cdr index) 1)
                    (throw
                     'reduce-cont
                     (values
                      t #'eq-reduce-formula
                      (list (if-test formula) substitutions nil
                            instantiations index
                            (cons (list (if-left formula) (if-right formula)
                                        substitutions
					;; After normalization, we now work
					;; with outer if, hence (cdr index)
					(cdr index))
                                  continuations)))))))
                 ((or (all-p formula) (some-p formula))
		  ;; quantified expression
                  (cond
                   ((or (not *reduce-normalizes-flag*) predicate)
		    ;; no normalization here
                    (eq-reduce-quantifier-cases
                     (eq-reduce-eliminate-quantifiers
                      formula substitutions index)
                     predicate
                     instantiations
                     index))
                   (t
                    (let ((result (eq-reduce-eliminate-quantifiers
                                   formula substitutions index))
                          (*maximum-level-of-reduction*
                           (1+ *maximum-level-of-reduction*)))
                      (multiple-value-bind
                       (formula success)
                       (perform-quantifier-case-analysis result index)
                       (cond
                        (success
			 ;; needs re-simplification
                         (eq-reduce-formula
                          formula nil predicate instantiations index
                          continuations))
                        ((or (all-p formula) (some-p formula))
                         (let ((result
                                (apply-one-point-rule formula index)))
                           (cond
                            (result
                             (eq-reduce-formula
                              result nil predicate instantiations
                              index continuations))
                            (t (when
                                *reduce-collects-quantifiers-flag*
                                (setq formula
                                      (collect-quantifiers formula index)))
                               (let ((result
                                      (eq-lookup
				       formula index
				       (make-context-for-bool-p-continuations
					continuations index)
				       )))
                                 (cond
                                  ((null continuations) result)
                                  (t
                                   (eq-reduce-reduced-formula-continuations
                                    result instantiations index
                                    continuations))))))))
                        (t (eq-reduce-formula
                            formula nil predicate instantiations index
                            continuations))))))))
		 ;; A non-IF subexpression is encountered
                 (t (eq-reduce-cases-or-apply
                     (cons (car formula)
                           (let ((seen nil))
                             (loop for expr in (cdr formula)
                                   for number = 1 then (+ 1 number)
                                   collect
                                   (let* ((*seen-expressions* seen)
                                          (res (eq-reduce-formula
                                                expr substitutions nil nil
                                                (cons number index))))
                                     (push res seen)
                                     res))))
                     predicate
                     instantiations
                     index
                     continuations))))))
    ;; Proof logging marker used for proof browsing.
    (when *record-proof-logs-flag*
      (cond ((and (eq (first (car *proof-log*)) 'marker)
                  (eq (first (third (car *proof-log*))) 'reduce)
                  (eq (second (third (car *proof-log*))) 'start))
             (pop *proof-log*))
            (t
             (push-proof-log
              'marker index
              (list 'reduce 'end *maximum-level-of-reduction*)))))
    result))

;;; ============ End of Top Level for the Reducer


;;; ============ Case Analysis

;;; (F A (IF B C D) E G) => (IF B (F A C E G) (F A D E G))
;;; The IF can occur in any argument position of F.

(defun perform-case-analysis-aux (formula processed-formula index)
  (if (null formula)
      (reverse processed-formula)
      (let ((arg (car formula)) (rest (cdr formula)))
	(if (if-p arg)
	    (progn
	      (incf (stat-case-analysis *reduce-statistics*))
	      (push-proof-log 'case-analysis index (length processed-formula))
	      (make-if (if-test arg)		;already case-analysis
		       (perform-case-analysis-aux (cons (if-left arg) rest)
						   processed-formula
						   (if-left-index))
		       (perform-case-analysis-aux (cons (if-right arg) rest)
						   processed-formula
						   (if-right-index))))
	    (perform-case-analysis-aux
             rest (cons arg processed-formula) index)))))

;;; Called by reducer if *reduce-does-case-analysis-flag* is t.
(defun perform-case-analysis (formula index)
  (perform-case-analysis-aux formula nil index))

;;; ============ End of Case Analysis


;;; ============ Quantifier Case Analysis

;;; e.g. (ALL (X) (IF P Q (FALSE))) => (IF (ALL (X) P) (ALL (X) Q) (FALSE))
;;; There are many other special cases. To understand the special cases,
;;; look at the corresponding proof logging functions (e.g.,
;;; log-all-case-analysis-1).


;;; Code to attempt an "ALL" case analysis and recur (on itself
;;; or through perform-some-quantifier-cases).
(defun perform-all-quantifier-cases (var expr index)
  (if (not (if-p expr))
      (if (occurs-in var expr)
	  (make-all-single var expr)
	  (progn (push-proof-log 'remove-universal index)
		 (coerce-to-bool expr index)))
      (let ((test (if-test expr))
            (left (if-left expr))
            (right (if-right expr)))
	(cond ((not (occurs-in var test))	;if
	       (incf (stat-case-analysis *reduce-statistics*))
	       (log-all-case-analysis-1	(make-all (list var) expr) index)
	       (make-if
                test
                (perform-all-quantifier-cases var left (if-left-index))
                (perform-all-quantifier-cases var right (if-right-index))))
	      ((true-p right)			;not/implies
	       (cond ((not (occurs-in var left))
		      (incf (stat-case-analysis *reduce-statistics*))
		      (log-all-case-analysis-2 (make-all (list var) expr) index)
		      (make-if
                       (perform-some-quantifier-cases var test (if-test-index))
                       (coerce-to-bool left (if-left-index))
                       *true*))
		     (t (make-all-single var expr))))
	      ((true-p left)			;or
	       (cond ((not (occurs-in var right))
		      (incf (stat-case-analysis *reduce-statistics*))
		      (log-all-case-analysis-3 (make-all-single var expr) index)
		      (make-if
                       (perform-all-quantifier-cases var test (if-test-index))
                       *true*
                       (coerce-to-bool right (if-right-index))))
		     (t (make-all-single var expr))))
	      ((false-p right)			;and
	       (incf (stat-case-analysis *reduce-statistics*))
	       (push-proof-log 'all-case-analysis index)
	       (make-if (perform-all-quantifier-cases var test (if-test-index))
			(perform-all-quantifier-cases var left (if-left-index))
			*false*))
	      ((false-p left)			;and-not
	       (incf (stat-case-analysis *reduce-statistics*))
	       (log-all-case-analysis-5 (make-all-single var expr) index)
	       (make-if
                (perform-some-quantifier-cases var test (if-test-index))
                *false*
                (perform-all-quantifier-cases var right (if-right-index))))
	      (t (make-all-single var expr))))))

;;; Code to attempt a "SOME" case analysis and recur (on itself
;;; or through perform-all-quantifier-cases).
(defun perform-some-quantifier-cases (var expr index)
  (if (not (if-p expr))
      (if (occurs-in var expr)
	  (make-some-single var expr)
          (progn (log-remove-existential index)
		 (coerce-to-bool expr index)))
      (let ((test (if-test expr))
            (left (if-left expr))
            (right (if-right expr)))
	(cond ((not (occurs-in var test))	;if
	       (incf (stat-case-analysis *reduce-statistics*))
	       (log-some-case-analysis-1 (make-some-single var expr) index)
	       (make-if
                test
                (perform-some-quantifier-cases var left (if-left-index))
                (perform-some-quantifier-cases var right (if-right-index))))
	      ((false-p right)			;and
	       (cond ((not (occurs-in var left))
		      (incf (stat-case-analysis *reduce-statistics*))
		      (log-some-case-analysis-2
		       (make-some-single var expr) index)
		      (make-if
                       (perform-some-quantifier-cases var test (if-test-index))
                       (coerce-to-bool left (if-left-index))
                       *false*))
		     (t (make-some-single var expr))))
	      ((false-p left)			;and not
	       (cond ((not (occurs-in var right))
		      (incf (stat-case-analysis *reduce-statistics*))
		      (log-some-case-analysis-3
		       (make-some-single var expr) index)
		      (make-if
                       (perform-all-quantifier-cases var test (if-test-index))
                       *false*
                       (coerce-to-bool right (if-right-index))))
		     (t (make-some-single var expr))))
	      ((true-p right)			;implies/not
	       (incf (stat-case-analysis *reduce-statistics*))
	       (log-some-case-analysis-4 index)
	       (make-if
                (perform-all-quantifier-cases var test (if-test-index))
                (perform-some-quantifier-cases var left (if-left-index))
                *true*))
	      ((true-p left)			;or
	       (incf (stat-case-analysis *reduce-statistics*))
	       (log-some-case-analysis-5 (make-some-single var expr) index)
	       (make-if
                (perform-some-quantifier-cases var test (if-test-index))
                *true*
                (perform-some-quantifier-cases var right (if-right-index))))
	      (t (make-some-single var expr))))))

;;; The dispatcher.
(defun perform-quantifier-case-analysis-aux (formula index)
  (cond ((all-p formula)
	 (perform-all-quantifier-cases
	   (all-var formula)
	   (perform-quantifier-case-analysis-aux
            (all-expr formula) (cons 2 index))
	   index))
	((some-p formula)
	 (perform-some-quantifier-cases
	   (some-var formula)
	   (perform-quantifier-case-analysis-aux
            (some-expr formula) (cons 2 index))
	   index))
	(t formula)))

;;; Entry point for quantifier case analysis. Called if
;;; *reduce-does-quantifier-case-analysis-flag* is non-nil.
(defun perform-quantifier-case-analysis (formula index)
  (let ((tmp (stat-case-analysis *reduce-statistics*)))
    (values (perform-quantifier-case-analysis-aux formula index)
	    (not (= tmp (stat-case-analysis *reduce-statistics*))))))

;;; ============ End of Quantifier Case Analysis


;;; ============ Continuations

;;; Continuations are used to speed up reduction that involve IF
;;; normalization (special case analysis moving an IF out of an IF
;;; test). The speed up is gained by delaying IF normalization until
;;; necessary (lazy evaluation), potentially avoiding duplicating branches.
;;;
;;; The left and right branches of an IF are pushed together with
;;; applicable substitutions as a continuation (note that if the stack
;;; of continuations was not empty before the push, then the IF
;;; expression is a test of an outer IF expression, therefore
;;; may need to be "normalized" eventually).  The test is then
;;; processed, which may itself be an IF expression and causes
;;; additional continuations to be pushed onto the continuation stack.
;;; Once we're done with the pushing (we don't encounter any more IF
;;; expressions) we start popping the continuations and process them.
;;; Only use continuations when predicate is nil.

;;; Code to construct an IF form from a test and a stack of continuations.
;;; Note that the code assumes that test has been fully substituted.

(defun make-if-from-continuations (test continuations index)
  (cond
   ((null continuations) test)
   ((true-p test)
    (push-proof-log 'if-true index)
    (make-if-from-continuations
     (sublis-eq (third (car continuations)) (caar continuations))
     (cdr continuations) index))
   ((false-p test)
    (push-proof-log 'if-false index)
    (make-if-from-continuations
     (sublis-eq (third (car continuations)) (second (car continuations)))
     (cdr continuations) index))
   (t
    (make-if
     test
     (make-if-from-continuations
      (sublis-eq (third (car continuations)) (caar continuations))
      (cdr continuations) (if-left-index))
     (make-if-from-continuations
      (sublis-eq (third (car continuations)) (second (car continuations)))
      (cdr continuations) (if-right-index))))))

;;; The context for a continuation is the innermost IF represented
;;; by the stack of continuations.

(defun make-context-for-bool-p-continuations (continuations index)
  (unless (null continuations)
    (list (list 'if) (cdr (member-equal 1 index)))))

;;; --- End of utility macros and functions

;;; Main continuation-specific reducer code

(defun eq-reduce-reduced-formula-continuations
  (formula instantiations index continuations)
  (cond
   ((true-p formula)
    (push-proof-log 'if-true (cdr index))
    (let ((args (list (caar continuations) (third (car continuations))
                      nil instantiations
                      (if (null (cdr continuations)) (cdr index) index)
                      (cdr continuations))))
      (throw 'reduce-cont (values t #'eq-reduce-formula args))))
   ((false-p formula)
    (push-proof-log 'if-false (cdr index))
    (let ((args (list (second (car continuations)) (third (car continuations))
                      nil instantiations
                      (if (null (cdr continuations)) (cdr index) index)
                      (cdr continuations))))
      (throw 'reduce-cont (values t #'eq-reduce-formula args))))
   (t
    (let (l-cont l-fcn l-args r-cont r-fcn r-args)
      (with-assumed-true
       (formula)
       (multiple-value-setq
        (l-cont l-fcn l-args)
        (apply-while-continue-with-suspend
         ((cdr continuations))
         (recur-left instantiations index continuations))))
      (with-assumed-false
       (formula)
       (multiple-value-setq
        (r-cont r-fcn r-args)
        (apply-while-continue-with-suspend
         ((cdr continuations))
         (recur-right instantiations index continuations))))
      (cond
       (l-cont
        (cond
         (r-cont
          (cond
           ((equal (first l-args) (first r-args))
            (push-proof-log 'if-equal (cdr index))
            (throw 'reduce-cont
                   (values t
                           l-fcn
                           (list (first l-args)
                                 (second l-args)
                                 (third l-args)
                                 (fourth l-args)
                                 (if (null (sixth l-args)) (cdr index) index)
                                 (sixth l-args)))))
           (t
            (multiple-value-bind
             (left right)
             (with-assumed-true-then-false
              (formula)
              (apply-while-continue (apply l-fcn l-args))
              (apply-while-continue (apply r-fcn r-args)))
             (cond ((equal left right)
                    (push-proof-log 'if-equal (cdr index))
                    left)
                   (t
                    (make-if formula left right)))))))
         (t
          (let ((left (with-assumed-true
                       (formula)
                       (apply-while-continue (apply l-fcn l-args)))))
            (cond ((equal left r-fcn)
                   (push-proof-log 'if-equal (cdr index))
                   left)
                  (t
                   (make-if formula left r-fcn)))))))
       (r-cont
        (let ((right (with-assumed-false
                      (formula)
                      (apply-while-continue (apply r-fcn r-args)))))
          (cond ((equal l-fcn right)
                 (push-proof-log 'if-equal (cdr index))
                 right)
                (t (make-if formula l-fcn right)))))
       ((equal l-fcn r-fcn)
        (push-proof-log 'if-equal (cdr index))
        l-fcn)
       (t (make-if formula l-fcn r-fcn)))))))
        

;;; ============ End of Continuations


;;; ============ Reducers for Subgoals

;;; For subgoals, we are not interested in simplified expressions.
;;; We are only interested to knowing if the subgoal can be reduced
;;; to (TRUE) or, if the subgoal is a logical negation (NOT expr)
;;; where expr is Boolean, if expr can be reduced to (FALSE).

(defun eq-reduce-to-true (formula substitutions index)
  (let ((test (if-test formula))
	(left (if-left formula))
	(right (if-right formula)))
    (cond ((false-p right)
	   (and (not (false-p left))
		(eq-reduce-formula
                 test substitutions *true* nil (if-test-index))
		(eq-reduce-formula
                 left substitutions *true* nil (if-left-index))
		(progn (push-proof-log 'if-true index) t)))	   
	  ((false-p left)
	   (and (cond ((bool-p test)
                       (eq-reduce-formula
                        test substitutions *false* nil (if-test-index)))
                      (t
		       (push-proof-log 'if-test index)
                       (eq-reduce-formula
                        (make-= test *true*) substitutions *false* nil
                        (if-test-index))))
                (eq-reduce-formula
                 right substitutions *true* nil (if-right-index))
		(progn (push-proof-log 'if-false index) t)))
	  ((true-p left)
	   (cond ((true-p right) (push-proof-log 'if-equal index) t)
		 ((let ((proof-log (save-proof-log)))
                    (or (eq-reduce-formula
                         test substitutions *true* nil (if-test-index))
                        (progn (restore-proof-log proof-log) nil)))
		  (push-proof-log 'if-true index) t)
		 ((eq-reduce-formula
                   right substitutions *true* nil (if-right-index))
		  (push-proof-log 'if-equal index) t)))
	  ((true-p right)
	   (cond ((let ((proof-log (save-proof-log)))
                    (or
                     (cond ((bool-p test)
                            (eq-reduce-formula
                             test substitutions *false* nil (if-test-index)))
                           (t
			    (push-proof-log 'if-test index)
                            (eq-reduce-formula
                             (make-= test *true*) substitutions *false* nil
                             (if-test-index))))
                     (progn (restore-proof-log proof-log) nil)))
		  (push-proof-log 'if-false index) t)
		 ((eq-reduce-formula
                   left substitutions *true* nil (if-left-index))
		  (push-proof-log 'if-equal index) t)))
	  (t (eq-reduce-if-parts
              (eq-reduce-formula test substitutions nil nil (if-test-index))
              left
              right
              substitutions
              *true*
              nil
              index)))))


(defun eq-reduce-to-false (formula substitutions index)
  (let ((test (if-test formula))
	(left (if-left formula))
	(right (if-right formula)))
    (cond ((false-p right)
	   (cond ((false-p left)
		  (push-proof-log 'if-equal index) t)
		 ((let ((proof-log (save-proof-log)))
                    (or (cond
                         ((bool-p test)
                          (eq-reduce-formula
                           test substitutions *false* nil (if-test-index)))
                         (t
			  (push-proof-log 'if-test index)
                          (eq-reduce-formula
                           (make-= test *true*) substitutions *false* nil
                           (if-test-index))))
                        (progn (restore-proof-log proof-log) nil)))
                  (push-proof-log 'if-false index) t)
		 ((eq-reduce-formula
                   left substitutions *false* nil (if-left-index))
		  (push-proof-log 'if-equal index) t)))
	  ((false-p left)
	   (cond ((let ((proof-log (save-proof-log)))
                    (or (eq-reduce-formula
                         test substitutions *true* nil (if-test-index))
                        (progn (restore-proof-log proof-log) nil)))
		  (push-proof-log 'if-true index) t)
		 ((eq-reduce-formula
                   right substitutions *false* nil (if-right-index))
		  (push-proof-log 'if-equal index) t)))
	  ((true-p left)
	   (and (not (true-p right))
                (cond ((bool-p test)
                       (eq-reduce-formula
                        test substitutions *false* nil (if-test-index)))
                      (t
		       (push-proof-log 'if-test index)
                       (eq-reduce-formula
                        (make-= test *true*) substitutions *false* nil
                        (if-test-index))))
		(eq-reduce-formula
                 right substitutions *false* nil (if-right-index))
		(progn (push-proof-log 'if-false index) t)))
	  ((true-p right)
	   (and (eq-reduce-formula
                 test substitutions *true* nil (if-test-index))
		(eq-reduce-formula
                 left substitutions *false* nil (if-left-index))
		(progn (push-proof-log 'if-true index) t)))
	  (t (eq-reduce-if-parts
              (eq-reduce-formula test substitutions nil nil (if-test-index))
              left
              right
              substitutions
              *false*
              nil
              index)))))

(defun eq-reduce-to-true-instantiate
  (formula substitutions instantiations index)
  (let ((test (if-test formula))
	(left (if-left formula))
	(right (if-right formula))
	(variables (car instantiations))
        (result nil)
        (result2 nil))
    (cond ((null variables)			;already instantiated
	   (and (eq-reduce-to-true formula substitutions index)
		instantiations))
	  ((false-p right)
	   (and (not (false-p left))
                (setq result (eq-reduce-formula
                              test substitutions *true* instantiations
                              (if-test-index)))
                (setq result2 (eq-reduce-formula
                               left
                               (if (equal result instantiations)
                                   substitutions
                                 (append (cdr result) substitutions))
                               *true* result (if-left-index)))
                (progn (push-proof-log 'if-true index) result2)))
	  ((false-p left)
	   (and (setq result
                      (cond ((bool-p test)
                             (eq-reduce-formula
                              test substitutions *false* instantiations
                              (if-test-index)))
                            (t
			     (push-proof-log 'if-test index)
                             (eq-reduce-formula
                              (make-= test *true*) substitutions *false*
                              instantiations (if-test-index)))))
                (setq result2 (eq-reduce-formula
                               right
                               (if (equal result instantiations)
                                   substitutions
                                 (append (cdr result) substitutions))
                               *true* result (if-right-index)))
                (progn (push-proof-log 'if-false index) result2)))
	  ((true-p left)
	   (cond ((true-p right)
                  (push-proof-log 'if-equal index) instantiations)
		 ((let ((proof-log (save-proof-log)))
                    (or (setq result
                              (eq-reduce-formula
                               test substitutions *true* instantiations
                               (if-test-index)))
                        (progn (restore-proof-log proof-log) nil)))
                  (push-proof-log 'if-true index) result)
		 ((setq result
                        (eq-reduce-formula
                         right substitutions *true* instantiations
                         (if-right-index)))
		  (push-proof-log 'if-equal index) result)))
	  ((true-p right)
	   (cond ((let ((proof-log (save-proof-log)))
                    (or (setq result
                              (eq-reduce-formula
                               (if (bool-p test)
                                   test
                                 (progn
				   (push-proof-log 'if-test index)
                                   (make-= test *true*)))
                               substitutions *false* instantiations
                               (if-test-index)))
                        (progn (restore-proof-log proof-log) nil)))
		  (push-proof-log 'if-false index) result)
		 ((setq result
                        (eq-reduce-formula
                         left substitutions *true* instantiations
                         (if-left-index)))
		  (push-proof-log 'if-equal index) result)))
	  (t (eq-reduce-if-parts
              (eq-reduce-formula test substitutions nil nil (if-test-index))
              left right substitutions *true* instantiations index)))))

(defun eq-reduce-to-false-instantiate
  (formula substitutions instantiations index)
  (let ((test (if-test formula))
	(left (if-left formula))
	(right (if-right formula))
	(variables (car instantiations))
        (result nil)
        (result2 nil))
    (cond ((null variables)			;already instantiated
	   (and (eq-reduce-to-false formula substitutions index)
		instantiations))
	  ((false-p right)
	   (cond ((false-p left)
                  (push-proof-log 'if-equal index) instantiations)
		 ((let ((proof-log (save-proof-log)))
                    (or (setq result
                              (eq-reduce-formula
                               (if (bool-p test)
                                   test
                                 (progn
				   (push-proof-log 'if-test index)
                                   (make-= test *true*)))
                               substitutions *false* instantiations
                               (if-test-index)))
                        (progn (restore-proof-log proof-log) nil)))
		  (push-proof-log 'if-false index) result)
		 ((setq result
                        (eq-reduce-formula
                         left substitutions *false* instantiations
                         (if-left-index)))
		  (push-proof-log 'if-equal index) result)))
	  ((false-p left)
	   (cond ((let ((proof-log (save-proof-log)))
                    (or (setq result
                              (eq-reduce-formula
                               test substitutions *true* instantiations
                               (if-test-index)))
                        (progn (restore-proof-log proof-log) nil)))
		  (push-proof-log 'if-true index) result)
		 ((setq result
                        (eq-reduce-formula
                         right substitutions *false* instantiations
                         (if-right-index)))
		  (push-proof-log 'if-equal index) result)))
	  ((true-p left)
	   (and (not (true-p right))
                (setq result
                      (eq-reduce-formula
                       test substitutions *false* instantiations
                       (if-test-index)))
                (setq result2
                      (eq-reduce-formula
                       right
                       (if (equal result instantiations)
                           substitutions
                         (append (cdr result) substitutions))
                       *false* result (if-right-index)))
                (progn (push-proof-log 'if-false index) result2)))
	  ((true-p right)
           (and (setq result
                      (eq-reduce-formula
                       test substitutions *true* instantiations
                       (if-test-index)))
                (setq result2
                      (eq-reduce-formula
                       left
                       (if (equal result instantiations)
                           substitutions
                         (append (cdr result) substitutions))
                       *false* result (if-left-index)))
                (progn (push-proof-log 'if-true index) result2)))
	  (t (eq-reduce-if-parts
              (eq-reduce-formula test substitutions nil nil (if-test-index))
              left right substitutions *false* instantiations index)))))

;;; Only used for short-circuiting (predicate is (TRUE) or (FALSE)).
(defun eq-reduce-instantiate-reduce
       (test left right substitutions predicate instantiations flagp index)
  (let ((variables (car instantiations)))	;variables for instantiation
    (multiple-value-bind (alist success)
	(if flagp
            (match-true-formula variables test (if-test-index))
          (cond ((bool-p test)
                 (match-false-formula variables test (if-test-index)))
                (t
		 (push-proof-log 'if-test index)
                 (match-false-formula
                  variables (make-= test *true*) (if-test-index)))))
      (when success
	 (let ((result
                (eq-reduce-formula
                 (if flagp left right)
                 (append alist substitutions)
                 predicate
                 (update-instantiations alist instantiations)
                 (if flagp (if-left-index) (if-right-index)))))
	   (when result
	     (if flagp (push-proof-log 'if-true index)
	       (push-proof-log 'if-false index)))
	   result)))))

;;; An instantiations object consists of a list of to-be-instantiated
;;; variables (car of the object) and a list of instantiations already
;;; determined (cdr of the object). Instantiation objects are used
;;; to support the Gallier-Book scheme.

;;; Update an instantiations object with new instantiations. Add the new
;;; instantiations (alist) to the instantiations part and remove the
;;; variables instantiated from the to-be-instantiated part.
(defun update-instantiations (alist instantiations)
  (when instantiations
    (let ((variables (car instantiations))
	  (instantiations (cdr instantiations)))
      (cons (remove-if #'(lambda (u) (assoc-eq u alist)) variables)
	    (append alist instantiations)))))

;;; ============ End of Reducers for Subgoals


;;; ============ Reducer for IF Expressions without Normalization
;;;              (except trivial ones).

;;; No continuations here since they are used for normalization.

;;; if-normalization-trivial-p (test left right) expects test to be an if-term,
;;; and returns T if the result of normalization duplicates only (TRUE) or
;;; (FALSE).  The patterns accepted are (k1 and k2 are (TRUE) or (FALSE)):
;;;  (IF (IF _ (TRUE) _) k1 _)
;;;  (IF (IF _ _ (TRUE)) k1 _)
;;;  (IF (IF _ (FALSE) _) _ k1)
;;;  (IF (IF _ _ (FALSE)) _ k1)
;;;  (IF (IF t l r) k1 k2) ; pushes coercion/negation to l and r.
;;;  (IF (IF t k1 k2) l r) ; remove coercion or flip l and r.

(defun if-normalization-trivial-p (test left right)
  (let ((test-left (if-left test))
	(test-right (if-right test)))
    (or (and (or (true-p test-left) (true-p test-right))
	     (or (true-p left) (false-p left)))
	(and (or (false-p test-left) (false-p test-right))
	     (or (true-p right) (false-p right)))
	(and (or (true-p left) (false-p left))
    	     (or (true-p right) (false-p right)))
	(and (or (true-p test-left) (false-p test-left))
    	     (or (true-p test-right) (false-p test-right))))))

(defun make-if-from-trivial-normalization (test left right index)
  (cond ((true-p test)
         (push-proof-log 'if-true index)
         left)
        ((false-p test)
         (push-proof-log 'if-false index)
         right)
        (t (make-if test left right))))

;;; Reduce IF without normalization (except trivial ones). It is called
;;; only if predicate is non-nil or *reduce-normalizes-flag* is nil.

(defun eq-reduce-if-formula-without-normalization
  (formula substitutions predicate instantiations index)
  (cond ((null predicate)			;no short circuiting
	 (cond ((and (if-p (if-test formula))
                     (if-normalization-trivial-p (if-test formula)
                                                 (if-left formula)
                                                 (if-right formula)))
                ;; normalize anyway if trivial normalization
		(incf (stat-normalization *reduce-statistics*))
		(push-proof-log 'case-analysis index 1)
		(eq-reduce-if-formula-without-normalization
		  (make-if (if-test (if-test formula))
			   (make-if-from-trivial-normalization
                            (if-left (if-test formula))
                            (if-left formula)
                            (if-right formula)
                            (if-left-index))
			   (make-if-from-trivial-normalization
                            (if-right (if-test formula))
                            (if-left formula)
                            (if-right formula)
                            (if-right-index)))
		  substitutions nil nil index))
	       (t (eq-reduce-if-parts
                   (eq-reduce-formula
                    (if-test formula) substitutions nil nil (if-test-index))
                   (if-left formula)
                   (if-right formula)
                   substitutions
                   nil
                   nil
                   index))))
	((null instantiations)     ;short circuit, no instantiation
	 (cond ((true-p predicate)   ;want *true* to be the reduced result
		(eq-reduce-to-true formula substitutions index))
	       ((false-p predicate)  ;want *false* to be the reduced result
		(eq-reduce-to-false formula substitutions index))
	       (t (error
                   "Attempt to short circuit to other than true or false."))))
	((true-p predicate)        ;want *true* possibly with instantiation
	 (eq-reduce-to-true-instantiate
          formula substitutions instantiations index))
	((false-p predicate)       ;want *false* possibly with instantiation
	 (eq-reduce-to-false-instantiate
          formula substitutions instantiations index))
	(t (error "Attempt to short circuit to other than true or false."))))

;;; ============ End of Reducer for IF Expressions without Normalization


;;; ============ Main Reducer for IF Expressions


;;; Reduce an "IF" where the test has been reduced, but not the left and
;;; right branches.
(defun eq-reduce-if-parts
  (test left right substitutions predicate instantiations index)
  (cond ((true-p test)
	 (push-proof-log 'if-true index)
	 (eq-reduce-formula left substitutions predicate instantiations index))
	((false-p test)
	 (push-proof-log 'if-false index)
	 (eq-reduce-formula
          right substitutions predicate instantiations index))
	((and (not *reduce-normalizes-flag*) (if-p test))
	 (cond
	  ((and (false-p (if-left test)) (true-p (if-right test)))
	   (log-if-negate-test index)
	   (eq-reduce-if-parts (if-test test)
			       right
			       left
			       substitutions
			       predicate
			       instantiations
			       index))
	  ((if-normalization-trivial-p test left right)
	   (eq-reduce-normalize-if-parts test
					 left
					 right
					 substitutions
					 predicate
					 instantiations
					 index))
	  ((null predicate)
	   (multiple-value-bind (left right)
	     (with-assumed-true-then-false
	      (test)
	      (eq-reduce-formula
	       left substitutions nil instantiations (if-left-index))
	      (eq-reduce-formula
	       right substitutions nil instantiations (if-right-index)))
	     (eq-final-reduce-if-parts test left right index)))
	  (t (let ((proof-log (save-proof-log)))
	       (if (and (with-assumed-true (test)
			  (eq-reduce-formula
			   left substitutions predicate instantiations
			   (if-left-index)))
			(with-assumed-false (test)
			  (eq-reduce-formula
			   right substitutions predicate instantiations
			   (if-right-index))))
		   (progn
		     (push-proof-log 'if-equal index)
		     t)
		   (progn (restore-proof-log proof-log) nil))))))
	((let ((proof-log (save-proof-log)))
           (or (and (not (bool-p test))
                    (progn
		      (push-proof-log 'if-test index)
                      (eq (eq-lookup (make-= test *true*) (if-test-index))
                          *false*)))
               (progn (restore-proof-log proof-log) nil)))
	 (push-proof-log 'if-false index)
	 (eq-reduce-formula
          right substitutions predicate instantiations index))
	((null predicate)
	 (multiple-value-bind (left right)
	     (with-assumed-true-then-false
              (test)
              (eq-reduce-formula
               left substitutions nil instantiations (if-left-index))
              (eq-reduce-formula
               right substitutions nil instantiations (if-right-index)))
	   (eq-final-reduce-if-parts test left right index)))
	((or (null instantiations) (null (car instantiations)))	;no variables?
	 (cond
	  ((true-p predicate)
	   (cond
	    ((or (false-p left) (false-p right)) nil)	;can't be (TRUE)
	    (t (and (or (true-p left)
			(with-assumed-true (test)
					   (eq-reduce-formula
					    left substitutions *true* nil
					    (if-left-index))))
		    (or (true-p right)
			(with-assumed-false (test)
					    (eq-reduce-formula
					     right substitutions *true* nil
					     (if-right-index))))
		    (progn (push-proof-log 'if-equal index)
			   (or instantiations t))))))
	  ((false-p predicate)
	   (cond
	    ((or (true-p left) (true-p right)) nil)	;can't be (FALSE)
	    (t (and (or (false-p left)
			(with-assumed-true (test)
					   (eq-reduce-formula
					    left substitutions *false* nil
					    (if-left-index))))
		    (or (false-p right)
			(with-assumed-false (test)
					    (eq-reduce-formula
					     right substitutions *false* nil
					     (if-right-index))))
		    (progn (push-proof-log 'if-equal index)
			   (or instantiations t))))))
	  (t (error
	      "Attempt to short circuit to other than (TRUE) or (FALSE)."))))
	(t (eq-reduce-if-parts-instantiate
	    test left right substitutions predicate instantiations index))))


(defun eq-reduce-if-parts-instantiate
  (test left right substitutions predicate instantiations index)
  (cond ((true-p predicate)
	 (cond ((false-p right)
		(eq-reduce-instantiate-reduce
		  test left right substitutions *true* instantiations t index))
	       ((false-p left)
		(eq-reduce-instantiate-reduce
		  test left right substitutions *true* instantiations nil
                  index))
	       (t (or (eq-reduce-instantiate-reduce
			test left right substitutions *true* instantiations
                        t index)
		      (eq-reduce-instantiate-reduce
			test left right substitutions *true* instantiations
                        nil index)))))
	((false-p predicate)
	 (cond ((true-p right)
		(eq-reduce-instantiate-reduce
		  test left right substitutions *false* instantiations
                  t index))
	       ((true-p left)
		(eq-reduce-instantiate-reduce
		  test left right substitutions *false* instantiations
                  nil index))
	       (t (or (eq-reduce-instantiate-reduce
			test left right substitutions *false* instantiations
                        t index)
		      (eq-reduce-instantiate-reduce
			test left right substitutions *false* instantiations
                        nil index)))))
	(t (error "Attempt to short circuit to other than true or false."))))


;;; Normalize the IF formula given in three parts. The test is assumed
;;; to be already reduced but not the left and right. Furthermore,
;;; the test is assumed to be an IF, thus the formula requires normalization.
;;; This is only called when normalization is turned off.
(defun eq-reduce-normalize-if-parts
  (test left right substitutions predicate instantiations index)
  (incf (stat-normalization *reduce-statistics*))
  (push-proof-log 'case-analysis index 1)
  (let ((test-test (if-test test)))
    (cond ((null predicate)
	   (multiple-value-bind (left right)
	       (with-assumed-true-then-false (test-test)
                 (progn (intern-expressions (if-left test))
                        (eq-reduce-if-parts
                         (if-left test) left right substitutions nil nil
                         (cons 2 index)))
                 (progn (intern-expressions (if-right test))
                        (eq-reduce-if-parts
                         (if-right test) left right substitutions nil nil
                         (cons 3 index))))
	     (eq-final-reduce-if-parts test-test left right index)))
	  ((or (null instantiations) (null (car instantiations)))
           ;; no variables
	   (and (with-assumed-true (test-test)
                  (intern-expressions (if-left test))
                  (eq-reduce-if-parts
                   (if-left test) left right substitutions predicate
                   instantiations (cons 2 index)))
                (with-assumed-false (test-test)
                  (intern-expressions (if-right test))
                  (eq-reduce-if-parts
                   (if-right test) left right substitutions predicate
                   instantiations (cons 3 index)))))
	  
	  (t (let ((variables (car instantiations)))
               ;; variables for instantiation
	       (multiple-value-bind (alist success)
		   (match-true-formula variables test-test (if-test-index))
		 (if success
		     (eq-reduce-if-parts
                      (if-left test) left right
                      (append alist substitutions)
                      predicate
                      (update-instantiations alist instantiations)
                      (cons 2 index))
		     (multiple-value-bind (alist success)
			 (cond ((bool-p test-test)
                                (match-false-formula
                                 variables test-test (if-test-index)))
                               (t
				(push-proof-log 'if-test index)
                                (match-false-formula
                                 variables (make-= test-test *true*)
                                 (if-test-index))))
		       (and success
			    (eq-reduce-if-parts
			      (if-right test) left right
			      (append alist substitutions)
			      predicate
			      (update-instantiations alist instantiations)
			      (cons 3 index)))))))))))

;;; Attempt 2 possible final reductions on an IF expression:
;;; - removal of Boolean coercion, or
;;; - (IF test expr expr) => expr.
(defun eq-final-reduce-if-parts (test left right index)
  (cond ((and (true-p left) (false-p right) (bool-p test))
	 (push-proof-log 'is-boolean index t)
	 test)
	((eq-equal left right index)  ;use simplifier
	 (push-proof-log 'if-equal index)
	 right)
	(t (make-if test left right))))

;;; ============ End of Main Reducer for IF Expressions


;;; ============ Reducer for Quantifications

;;; Redundant quantifiers are eliminated and case analysis performed.

(defun eq-reduce-eliminate-quantifiers (formula substitutions index)
  (cond ((all-p formula)
	 (let ((expr (eq-reduce-eliminate-quantifiers
		       (all-expr formula) substitutions (cons 2 index))))
	   (cond ((occurs-in (all-var formula) expr)
		  (make-all (all-vars formula) expr))
		 (t (push-proof-log 'remove-universal index)
		    (coerce-to-bool expr index)))))
 	((some-p formula)
	 (let ((expr (eq-reduce-eliminate-quantifiers
		       (some-expr formula) substitutions (cons 2 index))))
	   (cond ((occurs-in (some-var formula) expr)
		  (make-some (some-vars formula) expr))
		 (t (log-remove-existential index)
		    (coerce-to-bool expr index)))))
	(t (eq-reduce-formula formula substitutions nil nil index))))

;;; Perform the final reductions on a quantified formula.
;;; If no quantifier case analysis is being performed then just do a lookup
;;; otherwise case analysis is performed and further reduce new result.
(defun eq-reduce-quantifier-cases (formula predicate instantiations index)
  (if *reduce-does-quantifier-case-analysis-flag*
      (multiple-value-bind (formula success)
	  (perform-quantifier-case-analysis formula index)
        (cond (success				;needs re-simplification
               ;; we probably don't need case analysis again
               (let ((*reduce-does-quantifier-case-analysis-flag* nil))
                 (eq-reduce-formula
                  formula nil predicate instantiations index)))
              ((or (all-p formula) (some-p formula))
               (let ((result (apply-one-point-rule formula index)))
                 (cond (result (eq-reduce-formula
                                result nil predicate instantiations index))
                       (t (when *reduce-collects-quantifiers-flag*
                            (setq formula (collect-quantifiers formula index)))
                          (result-of (eq-lookup formula index)
                                     predicate instantiations)))))
              (t (result-of formula predicate instantiations))))
    ;; If the result is still quantified then try the one-point rule
    ;; and lookup. We don't apply rules here (rewriting quantifiers
    ;; is disallowed).
    (cond ((or (all-p formula) (some-p formula))
           (let ((result (apply-one-point-rule formula index)))
             (cond (result (eq-reduce-formula
                            result nil predicate instantiations index))
                   (t (when *reduce-collects-quantifiers-flag*
                        (setq formula (collect-quantifiers formula index)))
                      (result-of (eq-lookup formula index)
                                 predicate instantiations)))))
          (t (result-of formula predicate instantiations)))))

(defun collect-quantifiers (formula index)
  (cond ((all-p formula)
	 (make-all (all-vars formula)
		   (collect-quantifiers-aux
                    'all (all-expr formula) (all-expr-index)
		    (make-context-for-bool-p formula index))))
	((some-p formula)
	 (make-some (some-vars formula)
		    (collect-quantifiers-aux
                     'some (some-expr formula) (some-expr-index)
		     (make-context-for-bool-p formula index))))
	(t formula)))

(defun collect-quantifiers-aux (kind formula index bool-p)
  (cond ((all-p formula)
         (if (eq kind 'all)
             (make-all (all-vars formula)
                       (collect-quantifiers-aux
                        'all (all-expr formula) (all-expr-index)
			(make-context-for-bool-p formula index)))
           formula))
	((some-p formula)
         (if (eq kind 'some)
             (make-some (some-vars formula)
                        (collect-quantifiers-aux
                         'some (some-expr formula) (some-expr-index)
			 (make-context-for-bool-p formula index)))
           formula))
	((if-p formula)
	 (let ((test (if-test formula))
	       (left (collect-quantifiers-aux
                      kind (if-left formula) (if-left-index) bool-p))
	       (right (collect-quantifiers-aux
                       kind (if-right formula) (if-right-index) bool-p))
               (opp (if (eq kind 'all) 'some 'all)))
	   (cond ((or (false-p left) (true-p right))
		  (let ((normalized-test
                         (collect-quantifiers-aux
			  opp test (if-test-index)
			  (make-context-for-bool-p
			   (make-if test left right) index))))
                    (move-out-of-test
		     kind normalized-test left right index bool-p)))
                 (t (move-out-phase-2 kind test left right index bool-p)))))
	(t formula)))

;;; left is (FALSE) or right is (TRUE)
;;; Only move quantifiers out of test if they become the opposite kind.
;;; Should we move quantifiers out of test for the same kind (when
;;; left is (TRUE) or right is (FALSE))?

(defun move-out-of-test (kind test left right index bool-p)
  (cond ((and (all-p test) (eq kind 'some)
	      (not (occurs-in (all-var test) left))
              (not (occurs-in (all-var test) right)))
	 (cond ((false-p left)
		;; (if (all () ...) (false) right)
		(log-coerce-expr-for-boolean-or-bool-p
		 right (if-right-index) bool-p)
		(log-some-uncase-analysis-3
		 (make-if test left (make-if right *true* *false*)) index))
	       ((true-p right)
		(log-coerce-expr-for-boolean-or-bool-p
		 left (if-left-index) bool-p)
		(log-introduce-existential (all-vars test) (if-left-index))
		(log-some-uncase-analysis-4 index)))
         (make-some (all-vars test)
                    (move-out-of-test
                     'some (all-expr test) left right (some-expr-index)
		     (make-context-for-bool-p
		      (make-some (all-vars test) *true*) index))))
        ((and (some-p test) (eq kind 'all)
              (not (occurs-in (some-var test) left))
              (not (occurs-in (some-var test) right)))
	 (cond ((false-p left)
		(log-coerce-expr-for-boolean-or-bool-p
		 right (if-right-index) bool-p)
		(push-proof-log 'remove-universal (if-right-index)
				(some-vars test) t)
		(log-all-uncase-analysis-5
		 (make-if test left (make-all (some-vars test) right)) index))
	       ((true-p right)
		(log-coerce-expr-for-boolean-or-bool-p
		 left (if-left-index) bool-p)
		(log-all-uncase-analysis-2
		 (make-if test (make-if left *true* *false*) right) index)))
         (make-all (some-vars test)
                   (move-out-of-test
                    'all (some-expr test) left right (all-expr-index)
		    (make-context-for-bool-p
		     (make-all (some-vars test) *true*) index))))
        (t (move-out-phase-2 kind test left right index bool-p))))

(defun move-out-phase-2 (kind test left right index bool-p)
  (cond ((and (all-p left) (eq kind 'all)
              (not (occurs-in (all-var left) test))
              (not (occurs-in (all-var left) right)))
	 (log-coerce-expr-for-boolean-or-bool-p right (if-right-index) bool-p)
	 (push-proof-log 'remove-universal (if-right-index) (all-vars left) t)
	 (log-all-uncase-analysis-1
	  (make-if test left (make-all (all-vars left) right)) index)
         (make-all (all-vars left)
                   (move-out-phase-2
                    'all test (all-expr left) right (all-expr-index)
		    (make-context-for-bool-p
		     (make-all (all-vars left) *true*) index))))
        ((and (some-p left) (eq kind 'some)
              (not (occurs-in (some-var left) test))
              (not (occurs-in (some-var left) right)))
	 (log-coerce-expr-for-boolean-or-bool-p right (if-right-index) bool-p)
	 (log-introduce-existential (some-vars left) (if-right-index))
	 (log-some-uncase-analysis-1
	  (make-if test left (make-some (some-vars left) right)) index)
         (make-some (some-vars left)
                    (move-out-phase-2
                     'some test (some-expr left) right (some-expr-index)
		     (make-context-for-bool-p
		      (make-some (some-vars left) *true*) index))))
        (t (move-out-phase-3 kind test left right index bool-p))))

(defun move-out-phase-3 (kind test left right index bool-p)
  (cond ((and (all-p right) (eq kind 'all)
              (not (occurs-in (all-var right) test))
              (not (occurs-in (all-var right) left)))
	 (log-coerce-expr-for-boolean-or-bool-p left (if-left-index) bool-p)
	 (push-proof-log 'remove-universal (if-left-index) (all-vars right) t)
	 (log-all-uncase-analysis-1
	  (make-if test (make-all (all-vars right) left) right) index)
         (make-all (all-vars right)
                   (move-out-phase-3
                    'all test left (all-expr right) (all-expr-index)
		    (make-context-for-bool-p
		     (make-all (all-vars right) *true*) index))))
        ((and (some-p right) (eq kind 'some)
              (not (occurs-in (some-var right) test))
              (not (occurs-in (some-var right) left)))
	 (log-coerce-expr-for-boolean-or-bool-p left (if-left-index) bool-p)
	 (log-introduce-existential (some-vars right) (if-left-index))
	 (log-some-uncase-analysis-1
	  (make-if test (make-some (some-vars right) left) right) index)
         (make-some (some-vars right)
                    (move-out-phase-3
                     'some test left (some-expr right) (some-expr-index)
		     (make-context-for-bool-p
		      (make-some (some-vars right) *true*) index))))
        (t (make-if test left right))))

;;; ============ End of Reducer for Quantifications



;;; ============ Reducer for Function Applications

;;; This is where the interesting, beyond IF and quantification
;;; stuff, happens.

(defun eq-reduce-cases-or-apply (formula predicate instantiations index
                                          &optional (continuations nil))
  (let ((formula (if *reduce-does-case-analysis-flag*
		     (perform-case-analysis formula index)
		     formula)))
    (if (if-p formula)
	;; case analysis was effective
	;; we can save resimplification of the first if test
	;; while the others require simplification in the new context
        (cond ((or (not *reduce-normalizes-flag*)
                   predicate)
               (eq-reduce-if-parts (if-test formula)
                                   (if-left formula)
                                   (if-right formula)
                                   nil
                                   predicate
                                   instantiations
                                   index))
	      ((null continuations)
               ;; reduce test with initial continuation.
	       (eq-reduce-reduced-formula-continuations
		(if-test formula) instantiations (if-test-index)
		(list (list (if-left formula) (if-right formula) nil))))
	      (t
               ;; since there is continuation, must be an "if"
               ;; within an "if" test, "normalize" and save
               ;; the new branches as additional continuation.
	       (incf (stat-normalization *reduce-statistics*))
	       (push-proof-log 'case-analysis (cdr index) 1)
	       (eq-reduce-reduced-formula-continuations
		(if-test formula) instantiations index
		(cons (list (if-left formula) (if-right formula) nil index)
		      continuations))))
	;; case analysis was ineffective so we just do the apply now
	(eq-apply-anything-formula
         formula predicate instantiations index continuations))))

;;; Try to apply "things" (simplification, rewrite rules and function
;;; invocation) to the formula. If enabled, the cache is first consulted
;;; to avoid redoing work.
(defun eq-apply-anything-formula (formula predicate instantiations index
                                          &optional (continuations nil))
  (cond ((literal-p formula)
         ;; ***** Can this happen?
         (result-of formula predicate instantiations))
	((or continuations (null *reduce-caches-all-results-flag*))
	 (eq-apply-anything-expression formula predicate instantiations index
                                       continuations))
        (t
         (let* ((function (cache-index formula))
                (enabled (let* ((event (get-event function))
                                (slot (get (event-type event) 'enabled)))
                           (and slot (funcall slot event))))
                ;; The key includes whether or not the definition is enabled,
                ;; the mode of reduce (predicate), the instantiations,
		;; as well as the formula itself.
                (key (list enabled predicate instantiations formula)))
           (multiple-value-bind
            (value cache-hit idx log) (get-cache function key)
	    (cond
	     (cache-hit
	      (incf (stat-cache-hit *reduce-statistics*))
	      ;; Insert proof log from cache
	      (setq *proof-log*
		    (append (adjust-proof-log-segment log index idx)
			    *proof-log*))
	      (cond
	       ((null continuations) value)
	       (t (eq-reduce-reduced-formula-continuations
		   value instantiations index continuations))))
	     ((null continuations)
	      (incf (stat-cache-miss *reduce-statistics*))
	      (let* ((saved-proof-log (save-proof-log))
		     (result (eq-apply-anything-expression
			      formula predicate instantiations index)))
		;; Proof log segment is added to cache entry to make
		;; proof logging work with cache turned on.
		(put-cache function key result index
			   (subseq *proof-log* 0
				   (- (length *proof-log*)
				      (length saved-proof-log))))
		result))
	     (t
	      (incf (stat-cache-miss *reduce-statistics*))
	      (eq-apply-anything-expression
	       formula predicate instantiations index continuations))))))))

(defun index-prefix (index ref-index)
  (when (> (length index) (length ref-index))
    (cons (car index) (index-prefix (cdr index) ref-index))))

(defun adjust-proof-log-segment (proof-log-segment index segment-index)
  (loop for entry in proof-log-segment
	collect
	(list* (car entry)
	       (append (index-prefix (second entry) segment-index) index)
	       (cddr entry))))

;;; The workhorse for eq-apply-anything-formula.
(defun eq-apply-anything-expression (formula predicate instantiations index
                                             &optional (continuations nil))
  (let ((formula (eq-lookup formula index
			    (make-context-for-bool-p-continuations
			     continuations index)
			    )))
    ;; No renormalization after a lookup. If the lookup produces something
    ;; new it tends to be normalized anyway.
    (multiple-value-bind (result substitutions success)
	(if *reduce-applies-rules-flag*
	    (eq-apply-rules-formula formula predicate index)
	  (values formula nil nil))
	;; Rewrite rule applied?
      (cond
       (success (eq-reduce-formula
		 result substitutions predicate instantiations index
		 continuations))
       ((atom formula)
	(let ((result (result-of formula predicate instantiations)) 
	      (*maximum-level-of-reduction* (1+ *maximum-level-of-reduction*)))
	  (cond ((null continuations) result)
		(t (eq-reduce-reduced-formula-continuations
		    result instantiations index continuations)))))
       ((or (true-p formula) (false-p formula))
	(cond ((null continuations)
	       (result-of formula predicate instantiations))
	      (t (eq-reduce-reduced-formula-continuations
		  formula instantiations index continuations))))
       (t (multiple-value-bind
	   (result success)
	   (if *reduce-applies-functions-flag*
	       (eq-apply-functions-formula
		formula predicate instantiations index continuations)
	     (values formula nil))
	   ;; Function invoked?
	   (if success
	       result
	     (let ((result
		    (if (or (null instantiations)
			    (null (car instantiations)))
			(progn (incf (stat-apply-fail *reduce-statistics*))
			       (result-of formula predicate instantiations))
		      (multiple-value-bind
		       (alist success)
		       (if (true-p predicate)
			   (match-true-formula
			    (car instantiations) formula index)
			 (match-false-formula
			  (car instantiations) formula index))
		       ;; Instantiations succeeded?
		       (if success
			   (update-instantiations alist instantiations)
			 ;; nothing applied so increment and return
			 (progn (incf (stat-apply-fail *reduce-statistics*))
				(result-of formula predicate
					   instantiations))))))
		   (*maximum-level-of-reduction*
		    (1+ *maximum-level-of-reduction*)))
	       (cond ((null continuations) result)
		     (t (eq-reduce-reduced-formula-continuations
			 result instantiations index continuations)))))))))))


;;; Try to apply rewrite rules. If successful it returns the new formula,
;;; substitutions, and the rule applied. Otherwise it returns the original
;;; formula, nil, and nil.
(defun eq-apply-rules-formula (formula predicate index)
  (loop for rule in (get-rules formula)
	;; only apply rules which are enabled and further don't bother
	;; trying to rewrite to false when we are just performing a predicate
	when (and (rule-enabled rule)
		  (not (event-inaccessible-p rule))
		  ;; *** find out if this optimization is worthwhile
		  (or (null predicate)
		      (and (true-p predicate)
                           (not (false-p (rule-value rule))))
		      (and (false-p predicate)
                           (not (true-p (rule-value rule))))))
	  
	  do		   ;only then try applying the rule
	    (multiple-value-bind (substitutions match-success)
		(match-pattern-formula (rule-pattern rule) formula)
	      (cond ((not match-success) nil)
		    ;; for unconditional rules or those not requiring
                    ;; instantiation
		    ;; we can immediately check the ordering restriction
                    ;; before subgoaling
		    ((and (atom (rule-conditional rule))
			  ;unconditional or no instantiations?
			  (not (eq-should-apply-rule-p
                                rule formula substitutions)))
		     (incf (stat-ordering *reduce-statistics*)))
		    ((not (rule-conditional rule))	;an unconditional rule?
		     (incf (stat-rewrite *reduce-statistics*))
                     (push-proof-log 'marker index
				     (list 'rewrite 'start (rule-name rule)))
		     (log-use-axiom index (internal-name (rule-name rule)))
		     (update-rules rule)	;so return success
                     (let* ((right-index (cons 2 (repeat-all-expr-index
                                                  (length (rule-args rule))
                                                  (if-test-index))))
                            (renamed (conditionally-rename-quantified-variables
                                      (rule-valbound rule)
                                      (rule-value rule)
                                      right-index))
                            (unrenames (mapcar #'(lambda (x)
                                                     (cons (cdr x) (car x)))
                                                 (rule-renames rule)))
                            (unrenamed-substitutions
                             (mapcar #'(lambda (x)
                                         (make-= (binding-of (car x) unrenames)
                                                 (cdr x)))
                                     (reorder-substitutions
                                      substitutions
                                      ;;(sublis-eq (rule-renames rule)
                                      ;;           (rule-args rule))
				      (mapcar #'cdr (rule-renames rule))
				      ))))
                       (when *record-proof-logs-flag*
                         (log-rewrite
                          (make-if (make-series-of-quantification
                                    'all
                                    (mapcar #'=-left unrenamed-substitutions)
                                    (sublis-eq unrenames
                                               (make-= (rule-pattern rule)
                                                       renamed)))
                                   formula
                                   *true*)
                          unrenamed-substitutions
                          index)
                         (log-unrenames (rule-value rule) renamed right-index)
                         (push-proof-log 'use-axiom (if-test-index)
                                         (internal-name (rule-name rule)) t)
                         (push-proof-log 'if-true index)
                         (push-proof-log 'marker index
                                         (list 'rewrite 'end
                                               (sublis-eq substitutions
                                                          renamed))))
                       (return (values renamed substitutions rule))))
		    (t (multiple-value-bind (formula substitutions rule)
                         (eq-apply-rules-formula-conditional
                          formula rule substitutions index)
                         (unless (null rule)
                           (return (values formula substitutions rule)))))))
	finally (return (values formula nil nil))))	;apply failure

(defun eq-apply-rules-formula-conditional (formula rule substitutions index)
  ;; now try to subgoal on the rule instantiating any unbound variables
  ;; if any variables were instantiated then we need to check the ordering
  (let ((pre-subgoal-proof (save-proof))
        (pre-subgoal-proof-log (save-proof-log))
        (right-index (cons 2 (repeat-all-expr-index
                              (length (rule-args rule))
                              (if-test-index)))))
    (push-proof-log 'marker index (list 'rewrite 'start (rule-name rule)))
    (log-use-axiom index (internal-name (rule-name rule)))
    (let ((renamed-subgoal
           (conditionally-rename-quantified-variables
            (rule-subbound rule)
            (rule-subgoal rule)
            (cons 1 right-index)))
          (renamed-value
           (conditionally-rename-quantified-variables
            (rule-valbound rule)
            (rule-value rule)
            (cons 2 right-index))))
      (let ((pre-rewrite-proof-log (save-proof-log))
            instantiations success subgoal-log)
        (let ((*proof-log* nil))
          (multiple-value-setq (instantiations success)
            (eq-reduce-subgoal
             renamed-subgoal
             substitutions
             (and (not (atom (rule-conditional rule)))
                  (rule-conditional rule))
             (if-test-index)))
          (setq subgoal-log (save-proof-log)))
        (cond ((not success) ;subgoal failed?
               (restore-proof pre-subgoal-proof)
               (restore-proof-log pre-subgoal-proof-log)
               (incf (stat-subgoal-fail *reduce-statistics*))
               (values formula nil nil))
              (t (restore-proof-log pre-rewrite-proof-log)
                 (setq substitutions (append instantiations substitutions))
                 (let* ((unrenames (mapcar #'(lambda (x)
                                               (cons (cdr x) (car x)))
                                           (rule-renames rule)))
                        (unrenamed-substitutions
                         (mapcar #'(lambda (x)
                                     (make-= (binding-of (car x) unrenames)
                                             (cdr x)))
                                 (reorder-substitutions
                                  substitutions
                                  ;;(sublis-eq (rule-renames rule)
                                  ;;           (rule-args rule))
				  (mapcar #'cdr (rule-renames rule))
				  ))))
                   (when *record-proof-logs-flag*
                     (log-rewrite
                      (make-if (make-series-of-quantification
                                'all
                                (mapcar #'=-left unrenamed-substitutions)
                                (sublis-eq
                                 unrenames
                                 (make-= (rule-pattern rule)
                                         (make-if renamed-subgoal
                                                  renamed-value
                                                  (rule-pattern rule)))))
                               formula
                               *true*)
                      unrenamed-substitutions
                      index)
                     (log-unrenames (rule-value rule)
                                    renamed-value
                                    (cons 2 right-index))
                     (log-unrenames (rule-subgoal rule)
                                    renamed-subgoal
                                    (cons 1 right-index))
                     (push-proof-log 'use-axiom (if-test-index)
                                     (internal-name (rule-name rule)) t)
                     (push-proof-log 'if-true index)
                     (setq *proof-log*
                           (append (sublis-eq instantiations subgoal-log)
                                   *proof-log*))
                     (push-proof-log 'if-true index))
                   (cond ((and (not (atom (rule-conditional rule)))
                               (not (eq-should-apply-rule-p
                                     rule formula substitutions)))
                          (incf (stat-ordering *reduce-statistics*))
                          (restore-proof pre-subgoal-proof)
                          (restore-proof-log pre-subgoal-proof-log)
                          (values formula nil nil))
                         (t (incf (stat-crewrite *reduce-statistics*))
                            (update-rules rule) ;so return success
                            (push-proof-log 'marker index
                                            (list 'rewrite 'end
                                                  (sublis-eq substitutions
                                                             renamed-value)))
                            (values renamed-value
                                    substitutions
                                    rule) ;next rule
                            )))))))))

(defun reorder-substitutions (substitutions args)
  (mapcar #'(lambda (x) (cons x (binding-of x substitutions))) args))

;;; Return non-nil if the appled rule should actually be applied.
;;; This means either the rule is not a permutative rule or it is a
;;; permutative rule and the ordering restriction is not violated by
;;; the application of the rule..
(defun eq-should-apply-rule-p (rule formula substitutions)
  (or (not (rule-permutative rule))
      ;; permutative rules have to produce an smaller result
      ;; now use lrpo> rather than alphalessp
      (lrpo> formula (sublis-eq substitutions (rule-value rule)) nil)))

;;; Given a subgoal formula, call reduce on it. This is called in
;;; the application of a conditional rewrite rule where the condition
;;; becomes a subgoal.

(defun eq-reduce-subgoal (formula substitutions instantiations index)
  (let ((*maximum-level-of-subgoaling* (1- *maximum-level-of-subgoaling*)))
    
    (cond
     ((< *maximum-level-of-subgoaling* 0)	;depth limit?
      (incf (stat-subgoal-limit *reduce-statistics*))
      (values nil nil))			;just return a nil result
     ((member-equal (list formula substitutions) *current-subgoal-list*)
                                        ;subgoal looping?
      (incf (stat-subgoal-loop *reduce-statistics*))
      (values nil nil))			;then just increment and fail
     (t (let* ((*current-subgoal-list*	;update subgoal list
                (cons (list formula substitutions) *current-subgoal-list*))
               (result (eq-reduce-formula
                        formula substitutions *true* instantiations index)))
          (cond
           ((null result) (values nil nil))	;subgoal proof has failed
           ((atom result) (values nil t))	;success with no instantiations
           (t
            ;; success with instantiations
            ;; instantiate "don't cares" to 0
            (values (append (mapcar #'(lambda (u) (cons u 0)) (car result))
                            (cdr result))
                    t))))))))


;;; Invoke function definition. Formula is a function application where
;;; each of the arguments has already been reduced. It returns two values:
;;; - a suggested value to replace formula,
;;; - an indicator for invoked function (T if invoked function is recursive).

(defun eq-apply-functions-formula (formula predicate instantiations index
                                       &optional (continuations nil))
  (let ((event (get-event (car formula))))
    (cond
     ((or (not (ufunction-p event))		;no definition
          (not (ufunction-enabled event))	;currently disabled
          (event-inaccessible-p event))	;currently inaccessible
      (values formula nil))
     ((or (not (ufunction-recursive event))
          (and *reduce-evaluates-values-flag* (value-p formula)))
      (update-functions event)
      (incf (stat-invocation *reduce-statistics*))
      (values (reduce-suggested-value
	         event formula predicate instantiations index continuations)
              t))
     ;; Decide whether or not we prefer it to the original value.
     (t (let ((pre-suggestion-proof (save-proof))
              (pre-suggestion-proof-log (save-proof-log)))
          (let ((suggested-value		;evaluate general formula
		 (with-function-disabled (event)
		   (reduce-suggested-value
		     event formula predicate instantiations index))))
            (if (null predicate)
                (if (suggested-value-is-better event formula suggested-value)
                    (progn (update-functions event)
                           (incf (stat-invocation *reduce-statistics*))
			   (values
			    (eq-reduce-formula suggested-value nil nil
					       instantiations index
					       continuations)
			    t))
                  (progn (restore-proof pre-suggestion-proof)
                         (restore-proof-log pre-suggestion-proof-log)
                         (incf (stat-suggest-fail *reduce-statistics*))
                         (values formula nil)))
              (values suggested-value t))))))))

;;; Reduce the result of function invocation.
(defun reduce-suggested-value (event formula predicate instantiations index
				     &optional (continuations nil))
  (push-proof-log 'marker index
		  (list 'invoke 'start (ufunction-name event)))
  (let ((renamed (rename-and-log-invocation event formula index)))
    (push-proof-log
     'marker index
     (list 'invoke 'end
	   (sublis-eq (pairlis (ufunction-args event) (cdr formula)) renamed)))
    (eq-reduce-formula renamed
		       (pairlis (ufunction-args event) (cdr formula))
		       predicate
		       instantiations
		       index
		       continuations)))

(defun rename-and-log-invocation  (event formula index)
  (log-use-axiom index (internal-name (ufunction-name event)))
  (let* ((right-index
	  (cons 2 (repeat-all-expr-index (length (ufunction-args event))
					 (if-test-index))))
	 (renamed (conditionally-rename-quantified-variables
		   (ufunction-body-variables event)
		   (ufunction-internal-body event)
		   right-index)))
    (when *record-proof-logs-flag*
      (log-rewrite
       (make-if (make-series-of-quantification
		 'all (ufunction-args event)
		 (make-= (cons (car formula) (ufunction-args event)) renamed))
		formula
		*true*)
       (mapcar #'make-= (ufunction-args event) (cdr formula))
       index)
      (log-unrenames (ufunction-internal-body event) renamed right-index)
      (push-proof-log 'use-axiom (if-test-index)
		      (internal-name (ufunction-name event)) t)
      (push-proof-log 'if-true index))
    renamed))


;;; Return non-nil if the suggested value is better than the original.
;;; The heuristics is based on those of Boyer-Moore.
(defun suggested-value-is-better (event formula suggested-value)
  (or (not (ufunction-recursive event))    ;non-recursive ones always are
      ;; Now check the invocation of recursive functions
      (let ((recursive-calls (list-of-calls (car formula) suggested-value)))
	(or (null recursive-calls)
            ;; Better if the recursion was eliminated
	    ;; or if every recursive call has one of the following properties
	    ;; less complex arguments, more values as arguments,
            ;; or no new terms.
	    (let* ((subs (measured-subset-arguments event (cdr formula)))
		   (values (count-values-list subs))
		   (complexity (complexity-of-list subs)))
	      (every #'(lambda (call)
			 (let ((args (measured-subset-arguments
				      event (cdr call))))
			   (or (> (count-values-list args) values) ;more values
			       (< (complexity-of-list args) complexity)
			       (every #'(lambda (expr)
					  (or
					   (expr-occurs
					    expr *assumed-expressions*)
					   (expr-occurs
					    expr *seen-expressions*)))
				      ;no new terms introduced
				      args))))
		     recursive-calls))))))

;;; Function to compute the "complexity" of a formula.

(defun complexity-of (formula)
  (cond ((atom formula) (if (integerp formula) (abs formula) 0))
        ((if-p formula) (max (complexity-of (if-left formula))
                             (complexity-of (if-right formula))))
        (t (1+ (complexity-of-list formula)))))

(defun complexity-of-list (formula-list)
  (let ((result 0))
    (dolist (element formula-list)
      (incf result (complexity-of element)))
    result))

;;; ============ End of Reducer for Function Applications


;;; ============ The Reducer Interface

;;; The formula is reduced in the context of assumptions already
;;; in deductive database.
(defun reduce-formula-in-context-substitutions (formula substitutions index)
  (incf (stat-call *reduce-statistics*))
  (multiple-value-bind (result proof)		;last minute processing
    ; always set up a new cache
    (with-proof (with-empty-cache
	          (apply-grules *bool-node*)
                  (apply-grules *int-node*)
                  (eq-reduce-formula
                    (minimize-scope-formula formula index)
                    substitutions nil nil index)))
    (let ((success (not (equal formula result))))
      (when success (incf (stat-effective *reduce-statistics*)))
      (values result success proof))))

;;; The deductive database is cleared before reduction of formula
;;; (i.e., empty context).
(defun reduce-formula-substitutions (formula substitutions index)
  (reset-deductive-database)
  (reduce-formula-in-context-substitutions formula substitutions index))

;;; Don't clear deductive database before reduction.
(defun reduce-formula-in-context (formula index)
  (reduce-formula-in-context-substitutions formula nil index))

;;; The standard top level entry. It allows for subexpression modifier.
(defun reduce-formula (formula internal-form index)
  (let ((subexpression-modifier
         (get-subexpression-modifier *current-modifiers*)))
    (cond ((null subexpression-modifier)	; no subexpression selection
	   (reduce-formula-substitutions internal-form nil index))
	  ((eq (car subexpression-modifier) :subexpression)
	   (reduce-formula-subexpression (cdr subexpression-modifier)
                                         internal-form
                                         index))
	  ;; other subexpression selections?
	  )))

(defun reduce-formula-subexpression (subexpr formula index)
  (let ((expr (parse-formula subexpr)))
    (when (not (null expr))
      (multiple-value-bind (result proof)
	;; always set up a new cache since the context may have changed
	(with-proof (with-empty-cache
		      (apply-grules *bool-node*)
		      (apply-grules *int-node*)
		      (eq-reduce-subexpression expr formula index)))
        (let ((success (not (equal formula result))))
          (when success (incf (stat-effective *reduce-statistics*)))
          (values result success proof))))))

(defun eq-reduce-subexpression (subexpr formula index)
  (cond ((equal subexpr formula)
         (eq-reduce-formula formula nil nil nil index))
        ((atom formula) formula) ; can't possibly match
        ((or (all-p formula) (some-p formula))
         (list (first formula) (second formula)
               (eq-reduce-subexpression
                subexpr (third formula) (all-expr-index))))
        ((if-p formula)
         (let ((test (eq-reduce-subexpression
                      subexpr (if-test formula) (if-test-index))))
           (cond ((and *reduce-normalizes-flag* (if-p test))
                  (push-proof-log 'case-analysis index 1)
                  (multiple-value-bind (left right)
                    (with-assumed-true-then-false
                     ((if-test test))
                     (eq-reduce-subexpression-if
                      subexpr (if-left test) (if-left formula)
                      (if-right formula) (if-left-index))
                     (eq-reduce-subexpression-if
                      subexpr (if-right test) (if-left formula)
                      (if-right formula) (if-right-index)))
                    (make-if (if-test test) left right)))
                 (t
                  (multiple-value-bind (left right)
                    (with-assumed-true-then-false
                     (test)
                     (eq-reduce-subexpression
                      subexpr (if-left formula) (if-left-index))
                     (eq-reduce-subexpression
                      subexpr (if-right formula) (if-right-index)))
                    (make-if test left right))))))
        (t (cons (car formula)
                 (loop for expr in (cdr formula)
                       for number = 1 then (+ 1 number)
                       collect
                       (eq-reduce-subexpression
                        subexpr expr (cons number index)))))))

(defun eq-reduce-subexpression-if (subexpr test left right index)
  (cond ((true-p test)
         (push-proof-log 'if-true index)
         (eq-reduce-subexpression subexpr left index))
        ((false-p test)
         (push-proof-log 'if-false index)
         (eq-reduce-subexpression subexpr right index))
        ((if-p test)
         (push-proof-log 'case-analysis index 1)
         (multiple-value-bind (l r)
           (with-assumed-true-then-false
            ((if-test test))
            (eq-reduce-subexpression-if
             subexpr (if-left test) left right (if-left-index))
            (eq-reduce-subexpression-if
             subexpr (if-right test) left right (if-right-index)))
           (make-if (if-test test) l r)))
        (t
         (multiple-value-bind (l r)
           (with-assumed-true-then-false
            (test)
            (eq-reduce-subexpression subexpr left (if-left-index))
            (eq-reduce-subexpression subexpr right (if-right-index)))
           (make-if test l r)))))

;;; Macro to define variations of REDUCE. At the minimum, simplification
;;; is performed although you may specify whether it may or may not
;;; substitute equalities. Rewriting and function invocations are optional.
(defmacro defprover (name equal rewrite invoke)
  `(progn
     'compile					;for other lisps
     (defun ,(intern (string-append name "-FORMULA") *zk-package*)
       (formula internal-formula index)
       (let ((*simplifier-substitutes-equalities-flag* ,equal)
	     (*reduce-applies-rules-flag* ,rewrite)
	     (*reduce-applies-functions-flag* ,invoke))
	 (reduce-formula formula internal-formula index)))
     (defun ,(intern (string-append name "-FORMULA-IN-CONTEXT") *zk-package*)
         (formula index)
       (let ((*simplifier-substitutes-equalities-flag* ,equal)
	     (*reduce-applies-rules-flag* ,rewrite)
	     (*reduce-applies-functions-flag* ,invoke))
	 (reduce-formula-in-context formula index)))))

;;; Just do simplfication, allowing substitutions of equalities.
;;; This generates SIMPLIFY-FORMULA and SIMPLIFY-FORMULA-IN-CONTEXT.
;;; The SIMPLIFY command is defined in commands.lisp.
(defprover simplify t nil nil)

;;; Allow rewriting in addition to simplification.
;;; This generates REWRITE-FORMULA and REWRITE-FORMULA-IN-CONTEXT.
;;; The REWRITE command is defined in commands.lisp.
(defprover rewrite t t nil)
