
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


;;; Main functionalities:
;;; - Expansion/unexpansion of formulas.
;;; - Miscellaneous propositional conversions.
;;; - Proof logging propositional conversions.
;;; - Conjunctive/disjunctive normal forms.
;;; - Conversion to IF form and back (to using logical connectives).
;;; - Undo effects of case analysis.
;;; - Produce nice output.

(proclaim '(special *record-proof-logs-flag*))


;;; ==================== Expand/Unexpand ====================

;;; ----- Expansion

;;; (ALL (X Y) P) => (ALL (X) (ALL (Y) P))
;;; (+ I J K) => (+ I (+ J K))
;;; Quantifiers: ALL, SOME.
;;; Functions: AND, OR, +, *

(defun expand-formula (formula index)
  (cond ((atom formula) formula)
        ((all-p formula)
         (expand-all (all-vars formula)
                     (expand-formula (all-expr formula) (all-expr-index))
                     index))
        ((some-p formula)
         (expand-some (some-vars formula)
                      (expand-formula (some-expr formula) (some-expr-index))
                      index))
        (t
         (let* ((function (expand-formula (car formula) (cons 0 index)))
           (arguments (loop for expr in (cdr formula)
                          for number = 1 then (+ 1 number)
                          collect (expand-formula expr (cons number index)))))
           ;; only symbols expand, and make sure it is a function
           ;; since expand may be called before type checking
           (cond ((and (symbolp function)
                       (function-stub-p (get-event function))
                       (expand-p function))
                  (expand-function function arguments index))
                 (t (cons function arguments)))))))

(defun expand-all (vars expr index)
  (cond ((or (not (consp vars)) (= (length vars) 1))
         (make-all vars expr))
        (t (make-all-single (car vars)
                            (expand-all-aux (cdr vars) expr index)))))

(defun expand-all-aux (vars expr index)
  (cond ((null vars) expr)
        (t (push-proof-log 'syntax index)
           (make-all-single
             (car vars)
             (expand-all-aux (cdr vars) expr (all-expr-index))))))

(defun expand-some (vars expr index)
  (cond ((or (not (consp vars)) (= (length vars) 1))
         (make-some vars expr))
        (t (make-some-single (car vars)
                             (expand-some-aux (cdr vars) expr index)))))

(defun expand-some-aux (vars expr index)
  (cond ((null vars) expr)
        (t (log-expand-some index)
           (make-some-single
             (car vars)
             (expand-some-aux (cdr vars) expr (some-expr-index))))))

(defun expand-function (function arguments index)
  (if (let ((event (get-event function)))
	(and (function-stub-p event)
	     (> (length arguments)
		(length (function-stub-args (get-event function))))))
      (progn
	(push-proof-log 'syntax index)
	(list function
	      (car arguments)
	      (expand-function function (cdr arguments) (cons 2 index))))
    (cons function arguments)))


;;; ----- Unexpansion

(defun unexpand-formula (formula index)
  (cond ((atom formula) formula)
        ((all-p formula)
         (unexpand-all formula index))
        ((some-p formula)
         (unexpand-some formula index))
        (t
         (let* ((function (unexpand-formula (car formula) (cons 0 index)))
                (arguments (loop for expr in (cdr formula)
                                 for number = 1 then (+ 1 number)
                                 collect (unexpand-formula
                                          expr (cons number index)))))
           (cond ((and (symbolp function) (expand-p function))
                  (unexpand-function function arguments index))
		 ((and (eq function 'if)
		       (bool-p (first arguments))
		       (true-p (second arguments))
		       (false-p (third arguments)))
		  (push-proof-log 'is-boolean index t)
		  (first arguments))
                 (t (cons function arguments)))))))

(defun unexpand-all (formula index)
  (let ((result (unexpand-formula (all-expr formula) (all-expr-index))))
    (cond ((all-p result)
	   (push-proof-log 'syntax index t)
	   (make-all (append (all-vars formula) (all-vars result))
                     (all-expr result)))
	  (t (make-all (all-vars formula) result)))))

(defun unexpand-some (formula index)
  (let ((result (unexpand-formula (all-expr formula) (all-expr-index))))
    (cond ((some-p result)
	   (log-unexpand-some index)
	   (make-some (append (some-vars formula) (some-vars result))
		      (some-expr result)))
	  (t (make-some (some-vars formula) result)))))

(defun unexpand-function (function arguments index)
  (unexpand-function-aux function (cons function arguments) index))

(defun unexpand-function-aux (function expr index)
  (cond ((eq function 'and)
	 (really-flatten-ands expr index))
	((eq function 'or)
	 (really-flatten-ors expr index))
	((eq function '+)
	 (really-flatten-+s expr index))
	((eq function '*)
	 (really-flatten-*s expr index))
	(t expr)))

;;; ==================== End of Expand/Unexpand ====================

;;; =============== Miscellaneous Conversions ===============


;;; Logical negation.
(defun negate (formula index bool-p)
  (cond ((true-p formula)
	 (push-proof-log 'syntax index)
	 (push-proof-log 'if-true index)
	 *false*)
	((false-p formula)
	 (push-proof-log 'syntax index)
	 (push-proof-log 'if-false index)
	 *true*)
	((not-p formula)
         (log-not-not index)
	 (coerce-to-bool (not-expr formula) index bool-p))
	(t (make-not formula))))

;;; Make implications easier to read.
(defun make-normalized-implies (left right index)
  (cond ((implies-p right)
	 ;; Avoid nested implies on the right.
	 (log-unnest-implies (implies-right right) index)
	 (make-normalized-implies (make-and left (implies-left right))
				  (implies-right right)
                                  index))
	((or-p right)
	 ;; Avoid disjunction in the conclusion.
         (log-implies-or-to-implies-and (make-implies left right) index)
	 (make-normalized-implies
          (make-and left
                    (negate (or-left right) (cons 2 (implies-left-index))
			    (make-context-for-bool-p
			     (make-and left (make-not (or-left right)))
			     (implies-left-index))))
          (or-right right)
          index))
	(t (make-implies left right))))


;;; =============== End of Miscellaneous Conversions ===============


;;; ========== Proof Logging Propositional Conversion ==========

;;; Logging to convert formula to result where we know that formula
;;; is equivalent to result by propositional simplification.
;;; The trick is to call ls-simplify-formula for something we
;;; know will simplify to (TRUE) and have the bulk of the proof
;;; logging performed by ls-simplify-formula. We just need to
;;; add some "setup" and "cleanup" logs.

(defun log-propositional-conversion (formula result index bool-p)
  ;; Start with formula
  (push-proof-log 'if-equal index result t)
  ;; (if result formula formula)
  (push-proof-log 'if-true (if-left-index) *true* t)
  ;; (if result (if (true) formula (true)) formula)
  (push-proof-log 'if-equal (if-left-index) (make-= result *true*) t)
  ;; (if result (if (= result (true)) (if (true) formula (true)) ... ) formula)
  (push-proof-log 'look-up (list* 1 2 (if-left-index)) result)
  ;; (if result (if (= result (true)) (if result formula (true)) ... ) formula)
  (push-proof-log 'look-up (list* 1 1 (if-left-index)) *true*)
  ;; (if result (if (= (true) (true)) (if result formula (true)) ... ) formula)
  (push-proof-log 'compute (cons 1 (if-left-index)))
  (push-proof-log 'if-true (if-left-index))
  ;; (if result (if result formula (true)) formula)

  ;; (all () ... (all () (if result (if result formula (true)) formula)) ...)
  ;; or
  ;; (if result (if result formula (true)) formula) and formula is boolean
  ;;
  ;; simplifying the (if result formula (true))
  (cond ((true-p
          (ls-simplify-formula
           (if-form-proposition
            (expand-proposition
             (make-if result formula *true*)
             (if-left-index))
            (if-left-index))
           nil nil (if-left-index)
	   (unless (null index)
	     (list
	      (make-all
	       (last (unique (list-of-free-variables-unexpanded formula)))
	       (make-if result (make-if result formula *true*) formula))
	      (list 2)))
	   t))
         ;; (if result (true) formula)
         (push-proof-log 'if-false (if-right-index) *false* t)
         ;; (if result (true) (if (false) (false) formula))
         (push-proof-log 'if-equal (if-right-index)
                         (make-= (make-if result *true* *false*) *false*)
			 t)
         ;; (if result
         ;;     (true)
         ;;     (if (= (if result (true) (false)) (false))
         ;;         (if (false) (false) formula)
         ;;         (if (false) (false) formula)))
         (push-proof-log 'look-up (list* 1 2 (if-right-index))
                         (make-if result *true* *false*))
         ;; (if result
         ;;     (true)
         ;;     (if (= (if result (true) (false)) (false))
         ;;         (if (if result (true) (false)) (false) formula)
         ;;         (if (false) (false) formula)))

	 (cond ((bool-p result)
		(log-look-up-false (list* 1 1 1 (if-right-index))))
	       (t
		(log-coerce-if-test-to-bool (list* 1 1 (if-right-index)))
		(log-look-up-false-for-coercion
		 (list* 1 1 1 (if-right-index)))))
	 
         (push-proof-log 'if-false (list* 1 1 (if-right-index)))
         (push-proof-log 'compute (cons 1 (if-right-index)))
         (push-proof-log 'if-true (if-right-index))
         ;; (if result (true) (if (if result (true) (false)) (false) formula))
	 (log-remove-bool-coercion-from-if-test (if-right-index))
         ;; (if result (true) (if result (false) formula))
         (cond ((false-p
                 (ls-simplify-formula
                  (if-form-proposition
                   (expand-proposition
                    (make-if result *false* formula)
                    (if-right-index))
                   (if-right-index))
                  nil nil (if-right-index)
		  (unless (null index)
		    (list
		     (make-all
		      (last
		       (unique (list-of-free-variables-unexpanded formula)))
		      (make-if result
			       *true*
			       (make-if result *false* formula)))
		     (list 3)))
		  t))
                ;; (if result (true) (false))
                (push-proof-log 'is-boolean index t)
                ;; result
                t)
               (t nil)))
        (t nil)))

;;; Only expand the top-level propositional structure. Used by
;;; log-propositional-conversion.

(defun expand-proposition (formula index)
  (cond
   ((or (not-p formula) (and-p formula) (or-p formula) (implies-p formula))
    (let* ((function (car formula))
           (arguments (loop for expr in (cdr formula)
                            for number = 1 then (+ 1 number)
                            collect
                            (expand-proposition expr (cons number index)))))
      ;; only symbols expand, and make sure it is a function
      ;; since expand may be called before type checking
      (cond ((expand-p function) (expand-function function arguments index))
            (t (cons function arguments)))))
   ((if-p formula)
    (make-if (expand-proposition (if-test formula) (if-test-index))
             (expand-proposition (if-left formula) (if-left-index))
             (expand-proposition (if-right formula) (if-right-index))))
   (t formula)))

;;; Replace outer connectives by if-forms, assuming the top-level
;;; propositional structure is already expanded. Used by
;;; log-propositional-conversion.

(defun if-form-proposition (formula index)
  (cond
   ((not-p formula)
    (let ((expr (if-form-proposition (not-expr formula) (not-expr-index))))
      (push-proof-log 'syntax index)
      (make-if expr *false* *true*)))
   ((or-p formula)
    (let ((left (if-form-proposition (or-left formula) (or-left-index)))
          (right (if-form-proposition (or-right formula) (or-right-index))))
      (push-proof-log 'syntax index)
      (make-if left *true* (make-if right *true* *false*))))
   ((and-p formula)
    (let ((left (if-form-proposition (and-left formula) (and-left-index)))
          (right (if-form-proposition (and-right formula) (and-right-index))))
      (push-proof-log 'syntax index)
      (make-if left (make-if right *true* *false*) *false*)))
   ((implies-p formula)
    (let ((left (if-form-proposition
                 (implies-left formula) (implies-left-index)))
          (right (if-form-proposition
                  (implies-right formula) (implies-right-index))))
      (push-proof-log 'syntax index)
      (make-if left (make-if right *true* *false*) *true*)))
   ((if-p formula)
    (make-if (if-form-proposition (if-test formula) (if-test-index))
             (if-form-proposition (if-left formula) (if-left-index))
             (if-form-proposition (if-right formula) (if-right-index))))
   (t formula)))

;;; ========== End of Proof Logging Propositional Conversion ==========


;;; ========== Conjunctive/Disjunctive Normal Form ==========

;;; Calls cnf/dnf which uses BDDs and the Minato-Morreale technique.
;;; Proof logging is done after the fact using the above
;;; log-propositional-conversion.

(defun conjunctive-normal-form (formula index bool-p)
  (cond ((or (bool-p formula) bool-p)
         ;; must be in boolean context or formula must be boolean
	 (let* ((proof-log (save-proof-log))
		(result (cnf formula)))
           (cond ((or (null *record-proof-logs-flag*)
		      (log-propositional-conversion
		       formula result index bool-p))
                  result)
                 (t (restore-proof-log proof-log)
                    formula))))
        (t formula)))

(defun disjunctive-normal-form (formula index bool-p)
  (cond ((or (bool-p formula) bool-p)
         ;; must be in boolean context or formula must be boolean
	 (let* ((proof-log (save-proof-log))
		(result (dnf formula)))
           (cond ((or (null *record-proof-logs-flag*)
		      (log-propositional-conversion
		       formula result index bool-p))
                  result)
                 (t (restore-proof-log proof-log)
                    formula))))
        (t formula)))

;;; ========== End of Conjunctive/Disjunctive Normal Form ==========


;;; =============== Conversion to IF Form and Back ===============


(defun if-form (formula index)
  (cond
   ((atom formula) formula)
   ((litconst-p formula) formula)
   (t (case
       (car formula)
       (not (let ((expr (if-form (not-expr formula) (not-expr-index))))
	      (push-proof-log 'syntax index)
	      (make-if expr *false* *true*)))
       (or (let ((left (if-form (or-left formula) (or-left-index)))
		 (right (if-form (or-right formula) (or-right-index))))
	     (push-proof-log 'syntax index)
	     (make-if left *true* (make-if right *true* *false*))))
       (and (let ((left (if-form (and-left formula) (and-left-index)))
		  (right (if-form (and-right formula) (and-right-index))))
	      (push-proof-log 'syntax index)
	      (make-if left (make-if right *true* *false*) *false*)))
       (implies (let ((left (if-form (implies-left formula)
				     (implies-left-index)))
		      (right (if-form (implies-right formula)
				      (implies-right-index))))
		  (push-proof-log 'syntax index)
		  (make-if left (make-if right *true* *false*) *true*)))
       (= (let ((left (if-form (=-left formula) (=-left-index)))
		(right (if-form (=-right formula) (=-right-index))))
	    (cond ((true-p left)
		   (log-=-true-left-to-if right index)
		   (make-if right *true* *false*))
		  ((true-p right)
		   (log-=-true-right-to-if index)
		   (make-if left *true* *false*))
		  ((and (false-p left) (bool-p right))
		   (log-=-false-left-to-if right index)
		   (make-if right *false* *true*))
		  ((and (false-p right) (bool-p left))
		   (log-=-false-right-to-if left index)
		   (make-if left *false* *true*))
		  (t (make-= left right)))))
       ;; New definitions of > and <
       (< (progn
	    (log-use-axiom-as-rewrite
	     formula '<.definition
	     `((= |)X| ,(<-left formula)) (= |)Y| ,(<-right formula)))
	     index)
	    (make->= (if-form (<-right formula) (cons 1 index))
		     `(succ ,(if-form (<-left formula) (cons 2 index))))))
       (> (progn
	    (log-use-axiom-as-rewrite
	     formula '>.definition
	     `((= |)X| ,(>-left formula)) (= |)Y| ,(>-right formula)))
	     index)
	    (make->= (if-form (>-left formula) (cons 1 index))
		     `(succ ,(if-form (>-right formula) (cons 2 index))))))
       (<= (progn
	    (log-use-axiom-as-rewrite
	     formula '<=.definition
	     `((= |)X| ,(<=-left formula)) (= |)Y| ,(<=-right formula)))
	     index)
	    (make->= (if-form (<=-right formula) (cons 1 index))
		     (if-form (<=-left formula) (cons 2 index)))))
       (t (loop for expr in formula
		for number = 0 then (+ 1 number)
		collect (if-form expr (cons number index))))))))

;;; Try to obtain a readable proposition that use logical connectives.
(defun non-if-form (formula index bool-p)
  (cond ((atom formula) formula)
	((if-p formula)
	 (let ((test (non-if-form (if-test formula) (if-test-index)
				  (make-context-for-bool-p formula index)))
	       (left (non-if-form (if-left formula) (if-left-index) bool-p))
	       (right (non-if-form (if-right formula) (if-right-index) bool-p)))
	   ;; Some simplification but not too much as to interfere with
	   ;; proof commands.
	   (cond ((true-p test) (push-proof-log 'if-true index) left)
		 ((false-p test) (push-proof-log 'if-false index) right)
		 ;; Don't want this case.
		 ;; ((equal left right) left)
		 ((and (true-p left) (false-p right) (or bool-p (bool-p test)))
		  (log-remove-coercion-for-boolean-or-bool-p test index bool-p)
                  test)
		 ((and (false-p left) (true-p right))
                  (push-proof-log 'syntax index t)
                  (negate test index bool-p))
		 ;; Don't want this case.
		 ;; ((true-p left) (make-or test right))
		 ((false-p right)
		  (cond ((and (if-p left)
			      (true-p (if-left left))
			      (false-p (if-right left)))
                         (push-proof-log 'syntax index t)
			 (make-and test (if-test left)))
                        ((and (and-p left)
                              (= (length left) 3)
                              (true-p (and-right left)))
			 (log-and-true 2 2 (if-left-index))
                         (log-and-1 (if-left-index))
                         (push-proof-log 'syntax index t)
                         (make-and test (and-left left)))
			((or bool-p (bool-p left))
			 (if (bool-p left)
			     (push-proof-log 'is-boolean (if-left-index))
			   (log-coerce-expr-in-boolean-context
			    bool-p (if-left-index)))
                         (push-proof-log 'syntax index t)
                         (make-and test left))
			(t (make-if test left right))))
		 ((true-p right)
                  ;; Avoid nested implies on right.
		  (cond ((implies-p left)
			 (push-proof-log 'is-boolean (if-left-index))
                         (push-proof-log 'syntax index t)
			 (log-unnest-implies (implies-right left) index)
			 (make-normalized-implies
			   (make-and test (implies-left left))
			   (implies-right left)
                           index))
			((and (if-p left)
			      (true-p (if-left left))
			      (false-p (if-right left)))
                         (push-proof-log 'syntax index t)
			 (make-normalized-implies test (if-test left) index))
                        ((and (and-p left)
                              (= (length left) 3)
                              (true-p (and-right left)))
			 (log-and-true 2 2 (if-left-index))
                         (log-and-1 (if-left-index))
                         (push-proof-log 'syntax index t)
                         (make-normalized-implies test (and-left left) index))
			((or bool-p (bool-p left))
			 (if (bool-p left)
			     (push-proof-log 'is-boolean (if-left-index))
			   (log-coerce-expr-in-boolean-context
			    bool-p (if-left-index)))
                         (push-proof-log 'syntax index t)
                         (make-normalized-implies test left index))
			(t (make-if test left right))))
		 ((false-p left)
		  (cond ((and (if-p right)
			      (true-p (if-left right))
			      (false-p (if-right right)))
                         (log-if-to-and-not formula index)
			 (make-and (negate test
					   (and-left-index)
					   (make-context-for-bool-p
					    (make-and (make-not test)
						      (if-test right))
					    index))
                                   (if-test right)))
                        ((and (and-p right)
                              (= (length right) 3)
                              (true-p (and-right right)))
			 (log-and-true 2 2 (if-right-index))
                         (log-and-1 (if-right-index))
                         (log-if-to-and-not
			  (make-if test
				   *false*
				   (make-if (and-left right) *true* *false*))
			  index)
                         (make-and (negate test
					   (and-left-index)
					   (make-context-for-bool-p
					    (make-and (make-not test)
						      (and-left right))
					    index))
                                   (and-left right)))
			((or bool-p (bool-p right))
			 (if (bool-p right)
			     (push-proof-log 'is-boolean (if-right-index))
			   (log-coerce-expr-in-boolean-context
			    bool-p (if-right-index)))
                         (log-if-to-and-not
			  (make-if test *false* (make-if right *true* *false*))
			  index)
                         (make-and (negate test
					   (and-left-index)
					   (make-context-for-bool-p
					    (make-and (make-not test)
						      right)
					    index))
				   right))
			(t (make-if test left right))))
		 ;((equal left (negate right nil)) (make-= left test))
		 ((true-p left)
                  ;; don't make an or in implies
		  (cond ((implies-p right)
			 (push-proof-log 'is-boolean (if-right-index))
			 ;; (if test (true) (if (implies rl rr) (true) (false)))
			 (log-coerce-if-test-to-bool index)
			 (log-bool-coercion-is-double-negation (if-test-index))
			 (push-proof-log 'case-analysis index 1)
			 ;; (if (if test (false) (true))
			 ;;     (if (false)
			 ;;         (true)
			 ;;         (if (implies rl rr) (true) (false)))
			 ;;     (if (true)
			 ;;         (true)
			 ;;         (if (implies rl rr) (true) (false))))
			 (push-proof-log 'if-false (if-left-index))
			 (push-proof-log 'if-true (if-right-index))
			 ;; (if (if test (false) (true))
			 ;;     (if (implies rl rr) (true) (false)))
			 ;;     (true))
			 (push-proof-log 'syntax (if-test-index) t)
			 (push-proof-log 'syntax index t)
			 ;; (implies (not test) (implies rl rr))
                         (let ((expr
				(negate test
					(implies-left-index)
					(make-context-for-bool-p
					 (make-implies (make-not test)
						       (implies-right right))
					 index))))
			   (log-unnest-implies (implies-right right) index)
                           (make-normalized-implies
                            (make-and expr (implies-left right))
                            (implies-right right)
                            index)))
			((and (if-p right)
			      (true-p (if-left right))
			      (false-p (if-right right)))
                         (push-proof-log 'syntax index t)
			 (make-or test (if-test right)))
			((false-p right) (make-if test left right))
                        ((and (and-p right)
                              (= (length right) 3)
                              (true-p (and-right right)))
			 (log-and-true 2 2 (if-right-index))
                         (log-and-1 (if-right-index))
                         (push-proof-log 'syntax index t)
                         (make-or test (and-left right)))
			((or bool-p (bool-p right))
			 (log-coerce-expr-for-boolean-or-bool-p
			  right (if-right-index) bool-p)
			 (push-proof-log 'syntax index t)
                         (make-or test right))
			(t (make-if test left right))))
		 ((and (implies-p right)
                       (or bool-p (bool-p left))
                       (equal left (implies-right right)))
		  ;; (if test left (implies rr left))
		  (log-coerce-expr-for-boolean-or-bool-p
		   left (if-left-index) bool-p)
		  (push-proof-log 'syntax (if-right-index))
		  ;; (if test
		  ;;     (if left (true) (false))
		  ;;     (if rr (if left (true) (false)) (true)))
		  (push-proof-log 'if-true (if-left-index) *true* t)
		  (log-coerce-if-test-to-bool (if-right-index))
		  ;; (if test
		  ;;     (if (true) (if left (true) (false)) (true))
		  ;;     (if (if rr (true) (false))
		  ;;         (if left (true) (false))
		  ;;         (true)))
		  (push-proof-log 'case-analysis index 1 t)
		  ;; (if (if test (true) (if rr (true) (false)))
		  ;;     (if left (true) (false))
		  ;;     (true))
		  (push-proof-log 'syntax (if-test-index) t)
		  (push-proof-log 'syntax index t)
		  ;; (implies (or test rr) left)
		  (make-normalized-implies
                   (make-or test (implies-left right)) left index))
		 (t (make-if test left right)))))	;when nothing else
	;; place the literals on the right hand side
	((>=-p formula)
	 (if (and (literal-p (>=-left formula))
		  (not (literal-p (>=-right formula))))
	     (progn
	       (log-use-axiom-as-inverse-rewrite
		'<=.definition (make-<= (>=-right formula) (>=-left formula))
		formula
		`((= |)X| ,(>=-right formula)) (= |)Y| ,(>=-left formula)))
		index)
	       (make-<= (non-if-form (>=-right formula) (cons 1 index) nil)
			(>=-left formula)))
	   (make->= (non-if-form (>=-left formula) (cons 1 index) nil)
		    (non-if-form (>=-right formula) (cons 2 index) nil))))
        ((all-p formula)
         (make-all (all-vars formula)
                   (non-if-form (all-expr formula) (all-expr-index)
				(make-context-for-bool-p formula index))))
        ((some-p formula)
         (make-some (some-vars formula)
                    (non-if-form (some-expr formula) (some-expr-index)
				 (make-context-for-bool-p formula index))))
	(t (loop for expr in formula
               for number = 0 then (+ 1 number)
               collect (non-if-form expr (cons number index) nil)))))


;;; =============== End of Conversion to IF Form and Back ===============


;;; =============== Undo Effects of Case Analysis ===============


;;; Normalization is a special case of case analysis.
;;; Generally normalization is done as part of simplification.
;;; To obtain a readable result, we often want unnormalization.

;;; (IF p (IF q left right) (IF r left right)) =>
;;;    (IF (IF p q r) left right).
(defun unnormalize-if-form (formula index)
  (cond ((atom formula) formula)
	((if-p formula)
	 (unnormalize-if-parts
          (unnormalize-if-form (if-test formula) (if-test-index))
          (unnormalize-if-form (if-left formula) (if-left-index))
          (unnormalize-if-form (if-right formula) (if-right-index))
          index))
	(t (loop for expr in formula
               for number = 0 then (+ 1 number)
               collect (unnormalize-if-form expr (cons number index))))))

(defun unnormalize-if-parts (test left right index)
  (cond ((and (if-p left) (if-p right)
              (equal (if-left left) (if-left right))
              (equal (if-right left) (if-right right)))
         (push-proof-log 'case-analysis index 1 t)
         (unnormalize-if-parts
          (unnormalize-if-parts
           test (if-test left) (if-test right) (if-test-index))
          (if-left left)
          (if-right right)
          index))
        (t (make-if test left right))))


;;; Undo case analysis involving functions and quantifiers.
;;; Generally to be used as part of the output routines for obtaining
;;; readable output forms.
(defun uncase-analysis-form (formula index)
  (cond ((atom formula) formula)
	((if-p formula)
	 (uncase-analysis-if
          (uncase-analysis-form (if-test formula) (if-test-index))
          (uncase-analysis-form (if-left formula) (if-left-index))
          (uncase-analysis-form (if-right formula) (if-right-index))
          index))
	(t (loop for expr in formula
               for number = 0 then (+ 1 number)
               collect (uncase-analysis-form expr (cons number index))))))

;;; Try to move IFs into function applications and quantifications.
(defun uncase-analysis-if (test left right index)
  (cond	((and (all-p left) (all-p right)
	      (eq (all-var left) (all-var right))
	      (not (occurs-in (all-var left) test)))
         (log-all-uncase-analysis-1 (make-if test left right) index)
	 (make-all (all-vars left)
		   (uncase-analysis-if
                    test (all-expr left) (all-expr right) (all-expr-index))))
	((and (all-p left)
              (bool-p right)
	      (not (occurs-in (all-var left) test))
	      (not (occurs-in (all-var left) right)))
         (push-proof-log 'remove-universal
                         (if-right-index)
                         (all-vars left)
			 t)
         (log-all-uncase-analysis-1
	  (make-if test left (make-all (all-vars left) right)) index)
	 (make-all (all-vars left)
		   (uncase-analysis-if
                    test (all-expr left) right (all-expr-index))))
	((and (some-p left) (some-p right)
	      (eq (some-var left) (some-var right))
	      (not (occurs-in (some-var left) test)))
         (log-some-uncase-analysis-1 (make-if test left right) index)
	 (make-some (some-vars left)
		    (uncase-analysis-if test
                                        (some-expr left)
                                        (some-expr right)
                                        (some-expr-index))))
	((and (some-p left)
              (bool-p right)
	      (not (occurs-in (some-var left) test))
	      (not (occurs-in (some-var left) right)))
         (log-introduce-existential (some-vars left) (if-right-index))
         (log-some-uncase-analysis-1
	  (make-if test left (make-some-single (some-var left) right)) index)
	 (make-some (some-vars left)
		    (uncase-analysis-if
                     test (some-expr left) right (some-expr-index))))
	((and (all-p right)
              (bool-p left)
	      (not (occurs-in (all-var right) test))
	      (not (occurs-in (all-var right) left)))
         (push-proof-log 'remove-universal
                         (if-left-index)
                         (all-vars right)
			 t)
         (log-all-uncase-analysis-1
	  (make-if test (make-all (all-vars right) left) right) index)
	 (make-all (all-vars right)
                   (uncase-analysis-if
                    test left (all-expr right) (all-expr-index))))
	((and (some-p right)
              (bool-p left)
	      (not (occurs-in (some-var right) test))
	      (not (occurs-in (some-var right) left)))
         (log-introduce-existential (some-vars right) (if-left-index))
         (log-some-uncase-analysis-1
	  (make-if test (make-some-single (some-var right) left) right) index)
	 (make-some (some-vars right)
                    (uncase-analysis-if
                     test left (some-expr right) (some-expr-index))))
	((or (atom left) (atom right) (litconst-p left) (litconst-p right)
             (all-p left) (all-p right)
	     (some-p left) (some-p right) (neq (car left) (car right))
	     ;; so hsplit works
	     (equal left right))
	 (make-if test left right))
	(t (push-proof-log 'case-analysis index 0 t)
           (cons (car left)
                 (loop for pair in (pairlis (cdr left) (cdr right))
                     for number = 1 then (+ 1 number)
                     collect (cond ((equal (car pair) (cdr pair))
                                    (push-proof-log
                                     'if-equal (cons number index))
                                    (car pair))
                                   (t (uncase-analysis-if
                                       test (car pair) (cdr pair)
                                       (cons number index)))))))))

;;; =============== End of Undo Effects of Case Analysis ===============


;;; =============== Produce Nice Output ===============

(defvar *unnormalize-if-form-flag* t)

(defvar *uncase-analysis-form-flag* nil)

(defvar *unrename-quantified-variables-flag* t)

(defvar *use-non-if-form-flag* t)

(defun output-form (formula index &optional bool-p)
  (when *unnormalize-if-form-flag*
    (setq formula (unnormalize-if-form formula index)))
  (when *uncase-analysis-form-flag*
    (setq formula (uncase-analysis-form formula index)))
  (when *unrename-quantified-variables-flag*
    ;; the extra rename insures that all branches are uniquely named
    (setq formula (unrename-quantified-variables
                   (rename-quantified-variables formula index) index)))
  (when *use-non-if-form-flag*
    (setq formula (non-if-form formula index bool-p)))
  (unexpand-formula formula index)			;always unexpand
  )

;;; =============== End of Produce Nice Output ===============
