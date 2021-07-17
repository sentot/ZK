
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


(proclaim '(special *instantiation-list* *substitution-list*))


;;; =============== Simple Quantifier Manipulation ===============


;;; Instantiations of quantified variables are performed elsewhere.

;;; Main functionalities
;;; - Support for the PRENEX command.
;;; - Minimizing scope of quantifiers.
;;; - Skolem variables and functions.
;;; - Renaming and unrenaming of quantified variables.
;;; - Miscellaneous utility functions for quantifiers.


;;; ==================== Prenex ====================

;;; ----- Code to do prenexing for the PRENEX command.

;;; We want quantifications to be moved out if they become universals
;;; at the top level and only if they are members of vars or vars is nil.
;;; We assume that quantifications have been expanded.
(defun prenex-all (formula vars bool-p index)
  (prenex-all-aux formula vars nil bool-p index))

(defun prenex-all-aux (formula vars negated bool-p index)
  (cond ((all-p formula)
         (cond ((not negated)
                (let ((expr
                       (prenex-all-aux
                        (all-expr formula) vars negated
			(make-context-for-bool-p formula index)
			(all-expr-index))))
                  (cond ((and (not (null vars))
                              (not (member-eq (all-var formula) vars)))
                         (move-var-in-all expr (all-var formula) vars index))
                        (t (make-all (all-vars formula) expr)))))
               (t formula)))
	((some-p formula)
	 (cond (negated
                (let ((expr
                       (prenex-all-aux
                        (some-expr formula) vars negated
			(make-context-for-bool-p formula index)
			(some-expr-index))))
                  (cond ((and (not (null vars))
                              (not (member-eq (some-var formula) vars)))
                         (move-var-in-some expr (some-var formula) vars index))
                        (t (make-some (some-vars formula) expr)))))
	       (t formula)))
	((if-p formula)
	 (prenex-all-if
	   (if-test formula)
	   (if-left formula)
	   (if-right formula)
           vars
	   negated
	   bool-p
	   index))
	(t formula)))

;;; Before moving quantifiers out of an if expression,
;;; prenex the components first.

(defun prenex-all-if (test left right vars negated bool-p index)
  (let ((prenexed-test
	 (cond ((or (false-p left) (true-p right))
		(prenex-all-aux test vars (not negated)
				(make-context-for-bool-p
				 (make-if test left right) index)
				(if-test-index)))
	       ((or (true-p left) (false-p right))
		(prenex-all-aux test vars negated
				(make-context-for-bool-p
				 (make-if test left right) index)
				(if-test-index)))
	       (t test)))
	(prenexed-left
	 (prenex-all-aux left vars negated bool-p (if-left-index)))
	(prenexed-right
	 (prenex-all-aux right vars negated bool-p (if-right-index))))
    (prenex-all-if-aux
     prenexed-test prenexed-left prenexed-right vars negated bool-p index)))

;;; Try moving quantifiers out of the test first.

(defun prenex-all-if-aux (test left right vars negated bool-p index)
  (if negated
      (cond
       ((all-p test)
	(cond ((and (false-p left)
		    (or (null vars) (member-eq (all-var test) vars))
		    (or (bool-p right) bool-p)
		    (not (occurs-in (all-var test) right)))
	       ;; (if (all vars p) (false) right)
	       (if (bool-p right)
		   (push-proof-log 'is-boolean (if-right-index))
		 (log-coerce-expr-in-boolean-context bool-p (if-right-index)))
	       ;; (if (all vars P) (false) (if right (true) (false)))
	       (log-some-uncase-analysis-3
		(make-if test *false* (make-if right *true* *false*)) index)
	       ;; (some vars (if P (false) right))
	       (make-some
		(all-vars test)
		(prenex-all-if-aux
		 (all-expr test) left right vars negated
		 (make-context-for-bool-p
		  (make-some (all-vars test) *true*) index)
		 (some-expr-index))))
	      ((and (true-p right)
		    (or (null vars) (member-eq (all-var test) vars))
		    (or (bool-p left) bool-p)
		    (not (occurs-in (all-var test) left)))
	       ;; Slightly weak! ***
	       ;; Could extend to handle the case where left is (some vars Q)
	       
	       ;; (if (all vars P) left (true))
	       (if (bool-p left)
		   (push-proof-log 'is-boolean (if-left-index))
		 (log-coerce-expr-in-boolean-context bool-p (if-left-index)))
	       ;; (if (all vars P) (if left (true) (false)) (true))
	       (log-introduce-existential (all-vars test) (if-left-index))
	       ;; (if (all vars P) (some vars left) (true))
	       (log-some-uncase-analysis-4 index)
	       ;; (some vars (if P left (true)))
	       (make-some
		(all-vars test)
		(prenex-all-if-aux
		 (all-expr test) left right vars negated
		 (make-context-for-bool-p
		  (make-some (all-vars test) *true*) index)
		 (some-expr-index))))
	      (t (prenex-all-if-aux-2 test left right vars negated
				      bool-p index))))
       ((some-p test)
	(cond ((and (true-p left)
		    (or (null vars) (member-eq (some-var test) vars))
		    (or (bool-p right) bool-p)
		    (not (occurs-in (some-var test) right)))
	       ;; Slightly weak. ***
	       ;; Could extend to handle the case where right is (some vars Q).
	       
	       ;; (if (some vars P) (true) right)
	       (if (bool-p right)
		   (push-proof-log 'is-boolean (if-right-index))
		 (log-coerce-expr-in-boolean-context bool-p (if-right-index)))
	       ;; (if (some vars P) (true) (if right (true) (false)))
	       (log-introduce-existential (some-vars test) (if-right-index))
	       ;; (if (some vars P) (true) (some vars right))
	       (log-some-uncase-analysis-5
		(make-if test *true* (make-some (some-vars test) right))
		index)
	       ;; (push-proof-log 'some-out-test index)
	       ;; (some vars (if P (true) right))
	       (make-some
		(some-vars test)
		(prenex-all-if-aux
		 (some-expr test) left right vars negated
		 (make-context-for-bool-p
		  (make-some (some-vars test) *true*) index)
		 (some-expr-index))))
	      ((and (false-p right)
		    (or (null vars) (member-eq (some-var test) vars))
		    (or (bool-p left) bool-p)
		    (not (occurs-in (some-var test) left)))
	       ;; (if (some vars P) left (false))
	       (if (bool-p left)
		   (push-proof-log 'is-boolean (if-left-index))
		 (log-coerce-expr-in-boolean-context bool-p (if-left-index)))
	       ;; (if (some vars P) (if left (true) (false)) (false))
	       (log-some-uncase-analysis-2
		(make-if test (make-if left *true* *false*) *false*) index)
	       ;; (push-proof-log 'some-out-test index)
	       ;; (some vars (if P left (false)))
	       (make-some
		(some-vars test)
		(prenex-all-if-aux
		 (some-expr test) left right vars negated
		 (make-context-for-bool-p
		  (make-some (some-vars test) *true*) index)
		 (some-expr-index))))
	      (t (prenex-all-if-aux-2 test left right vars negated
				      bool-p index))))
       (t (prenex-all-if-aux-2 test left right vars negated bool-p index)))
    (cond
     ((all-p test)
      (cond ((and (true-p left)
		  (or (null vars) (member-eq (all-var test) vars))
		  (or (bool-p right) bool-p)
		  (not (occurs-in (all-var test) right)))
	     ;; (if (all vars P) (true) right)
	     ;; First, need to transform right to (if right (true) (false))
	     ;; to match pattern for log-all-uncase-analysis-3
	     (if (bool-p right)
		 (push-proof-log 'is-boolean (if-right-index))
	       (log-coerce-expr-in-boolean-context bool-p (if-right-index)))
	     ;; (if (all vars P) (true) (if right (true) (false)))
	     (log-all-uncase-analysis-3
	      (make-if test *true* (make-if right *true* *false*)) index)
	     ;; (all vars (if P (true) right))
	     (make-all
	      (all-vars test)
	      (prenex-all-if-aux
	       (all-expr test) left right vars negated
	       (make-context-for-bool-p	(make-all (all-vars test) *true*) index)
	       (all-expr-index))))
	    ((and (false-p right)
		  (or (null vars) (member-eq (all-var test) vars))
		  (or (bool-p left) bool-p)
		  (not (occurs-in (all-var test) left)))
	     ;; Slightly weak! ***
	     ;; Could extend to handle the case where left is (all vars Q).
	     
	     ;; (if (all vars P) left (false))
	     ;; First, need to transform left to (all vars left) before
	     ;; using all-case-analysis.
	     (if (bool-p left)
		 (push-proof-log 'is-boolean (if-left-index))
	       (log-coerce-expr-in-boolean-context bool-p (if-left-index)))
	     ;; (if (all vars P) (if left (true) (false)) (false))
	     (push-proof-log
	      'remove-universal (if-left-index) (all-vars test) t)
	     ;; (if (all vars P) (all vars left) (false))
	     (push-proof-log 'all-case-analysis index t)
	     ;; (all vars (if P left (false)))
	     (make-all
	      (all-vars test)
	      (prenex-all-if-aux
	       (all-expr test) left right vars negated
	       (make-context-for-bool-p	(make-all (all-vars test) *true*) index)
	       (all-expr-index))))
	    (t (prenex-all-if-aux-2 test left right vars negated
				    bool-p index))))
     ((some-p test)
      (cond ((and (false-p left)
		  (or (null vars) (member-eq (some-var test) vars))
		  (or (bool-p right) bool-p)
		  (not (occurs-in (some-var test) right)))
	     ;; Slightly weak! ***
	     ;; Could extend to handle the case where right is (all vars Q).

	     ;; (if (some vars P) (false) right)
	     (if (bool-p right)
		 (push-proof-log 'is-boolean (if-right-index))
	       (log-coerce-expr-in-boolean-context bool-p (if-right-index)))
	     ;; (if (some vars P) (false) (if right (true) (false)))
	     (push-proof-log 'remove-universal (if-right-index)
			     (some-vars test) t)
	     ;; (if (some vars P) (false) (all vars right))
	     (log-all-uncase-analysis-5
	      (make-if test *false* (make-all (some-vars test) right)) index)
	     ;; (push-proof-log 'some-out-test-negate index)
	     ;; (all vars (if P (false) right))
	     (make-all
	      (some-vars test)
	      (prenex-all-if-aux
	       (some-expr test) left right vars negated
	       (make-context-for-bool-p
		(make-all (some-vars test) *true*) index)
	       (all-expr-index))))
	    ((and (true-p right)
		  (or (null vars) (member-eq (some-var test) vars))
		  (or (bool-p left) bool-p)
		  (not (occurs-in (some-var test) left)))
	     ;; (if (some vars P) left (true))
	     (if (bool-p left)
		 (push-proof-log 'is-boolean (if-left-index))
	       (log-coerce-expr-in-boolean-context bool-p (if-left-index)))
	     ;; (if (some vars p) (if left (true) (false)) (true))
	     (log-all-uncase-analysis-2
	      (make-if test (make-if left *true* *false*) *true*) index)
	     ;; (push-proof-log 'some-out-test-negate index)
	     ;; (all vars (if P left (true)))
	     (make-all
	      (some-vars test)
	      (prenex-all-if-aux
	       (some-expr test) left right vars negated
	       (make-context-for-bool-p
		(make-all (some-vars test) *true*) index)
	       (all-expr-index))))
	    (t (prenex-all-if-aux-2 test left right vars negated
				    bool-p index))))
     (t (prenex-all-if-aux-2 test left right vars negated bool-p index)))))

;;; Then try moving quantifiers out of the left branch.
;;; Slightly weak? Extend to handle cases where left and right
;;; have the same quantification? *****

(defun prenex-all-if-aux-2 (test left right vars negated bool-p index)
  (cond ((and negated
	      (some-p left)
              (or (null vars) (member-eq (some-var left) vars))
	      (or (bool-p right) bool-p)
	      (not (occurs-in (some-var left) test))
	      (not (occurs-in (some-var left) right)))
	 ;; (if test (some vars P) right)
	 (if (bool-p right)
	     (push-proof-log 'is-boolean (if-right-index))
	   (log-coerce-expr-in-boolean-context bool-p (if-right-index)))
	 ;; (if test (some vars P) (if right (true) (false)))
	 (log-introduce-existential (some-vars left) (if-right-index))
	 ;; (if test (some vars P) (some vars right))
	 (log-some-uncase-analysis-1
	  (make-if test left (make-some (some-vars left) right)) index)
	 ;; (push-proof-log 'some-out-left index)
	 ;; (some vars (if test P right))
	 (make-some
	  (some-vars left)
	  (prenex-all-if-aux-2
	   test (some-expr left) right vars negated
	   (make-context-for-bool-p (make-some (some-vars left) *true*) index)
	   (some-expr-index))))
	((and (not negated)
	      (all-p left)
              (or (null vars) (member-eq (all-var left) vars))
	      (or (bool-p right) bool-p)
	      (not (occurs-in (all-var left) test))
	      (not (occurs-in (all-var left) right)))
	 ;; (if test (all vars P) right)
	 (if (bool-p right)
	     (push-proof-log 'is-boolean (if-right-index))
	   (log-coerce-expr-in-boolean-context bool-p (if-right-index)))
	 ;; (if test (all vars P) (if right (true) (false)))
	 (push-proof-log 'remove-universal (if-right-index) (all-vars left) t)
	 ;; (if test (all vars P) (all vars right))
	 (log-all-uncase-analysis-1
	  (make-if test left (make-all (all-vars left) right)) index)
	 ;;; (all vars (if test P right))
	 (make-all
	  (all-vars left)
	  (prenex-all-if-aux-2
	   test (all-expr left) right vars negated
	   (make-context-for-bool-p (make-all (all-vars left) *true*) index)
	   (all-expr-index))))
	(t (prenex-all-if-aux-3 test left right vars negated bool-p index))))

;;; Finally, try moving quantifiers out of the right branch.

(defun prenex-all-if-aux-3 (test left right vars negated bool-p index)
  (cond ((and negated
	      (some-p right)
              (or (null vars) (member-eq (some-var right) vars))
	      (or (bool-p left) bool-p)
	      (not (occurs-in (some-var right) test))
	      (not (occurs-in (some-var right) left)))
	 ;; (if test left (some vars P))
	 (if (bool-p left)
	     (push-proof-log 'is-boolean (if-left-index))
	   (log-coerce-expr-in-boolean-context bool-p (if-left-index)))
	 ;; (if test (if left (true) (false)) (some vars P))
	 (log-introduce-existential (some-vars right) (if-left-index))
	 ;; (if test (some vars left) (some vars P))
	 (log-some-uncase-analysis-1
	  (make-if test (make-some (some-vars right) left) right) index)
	 ;; (push-proof-log 'some-out-right index)
	 ;; (some vars (if test left P))
	 (make-some
	  (some-vars right)
	  (prenex-all-if-aux-3
	   test left (some-expr right) vars negated
	   (make-context-for-bool-p (make-some (some-vars right) *true*) index)
	   (some-expr-index))))
	((and (not negated)
	      (all-p right)
              (or (null vars) (member-eq (all-var right) vars))
	      (or (bool-p left) bool-p)
	      (not (occurs-in (all-var right) test))
	      (not (occurs-in (all-var right) left)))
	 ;; (if test left (all vars P))
	 (if (bool-p left)
	     (push-proof-log 'is-boolean (if-left-index))
	   (log-coerce-expr-in-boolean-context bool-p (if-left-index)))
	 ;; (if test (if left (true) (false)) (all vars P))
	 (push-proof-log 'remove-universal (if-left-index) (all-vars right) t)
	 ;; (if test (all vars left) (all vars P))
	 (log-all-uncase-analysis-1
	  (make-if test (make-all (all-vars right) left) right) index)
	 ;; (all vars (if test left P))
	 (make-all
	  (all-vars right)
	  (prenex-all-if-aux-3
	   test left (all-expr right) vars negated
	   (make-context-for-bool-p (make-all (all-vars right) *true*) index)
	   (all-expr-index))))
	(t (make-if test left right))))

(defun move-var-in-all (formula var vars index)
  (cond ((and (all-p formula) (member-eq (all-var formula) vars))
         (push-proof-log 'flip-universals index)
         (make-all (all-vars formula)
                   (move-var-in-all
                    (all-expr formula) var vars (all-expr-index))))
        (t (make-all var formula))))

(defun move-var-in-some (formula var vars index)
  (cond ((and (some-p formula) (member-eq (some-var formula) vars))
         (log-flip-existentials index)
         (make-some (some-vars formula)
                    (move-var-in-some
                     (some-expr formula) var vars (some-expr-index))))
        (t (make-some var formula))))

;;; ==================== End of Prenex ====================


;;; =============== Minimize Scope of Quantifiers ===============

;;; Called by the reducer mainly to enable simple instantiations.

(defun minimize-scope-formula (formula index)
  (cond ((atom formula) formula)
	((if-p formula)
	 (make-if
	  (minimize-scope-formula (if-test formula) (if-test-index))
	  (minimize-scope-formula (if-left formula) (if-left-index))
	  (minimize-scope-formula (if-right formula) (if-right-index))))
	((all-p formula)
	 (minimize-scope-all
	  (all-var formula)
	  (minimize-scope-formula (all-expr formula) (all-expr-index))
	  index))
	((some-p formula)
	 (minimize-scope-some
	  (some-var formula)
	  (minimize-scope-formula (some-expr formula) (some-expr-index))
	  index))
	(t (loop for expr in formula
		 for number = 0 then (+ 1 number)
		 collect (minimize-scope-formula
			  expr (cons number index))))))

;;; push universal quantifier into if expression

(defun minimize-scope-all (var expr index)
  (cond ((not (occurs-in var expr))
	 (push-proof-log 'remove-universal index)
	 (coerce-to-bool expr index))
	((if-p expr)
	 (let ((test (if-test expr))
	       (left (if-left expr))
	       (right (if-right expr)))
	   (cond
	     ((not (occurs-in var test))
	      (log-all-case-analysis-1	(make-all (list var) expr) index)
	      (make-if test
		       (minimize-scope-all var left (if-left-index))
		       (minimize-scope-all var right (if-right-index))))
	     ((false-p left)
	      (log-all-case-analysis-5 (make-all (list var) expr) index)
	      (make-if (minimize-scope-some var test (if-test-index))
		       left
		       (minimize-scope-all var right (if-right-index))))
	     ((false-p right)
	      (push-proof-log 'all-case-analysis index)
	      (make-if (minimize-scope-all var test (if-test-index))
		       (minimize-scope-all var left (if-left-index))
		       right))
	     (t (make-all-single var expr)))))
	(t (make-all-single var expr))))

;;; push existential quantifier into if expression

(defun minimize-scope-some (var expr index)
  (cond ((not (occurs-in var expr))
	 (log-remove-existential index)
	 (coerce-to-bool expr index))
	((if-p expr)
	 (let ((test (if-test expr))
	       (left (if-left expr))
	       (right (if-right expr)))
	   (cond
	     ((not (occurs-in var test))
	      (log-some-case-analysis-1 (make-some-single var expr) index)
	      (make-if test
		       (minimize-scope-some var left (if-left-index))
		       (minimize-scope-some var right (if-right-index))))
	     ((true-p left)
	      (log-some-case-analysis-5 (make-some-single var expr) index)
	      (make-if (minimize-scope-some var test (if-test-index))
		       left
		       (minimize-scope-some var right (if-right-index))))
	     ((true-p right)
	      (log-some-case-analysis-4	index)
	      (make-if (minimize-scope-all var test (if-test-index))
		       (minimize-scope-some var left (if-left-index))
		       right))
	     (t (make-some-single var expr)))))
	(t (make-some-single var expr))))

;;; =============== End of Minimize Scope of Quantifiers ===============


;;; ==================== Skolems ====================

;;; given a formula return a list of the skolem variables

(defun list-of-skolem-variables (formula)
  (cond ((atom formula)
	 (and (symbolp formula)
	      (get formula 'variable)
	      (get formula 'skolem)
	      (list formula)))
	(t (mapcan #'(lambda (u) (list-of-skolem-variables u)) formula))))

;;; contains-skolem checks to see if an expression contains a skolem
;;; constant or variable.

(defun contains-skolem-p (expr)
  (cond ((symbolp expr) (get expr 'skolem))
	((consp expr)
	 (dolist (exp expr) (when (contains-skolem-p exp) (return t))))))

;;; make-skolem makes a symbol a skolem (constant or variable).

(defun make-skolem (is-constant variable variables)
  (cond ((and is-constant variables)
	 (let ((symbol (gensym)))
	   (setf (get symbol 'skolem) t)
	   (push (cons variable symbol) *substitution-list*)
	   (cons symbol variables)))
	(t (let ((symbol (genvar variable)))
	     (setf (get symbol 'skolem) t)
	     (push (cons variable symbol) *substitution-list*)
	     (unless is-constant
	       (setf (get symbol 'variable) t)
	       (push symbol *variable-symbols*)
	       (push-undo *undo-push-var-mark*))
	     symbol))))

;;; replace skolems in an expression by their original names

(defun replace-skolems (expr)
  (cond ((symbolp expr)
	 (if (get expr 'skolem)
	     (car (rassoc-equal expr *substitution-list*))
	   expr))
	((consp expr)
	 (if (symbolp (first expr))
	     (if (get (first expr) 'skolem)
		 (if (get (first expr) 'variable)
		     (mapcar #'replace-skolems expr)
		     (car (rassoc-equal (first expr)
					*substitution-list*)))
		 (mapcar #'replace-skolems expr))
	     (mapcar #'replace-skolems expr)))
	(t expr)))

;;; ==================== End of Skolems ====================


;;; =============== Renaming/Unrenaming ===============


;;; Rename all quantified variables with genvars. Formula assumed
;;; to be in expanded form.
(defun rename-quantified-variables (formula index)
  (rename-quantified-variables-aux formula nil index))

;;; Conditionally rename all quantified variables with genvars.
(defun conditionally-rename-quantified-variables (condition formula index)
  (if (not condition)
      formula
      (rename-quantified-variables-aux formula nil index)))

;;; Rename all quantified variables with genvars. No assumption about
;;; formula being expanded.
(defun rename-quantified-variables-unexpanded (unexpanded index)
  (rename-quantified-variables-unexpanded-aux unexpanded nil index))

(defun rename-quantified-variables-aux (formula substitutions index)
  (cond ((integerp formula) formula)
	((atom formula) (binding-of formula substitutions))
	((all-p formula)
	 (let* ((new-var (genvar (all-var formula)))
		(new-sub (cons (all-var formula) new-var)))
	   (push-proof-log 'rename-universal index (all-var formula) new-var)
	   (make-all-single
             new-var
	     (rename-quantified-variables-aux
               (all-expr formula)
               (cons new-sub substitutions)
               (all-expr-index)))))
	((some-p formula)
	 (let* ((new-var (genvar (some-var formula)))
		(new-sub (cons (some-var formula) new-var)))
	   (log-rename-existential (some-var formula) new-var index)
	   (make-some-single
             new-var
	     (rename-quantified-variables-aux
               (some-expr formula)
	       (cons new-sub substitutions)
	       (some-expr-index)))))
	(t (loop for i = 0 then (1+ i)
		 for expr in formula
		 collect (rename-quantified-variables-aux
			  expr substitutions (cons i index))))))

(defun rename-quantified-variables-unexpanded-aux (formula substitutions index)
  (cond ((integerp formula) formula)
	((atom formula) (binding-of formula substitutions))
	((all-p formula)
         (let* ((vars (all-vars formula))
                (var (car vars))
                (new-var (genvar var))
                (new-sub (cons var new-var)))
          (cond ((> (length vars) 1)
                 (push-proof-log 'syntax index)
                 (push-proof-log
                   'rename-universal index var new-var)
                  (let ((result (rename-quantified-variables-unexpanded-aux
                                 (make-all (cdr vars) (all-expr formula))
                                 (cons new-sub substitutions)
                                 (all-expr-index))))
                   (push-proof-log 'syntax index t)
                   (make-all (cons new-var (all-vars result))
                             (all-expr result))))
                (t
                 (push-proof-log 'rename-universal index var new-var)
                 (make-all-single
                   new-var
                   (rename-quantified-variables-unexpanded-aux
                     (all-expr formula)
                     (cons new-sub substitutions)
                     (all-expr-index)))))))
	((some-p formula)
         (let* ((vars (some-vars formula))
                (var (car vars))
                (new-var (genvar var))
                (new-sub (cons var new-var)))
           (cond ((> (length vars) 1)
                  (log-expand-some index)
                  (push-proof-log
                    'rename-universal index var new-var)
                  (let ((result (rename-quantified-variables-unexpanded-aux
                                  (make-some (cdr vars) (some-expr formula))
                                  (cons new-sub substitutions)
                                  (some-expr-index))))
                    (log-unexpand-some index)
                    (make-some (cons new-var (some-vars result))
                               (some-expr result))))
                 (t
                  (push-proof-log
                    'rename-universal index var new-var)
                  (make-some-single
                    new-var
                    (rename-quantified-variables-unexpanded-aux
                      (some-expr formula)
                      (cons new-sub substitutions)
                      (some-expr-index)))))))
	(t (loop for i = 0 then (1+ i)
		 for expr in formula
		 collect (rename-quantified-variables-unexpanded-aux
			  expr substitutions (cons i index))))))

;;; Undo renaming.
(defun unrename-quantified-variables (formula index &optional bound)
  (let ((variables
         (unique-symbol (append bound (list-of-all-variables formula)))))
    (let ((renames (remove-if-not #'genvarp variables))
	  (table (remove-if #'genvarp variables))
	  (substitutions nil))
      (loop for var in renames
	    for newvar = (ungenvar var table)
	    do (push newvar table)
	       (push (cons var newvar) substitutions)
	    finally (return (unrename-quantified-variables-aux
			     substitutions formula index))))))

(defun unrename-quantified-variables-aux (substitutions formula index)
  (cond ((integerp formula) formula)
	((atom formula) (binding-of formula substitutions))
	((all-p formula)
	 (let ((new-var (binding-of (all-var formula) substitutions)))
	   (unless (eq (all-var formula) new-var)
	     (push-proof-log
               'rename-universal index (all-var formula) new-var))
	   (make-all-single
             new-var
	     (unrename-quantified-variables-aux
               substitutions (all-expr formula) (all-expr-index)))))
	((some-p formula)
	 (let ((new-var (binding-of (some-var formula) substitutions)))
	   (unless (eq (some-var formula) new-var)
             (log-rename-existential (some-var formula) new-var index))
	   (make-some-single
             new-var
	     (unrename-quantified-variables-aux
               substitutions (some-expr formula) (some-expr-index)))))
	(t (loop for i = 0 then (1+ i)
		 for expr in formula
		 collect (unrename-quantified-variables-aux
			  substitutions expr (cons i index))))))

;;; =============== End of Renaming/Unrenaming ===============


;;; ==================== Miscellaneous ====================

;;; Clear the instantiation list

(defun clear-instantiations ()
  (setq *instantiation-list* (setq *substitution-list* nil)))

;;; Get the printable (i.e. all symbols are declared as events)
;;; instantiations

(defun get-printable-instantiations ()
  (let ((inst-list nil))
    (dolist (i (unique (get-instantiations)))
      (when (and (symbolp (car i))
		 (not (genvarp (car i)))
		 (not (dolist (s (unique (list-of-symbols (cdr i))))
			(when (genvarp s) (return t)))))
	(push i inst-list)))
    inst-list))

;;; Get all instantiations (including non-printable ones).

(defun get-instantiations ()
  (get-instantiations-recursively *instantiation-list*))

(defun get-instantiations-recursively (instantiation-list)
  (cond ((null instantiation-list) nil)
	(t (let* ((substitution (car instantiation-list))
		  (left (car substitution))
		  (right (cdr substitution)))
;	     (when (or (not (symbolp left)) (not (get left 'skolem)))
;		   (swapf left right))
	     (cons (cons (replace-skolems left) (replace-skolems right))
		   (get-instantiations-recursively
		    (cdr instantiation-list)))))))

;;; Function to strip off leading universal quantifiers.
;;; We don't assume anything about the formula.

(defun strip-off-leading-universals (formula index)
  (cond ((and (all-p formula) (> (length (all-vars formula)) 1))
         (push-proof-log 'syntax index)
         (strip-off-leading-universals
          (make-all (cdr (all-vars formula)) (all-expr formula))
          (all-expr-index)))
        ((all-p formula)
         (strip-off-leading-universals (all-expr formula) (all-expr-index)))
        (t formula)))

;;; We don't assume anything about the formula.

(defun list-of-leading-universals (formula)
  (if (all-p formula)
      (append (all-vars formula)
	      (list-of-leading-universals (all-expr formula)))
      nil))

;;; Function to strip off leading existential quantifiers.
;;; We don't assume anything about the formula.

(defun strip-off-leading-existentials (formula index)
  (cond ((and (some-p formula) (> (length (some-vars formula)) 1))
         (log-expand-some index)
         (strip-off-leading-existentials
          (make-some (cdr (some-vars formula)) (some-expr formula))
          (some-expr-index)))
        ((some-p formula)
         (strip-off-leading-existentials
          (some-expr formula) (some-expr-index)))
        (t formula)))

;;; We don't assume anything about the formula.

(defun list-of-leading-existentials (formula)
  (if (some-p formula)
      (append (some-vars formula)
	      (list-of-leading-existentials (some-expr formula)))
      nil))

;;; ==================== End of Miscellaneous ====================
