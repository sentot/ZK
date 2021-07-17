
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

;;; ==================== Rearrange ====================


(defcmd rearrange (:display)
  ((:string "Try to rearrange the current formula.  The rearrangement
consists of reordering the arguments of the conjunctions and
disjunctions of the current formula.  In general, equalities and
simple expressions are placed before more complex arguments such
as quantified expressions.")
   (:paragraph)
   (:string "Rearranging can be useful because the prover is sensitive to
the ordering within formulas (see")
   (:help-name reduction)
   (:punctuation ").")
   (:string "As a result, the prover is often
more likely to obtain a proof, and may do so more efficiently, if
a formula has been rearranged using the")
   (:command-name rearrange)
   (:string "command."))
  (let* ((reduced-formula (display-formula display))
	 (rearranged-formula
          (rearrange-formula
	   reduced-formula index
	   (make-context-for-bool-p-from-display display))))
    (unless (equal rearranged-formula reduced-formula)
      (make-display :formula rearranged-formula
		    :explain (list (list :string "Rearranging gives ..."))))))

(defcmd prove-by-rearrange (:display)
  ((:string
     "Try to prove the current subformula using the rearranging
heuristic. The command")
   (:newline)
   (:command (without-instantiation (reduce)))
   (:newline)
   (:string "is performed first, followed by")
   (:newline)
   (:command (rearrange))
   (:newline)
   (:string "and finally")
   (:newline)
   (:command (without-case-analysis (simplify)))
   (:newline)
   (:string "is performed last."))
  display					;compiler hack
  (let ((result-success (without-instantiation (reduce))))
    (setq result-success (or (rearrange) result-success))
    (setq result-success
          (or (without-case-analysis (simplify)) result-success))
    result-success))



(defun worth-rearranging (sexpr)
  ;; For now just see if there are any quantifiers.
  (contains-quantifier sexpr))

;;; Rearranging works on the output form.
(defun rearrange-formula (sexpr index bool-p)
  (cond ((or (atom sexpr) (litconst-p sexpr)) sexpr)	;optimize
	((implies-p sexpr) (rearrange-implies sexpr index))
	((not-p sexpr)
         (negate (rearrange-formula (not-expr sexpr) (not-expr-index)
				    (make-context-for-bool-p sexpr index))
                 index
                 bool-p))
	((or (or-p sexpr) (and-p sexpr))
         (rearrange-conjunction sexpr index))
	((or (all-p sexpr) (some-p sexpr))
	 (list (first sexpr) (second sexpr)
	       (rearrange-formula (third sexpr) (all-expr-index)
				  (make-context-for-bool-p sexpr index))))
	((and (=-p sexpr)
              (or (bool-p (=-left sexpr)) (bool-p (=-right sexpr))))
	 (make-= (rearrange-formula (=-left sexpr) (=-left-index) nil)
		 (rearrange-formula (=-right sexpr) (=-right-index) nil)))
	((if-p sexpr)
         (make-if (rearrange-formula (if-test sexpr) (if-test-index)
				     (make-context-for-bool-p sexpr index))
                  (rearrange-formula (if-left sexpr) (if-left-index) bool-p)
                  (rearrange-formula (if-right sexpr) (if-right-index) bool-p)))
	(t sexpr)))				;don't go into functions

;;; Rearrange implication.	 
(defun rearrange-implies (sexpr index)
  (rearrange-implies-aux (implies-left sexpr) (implies-right sexpr) index))

(defun rearrange-implies-aux (hypothesis conclusion index)
  (cond ((or-p conclusion)
         (log-implies-or-to-implies-and
	  (make-implies hypothesis conclusion) index)
         ;; each disjunct in the conclusion moved to
         ;; the hypothesis part is negated.
	 (let ((collected
                (loop for c in (butlast (cdr conclusion))
                      and i = 2 then (+ i 1)
                      collect (negate
                               c t (cons i (implies-left-index))))))
           (rearrange-implies-aux
	       (unexpand-function
                'and (cons hypothesis collected)
                (implies-left-index))
	       (car (last conclusion))
               index)))
	((implies-p conclusion)
	 (log-unnest-implies (implies-right conclusion) index)
	 (rearrange-implies-aux
	   (unexpand-function
            'and (list hypothesis (implies-left conclusion))
            (implies-left-index))
	   (implies-right conclusion)
           index))
	(t (make-implies (rearrange-formula
			  hypothesis (implies-left-index)
			  (make-context-for-bool-p
			   (make-implies hypothesis conclusion) index))
			 (rearrange-formula
			  conclusion (implies-right-index)
			  (make-context-for-bool-p
			   (make-implies hypothesis conclusion) index))))))

;;; Predicate returns t iff symbol is one of "and", "or" or "implies".
(defun boolean-connective-p (symbol)
  (or (eq symbol 'and)
      (eq symbol 'or)
      (eq symbol 'implies)))

;;; Compute the complexity of an expression for the purpose of rearranging.
;;; Each if in the expression is given a weight of 2, each quantification
;;; a weight of 1, and others a weight of 0.
(defun instantiation-complexity-of (sexpr)
  (cond ((symbolp sexpr) 0)
	((or (all-p sexpr) (some-p sexpr))
	 (+ (length sexpr) -2
            (instantiation-complexity-of (first (last sexpr)))))
	((if-p sexpr)
	 (+ 2
	    (instantiation-complexity-of (if-test sexpr))
	    (instantiation-complexity-of (if-left sexpr))
	    (instantiation-complexity-of (if-right sexpr))))
	((consp sexpr)
	 (let ((complexity (if (boolean-connective-p (first sexpr)) 1 0)))
	   (dolist (s sexpr)
	     (setq complexity (+ complexity (instantiation-complexity-of s))))
	   complexity))
	(t 0)))

;;; Rearrange-conjunction (and) or disjunction (or).
(defun rearrange-conjunction (sexpr index)
  (let ((op (first sexpr))
	(args (cdr sexpr))
	(bool-p (make-context-for-bool-p sexpr index)))
    (setq args
          (loop for expr in args
                for n = 1 then (+ n 1)
                collect (rearrange-formula expr (cons n index) bool-p)))
    (multiple-value-bind (type-predicates
			  simple-integer-relations
			  other-integer-relations
			  others-0
			  others-1
			  others-2
			  others)
	(rearrange-conjunction-arguments args index 1)
      (let ((indexed-arguments
             (append type-predicates
                     simple-integer-relations
                     other-integer-relations
                     others-0
                     others-1
                     others-2
                     others)))
        (log-permute-connective-arguments
         op
	 indexed-arguments
	 index)
        (cons op (mapcar #'car indexed-arguments))))))

(defun extended-type-predicate-p (expr)
  (or (and (in-p expr)
	   (or (bool-type-p (in-set expr))
	       (int-type-p (in-set expr))))
      (and (=-p expr)
	   (or (type-of-p (=-left expr))
	       (type-of-p (=-right expr))))))

(defun type-predicate-argument (expr)
  (cond ((in-p expr) (in-elem expr))
	((=-p expr) (type-of-expr (=-left expr)))
	((second expr))))

(defun smaller-type-predicate (pred1 pred2)
  (expr-occurs (type-predicate-argument pred1)
	       (type-predicate-argument pred2)))

;;; Return index of last element of predicate-list that satisfies
;;; smaller-type-predicate.
(defun find-smaller-type-predicate (predicate indexed-predicate-list)
  (let ((result 0)
	(i 0))
    (dolist (x indexed-predicate-list)
      (incf i)
      (when (smaller-type-predicate (car x) predicate)
	(setq result i)))
    result))

;;; Place expr after the ith element in expr-list.
(defun insert-after (expr i expr-list)
  (cond ((zerop i) (cons expr expr-list))
	(t (cons (car expr-list)
		 (insert-after expr (1- i) (cdr expr-list))))))

;;; The conjuncts (or disjuncts) are ordered starting with simple integer
;;; relations, followed by other integer relations, other expressions
;;; with weight 0, weight 1, weight 2, and weight more than 2.
(defun rearrange-conjunction-arguments (arguments index n)
  (if (null arguments)
      (values nil nil nil nil nil nil nil)
      (multiple-value-bind (type-predicates
			    simple-relations
			    other-relations
			    others-0
			    others-1
			    others-2
			    others)
	  (rearrange-conjunction-arguments (cdr arguments) index (+ n 1))
	(let ((next (first arguments)))
	  (cond ((extended-type-predicate-p next)
		 (setq type-predicates
		       (insert-after
			 (cons next n)
			 (find-smaller-type-predicate next type-predicates)
			 type-predicates)))
		((>=-p next)
		 (if (and (simple-expression-p (second next))
			  (simple-expression-p (third next)))
		     (push (cons next n) simple-relations)
		     (push (cons next n) other-relations)))
		((=-p next)
		 (if (or (bool-p (=-left next)) (bool-p (=-right next)))
                     (let ((complexity (instantiation-complexity-of next)))
                       (cond ((= complexity 0)
                              (push (cons next n) others-0))
                             ((= complexity 1)
                              (push (cons next n) others-1))
                             ((= complexity 2)
                              (push (cons next n) others-2))
                             (t (push (cons next n) others))))
                   (if (and (simple-expression-p (second next))
                            (simple-expression-p (third next)))
                       (push (cons next n) simple-relations)
                     (push (cons next n) other-relations))))
		(t (let ((complexity (instantiation-complexity-of next)))
                     (cond ((= complexity 0)
                            (push (cons next n) others-0))
                           ((= complexity 1)
                            (push (cons next n) others-1))
                           ((= complexity 2)
                            (push (cons next n) others-2))
                           (t (push (cons next n) others))))))
	  (values type-predicates
		  simple-relations
		  other-relations
		  others-0
		  others-1
		  others-2
		  others)))))

;;; ----- Proof logging permutation of connective arguments.

(defun log-permute-connective-arguments (connective permutation index)
  (let* ((n (length permutation))
         (initial-indices (loop for i from 1 to n collect i))
	 (initial (mapcar #'(lambda (u) (rassoc-equal u permutation))
			  initial-indices)))
    (unless (equal permutation initial)
      (log-expand-connective n index)
      (log-permutation connective permutation initial index)
      (log-unexpand-connective n index))))

(defun log-expand-connective (n index)
  (unless (<= n 2)
    (push-proof-log 'syntax index)
    (log-expand-connective (- n 1) (cons 2 index))))

(defun log-unexpand-connective (n index)
  ;; (op x1 (op x2 (op x3 ...)))
  (unless (<= n 2)
    (log-unexpand-connective (- n 1) (cons 2 index))
    (push-proof-log 'syntax index t)
    ;; (op x1 x2 ...)
    ))

(defun log-permutation (connective target source index)
  (unless (null target)
    (let ((revised-source
           (log-permutation-aux connective (car target) source index)))
      (log-permutation
       connective (cdr target) revised-source (cons 2 index)))))

(defun log-permutation-aux (connective tgt source index)
  (cond
   ((= (cdr tgt) (cdr (car source))) (cdr source))
   (t
    (let* ((res (log-permutation-aux
		 connective tgt (cdr source) (cons 2 index)))
	   (expr (create-expr-from-indexed-arguments
		  connective (list* (car source) tgt res))))
      (if (>= (length source) 3)
	  (log-permute expr index)
	(log-commute expr index))
      (cons (car source) res)))))

(defun create-expr-from-indexed-arguments (op indexed-arguments)
  (cond ((= (length indexed-arguments) 2)
	 (cons op (mapcar #'car indexed-arguments)))
	(t (list op (car (car indexed-arguments))
		 (create-expr-from-indexed-arguments
		  op (cdr indexed-arguments))))))

