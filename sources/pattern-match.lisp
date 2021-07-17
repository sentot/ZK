
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

;;; ========== Pattern Matcher for Rewrite Rules ==========


;;; The pattern matcher assumes functions are used consistently with
;;; the same arity (it works on formulas in internal form).


;;; The main functions of the pattern matcher.

(proclaim '(special *reduce-statistics*))

;;; Find substitutions that when applied to pattern results in
;;; the formula. Return the substitutions and a success indicator.
(defun match-pattern-formula (pattern formula)
  (multiple-value-bind
   (substitutions success)
   (catch 'exit-match
     (values (generate-substitutions pattern formula nil) t))
    (if success
	(incf (stat-match-success *reduce-statistics*))
	(incf (stat-match-fail *reduce-statistics*)))
    (values substitutions success)))

;;; The workhorse for match-pattern-formula.
(defun generate-substitutions (pattern formula substitutions)
  (cond ((atom pattern)
	 (if (litconst-p pattern)
	     ;; litconsts must match exactly
	     (if (equal pattern formula)
		 substitutions
	       (throw 'exit-match (values nil nil)))
	     (add-substitution pattern formula substitutions)))
	((atom formula)
	 (throw 'exit-match (values nil nil)))
	((atom (car pattern))
	 (if (eq (car pattern) (car formula))
	     (generate-substitutions-args
	      (cdr pattern) (cdr formula) substitutions)
	   (throw 'exit-match (values nil nil))))
	((atom (car formula))
	 (throw 'exit-match (values nil nil)))
	(t (generate-substitutions-args pattern formula substitutions))))

(defun generate-substitutions-args (pattern-list formula-list substitutions)
  (if (null pattern-list) substitutions		;done
      (generate-substitutions			;recur away
	(car pattern-list) (car formula-list)	;we match from right to left
	(generate-substitutions-args
	 (cdr pattern-list) (cdr formula-list) substitutions))))


;;; Add new substitution to front of substitutions alist. If new
;;; substitution clashes with another substitution, then throw to exit-match.
(defun add-substitution  (variable value substitutions)
  (let ((previous-binding (assoc-eq variable substitutions)))
    (cond ((null previous-binding)
	   (cons (cons variable value) substitutions))
	  ((equal (cdr previous-binding) value) substitutions)
	  (t (throw 'exit-match (values nil nil))))))

;;; Return non-nil if formula-1 and formula-2 are permutations of each
;;; other. Allows rules such as (equal (f x y) (f x x)). We do not
;;; consider the trivial case of equality to be a permutation
;;; and hence require at least one of the substitutions to be different.
(defun permutative-formulas-p (formula-1 formula-2)
  (when (not (equal formula-1 formula-2))
    (multiple-value-bind (substitutions match-success)
	(match-pattern-formula formula-1 formula-2)
      (and match-success (every #'(lambda (u) (atom (cdr u))) substitutions)))))

;;; Try to match the pattern with any subformula. This is useful
;;; for detecting looping rules (direct or through subgoal).
(defun match-pattern-subformula (pattern formula)
  (multiple-value-bind (substitutions success)
      (match-pattern-formula pattern formula)
      (cond (success
	     ;; match at the top
	     (values substitutions success))
	    ((atom formula)
	     ;; failed
	     (values nil nil))
	    (t (loop for subformula in formula
		     ;; try every subexpression
		     do (multiple-value-setq
			 (substitutions success)
			 (match-pattern-subformula pattern subformula))
		     ;; done at first success
		     until success
		     finally (return (values substitutions success)))))))

