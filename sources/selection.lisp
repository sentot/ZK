
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

;;; =============== Selection of Subexpression ===============

;;; Code to support focus on selected subexpression.


;;; Return a list of lists of assumptions that represent the contexts
;;; of the occurrences of the selected expression in the formula.
;;; It is list of lists because the subexpression may occur more
;;; than once in the formula thus producing multiple contexts.
(defun select-list-of-assumptions (expr formula)
  (select-list-of-assumptions-aux expr formula nil nil))

;;; Dive into the formula to match the expression while
;;; collecting the assumptions.  There are seven cases to be
;;; handled depending on the current subformula.
(defun select-list-of-assumptions-aux (expr formula assumptions result)
  (cond ((equal expr formula)			; we've got a match
	 (cons assumptions result))
	((atom formula) result)			; can't possibly match
	((implies-p formula)			; dive into implication
	 (select-list-of-assumptions-aux
	   expr
	   (implies-right formula)
	   (select-add-assumptions (implies-left formula) assumptions)
	   (select-list-of-assumptions-aux
	     expr (implies-left formula) assumptions result)))
	((and-p formula)			; dive into conjunction
	 (select-list-of-assumptions-and
	   expr (cdr formula) assumptions result))
	((or-p formula)				; dive into disjunction
	 (select-list-of-assumptions-or
	   expr (cdr formula) assumptions result))
	((if-p formula)				; dive into if
	 (select-list-of-assumptions-aux
	   expr
	   (if-right formula)
	   (select-add-negated-assumptions (if-test formula) assumptions)
	   (select-list-of-assumptions-aux
	     expr
	     (if-left formula)
	     (select-add-assumptions (if-test formula) assumptions)
	     (select-list-of-assumptions-aux
	       expr (if-test formula) assumptions result))))
	(t					; dive further into formula
	 (select-list-of-assumptions-list expr formula assumptions result))))

;;; In the case of a conjunction, formula-list is the list of
;;; conjuncts.  Add each of the conjuncts as an assumption.
(defun select-list-of-assumptions-and (expr formula-list assumptions result)
  (cond ((null formula-list) result)
	(t (select-list-of-assumptions-and
	     expr
	     (cdr formula-list)
	     (select-add-assumptions (car formula-list) assumptions)
	     (select-list-of-assumptions-aux
	       expr (car formula-list) assumptions result)))))

;;; In the case of a disjunction, formula-list is the list of
;;; disjuncts.  Add each of the disjuncts as a negated assumption.
(defun select-list-of-assumptions-or (expr formula-list assumptions result)
  (cond ((null formula-list) result)
	(t (select-list-of-assumptions-or
	     expr
	     (cdr formula-list)
	     (select-add-negated-assumptions (car formula-list) assumptions)
	     (select-list-of-assumptions-aux
	       expr (car formula-list) assumptions result)))))

;;; In the case of other function application, formula-list is a list of
;;; arguments (can also include the function applied).
(defun select-list-of-assumptions-list (expr formula-list assumptions result)
  (cond ((null formula-list) result)
	(t (select-list-of-assumptions-list
	     expr
	     (cdr formula-list)
	     assumptions
	     (select-list-of-assumptions-aux
	       expr (car formula-list) assumptions result)))))

;;; Functions to add assumptions that linearize ands.
(defun select-add-assumptions (formula assumptions)
  (cond ((and-p formula)
	 (select-add-assumptions-and (cdr formula) assumptions))
	(t (cons formula assumptions))))

(defun select-add-assumptions-and (formula-list assumptions)
  (cond ((null formula-list) assumptions)
	(t (select-add-assumptions-and
	     (cdr formula-list)
	     (select-add-assumptions (car formula-list) assumptions)))))

;;; Functions to add negated assumptions that linearize ors (with the
;;; negation distributed).
(defun select-add-negated-assumptions (formula assumptions)
  (cond ((or-p formula)
	 (select-add-negated-assumptions-or (cdr formula) assumptions))
	(t (cons (make-not formula) assumptions))))

(defun select-add-negated-assumptions-or (formula-list assumptions)
  (cond ((null formula-list) assumptions)
	(t (select-add-negated-assumptions-or
	     (cdr formula-list)
	     (select-add-negated-assumptions (car formula-list) assumptions)))))


;;; Return modified formula with the first occurrence of the subexpression
;;; replaced by first replacement expression, the second occurrence of
;;; the expression replaced by the second replacement expression, etc.
(defun select-collect-formulas (formula expr replacements)
  (multiple-value-bind (form rep)
      (select-collect-formulas-aux formula expr replacements)
    rep
    form))

(defun select-collect-formulas-aux (formula expr replacements)
  (cond ((null replacements) (values formula replacements))
	((equal formula expr) (values (car replacements) (cdr replacements)))
	((atom formula) (values formula replacements))
	(t (select-collect-formulas-aux-aux formula expr replacements))))

(defun select-collect-formulas-aux-aux (formula-list expr replacements)
  (cond ((null formula-list) (values formula-list replacements))
	(t (multiple-value-bind
	    (form rep)
	    (select-collect-formulas-aux (car formula-list) expr replacements)
	    (multiple-value-bind
	     (form-list rep2)
	     (select-collect-formulas-aux-aux (cdr formula-list) expr rep)
	     (values (cons form form-list) rep2))))))

;;; Given a list of proofs, combine them into a single proof.
(defun select-collect-proofs (proof-list)
  (loop with (final-proof)
	for proof in proof-list
	do (setq final-proof (join-proofs proof final-proof))
	finally (return final-proof)))

;;; Perform an assumption.
(defun select-assume-assumption (assumption)
  (cond ((not-p assumption)
	 (cond ((not-p (not-expr assumption))
		(let ((expr (parse-formula (not-expr (not-expr assumption)))))
		  (assume-true expr)))
	       (t
		(let ((expr (parse-formula (not-expr assumption))))
		  (assume-false expr)))))
	(t (let ((expr (parse-formula assumption)))
	     (assume-true expr)))))

;;; Return the innermost subexpression modifier.
(defun get-subexpression-modifier (modifier-alist)
  (assoc-eq :subexpression modifier-alist))

;;; Return the indices of matching subexpressions in formula.
(defun select-get-indices (expr formula index)
  (cond ((equal expr formula) (list index))
        ((consp formula)
         (loop for form in formula
               for number = 0 then (+ number 1)
               append (select-get-indices expr form (cons number index))))
        (t nil)))
