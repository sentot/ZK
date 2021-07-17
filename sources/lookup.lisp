
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


;;; This is the look-up part of the deductive database interface.

;;; ==================== The Interface ====================

;;; Check to see if left and right are known to be equal in the deductive
;;; database.  Force pending updates first.
(defun eq-equal (left right index)
  (perform-pending-assumptions)
  (eq-equal-in-egraph left right index))

;;; Lookup a formula in the deductive database possibly returning a
;;; simpler result. Force pending updates first.
(defun eq-lookup (formula index &optional (bool-context-p nil))
  (perform-pending-assumptions)
  (eq-lookup-in-egraph formula index bool-context-p))

;;; Try to find instantiations for the variables in var-list which make
;;; formula equivalent to (TRUE). Force pending updates first.
(defun match-true-formula (var-list formula index)
  (perform-pending-assumptions)
  (match-true-formula-in-egraph var-list formula index))

;;; Try to find instantiations for the variables in var-list which make
;;; formula equivalent to (FALSE). Force pending updates first.
(defun match-false-formula (var-list formula index)
  (perform-pending-assumptions)
  (match-false-formula-in-egraph var-list formula index))

;;; ==================== End of The Interface ====================


;;; Globals

(proclaim '(special *inconsistent* *undo-stack*
                    *simplifier-instantiates-variables-flag*
		    *variable-symbols* *simplifier-substitutes-equalities-flag*
		    *true-node* *false-node* *instantiation-list*
                    *record-proof-logs-flag*))

(defvar *variable-pointer* (gensym))



;;; Are left and right knwon to be equal in the deductive database?
;;; Return t or nil.
(defun eq-equal-in-egraph (left right index)
  (or (is-inconsistent *true* index)
      (with-undo
       (let ((left-node (intern-expression left))
             (right-node (intern-expression right)))
         (cond ((is-inconsistent *true* index) t)
               ((eq (e-node-root left-node) (e-node-root right-node))
                (when *record-proof-logs-flag*
                  (log-node-equality left-node right-node (if-left-index)))
                t))))))

;;; Function returns non-nil if expr is an `obvious' type predicate.

(defun type-predicate-p (expr)
  (or (and (in-p expr) (is-type-p (in-set expr)))
      (and (=-p expr)
	   (or (and (type-of-p (=-left expr))
		    (is-type-p (=-right expr)))
	       (and (type-of-p (=-right expr))
		    (is-type-p (=-left expr)))))))

(defun is-type-p (expr)
  (or (bool-type-p expr) (int-type-p expr)))

(defun intern-expressions-in-egraph (expr)
  (unless (contains-quantifier expr)
    (intern-expressions-in-egraph-aux expr)))

(defun intern-expressions-in-egraph-aux (expr)
  (when (consp expr) (mapcar #'intern-expressions-in-egraph-aux (cdr expr)))
  (intern-expression expr))



;;; The main look-up routine. It may return (TRUE), (FALSE), and integer
;;; literal or any simplified expression equivalent to the original
;;; (within the current context).

(defun eq-lookup-in-egraph (expr index &optional (bool-context-p nil))
  (incf (stat-lookup *reduce-statistics*))
  (push-proof-log 'marker index (list 'simplify 'start expr))
  (let ((instantiation-list *instantiation-list*)
        (result
         (cond ((is-inconsistent *true* index) *true*)
               ((or (all-p expr) (some-p expr))
                (let ((formula (look-up-expr expr index)))
                  (cond ((and (or (all-p formula) (some-p formula))
                              *simplifier-instantiates-variables-flag*)
			 (with-recover-undo-stack-always
                           (look-up-quantified-formula formula index)))
                        (t formula))))
               ((type-predicate-p expr)
                (let ((node1 (intern-expression
                              (if (in-p expr)
                                  (make-type-of (in-elem expr))
                                (=-left expr))))
                      (node2 (intern-expression
                              (if (in-p expr)
                                  (in-set expr)
                                (=-right expr)))))
                  (cond ((is-inconsistent *true* index) *true*)
                        ((eq (e-node-root node1) (e-node-root node2))
                         (when *record-proof-logs-flag*
                               (when (in-p expr)
                                     (log-in-to-type-of
                                      (in-elem expr) (in-set expr) index))
                               (log-node-equality node1 node2 (=-left-index))
                               (push-proof-log 'compute index))
                         *true*)
                        ((check-forbid (e-node-root node1)
                                       (e-node-root node2))
                         (when *record-proof-logs-flag*
                               (when (in-p expr)
                                     (log-in-to-type-of
                                      (in-elem expr) (in-set expr) index))
                               ;; (= (type-of x) type)
                               (let ((x (if (in-p expr)
                                            (in-elem expr)
                                          (second (=-left expr))))
                                     (type (if (in-p expr)
                                               (in-set expr)
                                             (=-right expr))))
                                 (log-convert-boolean-to-coerced
                                  `(= (type-of ,x) ,type) index)
                                 ;; (if (= (type-of x) type) (true) (false))
                                 (push-proof-log 'if-false
						 (if-left-index) *false* t)
                                 (push-proof-log
                                  'if-true (if-right-index) *true* t)
                                 ;; (if (= (type-of x) type)
                                 ;;     (if (false) (false) (true))
                                 ;;     (if (true) (false) (true)))
                                 (push-proof-log 'case-analysis index 1 t)
                                 (log-forbid node1 node2 (if-test-index))
                                 (push-proof-log 'if-true index)))
                         *false*)
                        (t (look-up-expr expr index)))))
               (t (look-up-expr expr index bool-context-p)))))
    (unless (or (true-p result) (false-p result))
      (setq *instantiation-list* instantiation-list))
    (when *record-proof-logs-flag*
      (cond ((and (eq (first (car *proof-log*)) 'marker)
                  (eq (first (third (car *proof-log*))) 'simplify)
                  (eq (second (third (car *proof-log*))) 'start))
             (pop *proof-log*))
            (t (push-proof-log 'marker index (list 'simplify 'end result)))))
    result))



;;; This is used to determine if two quantified expressions are equivalent.
(defun debruijn-form (formula)
  (debruijn-form-aux formula nil))

(defun debruijn-form-aux (formula vars)
  (cond ((all-p formula)
	 (list (first formula)
	       *variable-pointer*
	       (debruijn-form-aux (all-expr formula)
				  (cons (all-var formula) vars))))
        ((some-p formula)
	 (list (first formula)
	       *variable-pointer*
	       (debruijn-form-aux (some-expr formula)
				  (cons (some-var formula) vars))))
	((and (symbolp formula) (member-eq formula vars))
	 (list *variable-pointer*
	       (loop for i from 0 by 1
		     for v in vars
		     when (eq v formula) do (return i))))
	((atom formula) formula)
	(t (list* (car formula)
		  (mapcar #'(lambda (u) (debruijn-form-aux u vars))
			  (cdr formula))))))

(defun log-debruijn-form (formula original index)
  (cond ((all-p formula)
         (unless (eq (all-var formula) (all-var original))
           (push-proof-log 'rename-universal index
                           (all-var formula) (all-var original)))
         (log-debruijn-form
          (all-expr formula) (all-expr original) (all-expr-index)))
        ((some-p formula)
         (unless (eq (some-var formula) (some-var original))
           (log-rename-existential
	    (some-var formula) (some-var original) index))
         (log-debruijn-form
          (some-expr formula) (some-expr original) (some-expr-index)))
        ((consp formula)
         (loop for expr in (cdr formula)
               for orig in (cdr original)
               for i = 1 then (+ i 1)
               do (log-debruijn-form expr orig (cons i index))))))



(defun sublis-eq-log-entry (subst-list entry)
  (let ((type (car entry)))
    (cond ((and (or (eq type 'if-true) (eq type 'if-false) (eq type 'if-equal))
		(> (length entry) 2))
	   (list type (second entry)
		 (sublis-eq subst-list (third entry))
		 t))
	  ((and (eq type 'remove-universal) (> (length entry) 2))
	   (list type (second entry)
		 (mapcar #'(lambda (u) (sublis-eq subst-list u))
			 (third entry))
		 t))
	  ((eq type 'rename-universal)
	   (list type (second entry)
		 (sublis-eq subst-list (third entry))
		 (sublis-eq subst-list (fourth entry))))
	  ((or (eq type 'induct) (eq type 'look-up))
	   (list type (second entry)
		 (sublis-eq subst-list (third entry))))
	  ((eq type 'instantiate-universal)
	   (if (= (length entry) 3)
	       (list type (second entry)
		     (sublis-eq subst-list (third entry)))
	     (list type (second entry)
		   (sublis-eq subst-list (third entry)) t)))
	  (t entry))))
	  

(defun look-up-quantified-formula (formula index)
  (cond (*simplifier-instantiates-variables-flag*
         (cond ((and (all-p formula)
                     (expr-quantified-disjunction-p formula))
                (let ((renames nil)
                      (instantiations nil)
                      (expr formula)
                      (log-sub nil)
                      result proof-log)
                  (loop while (all-p expr)
                        do
                        (let ((skolem (make-skolem nil (all-var expr) nil)))
                          (push (cons (all-var expr) skolem) renames)
                          (setq expr (subst-eq skolem (all-var expr)
                                               (all-expr expr)))))
                  (let* ((*proof-log* nil))
                    (setq result
                          (eq-lookup-in-egraph-false expr (if-test-index)))
                    (setq proof-log (save-proof-log)))
                  (when result
                    (dolist (rename renames)
                      (let ((sub (assoc-eq (cdr rename) *instantiation-list*)))
                        (cond ((null sub)
                               (push (cons (car rename) 0) instantiations))
                              ((contains-skolem-p (cdr sub)) (setq result nil))
                              (t (push sub log-sub)
                                 (push (cons (car rename) (cdr sub))
                                       instantiations))))))
                  (cond ((null result) formula)
                        (t (log-instantiations 'all nil instantiations index)
                           (setq *proof-log*
                                 (append
				  (mapcar #'(lambda (u)
					      (sublis-eq-log-entry log-sub u))
					  proof-log)
                                         *proof-log*))
                           (push-proof-log 'if-false index)
                           *false*))))
               ((and (some-p formula)
                     (expr-quantified-conjunction-p formula))
                (let ((renames nil)
                      (instantiations nil)
                      (expr formula)
                      (log-sub nil)
                      result proof-log)
                  (loop while (some-p expr)
                        do
                        (let ((skolem (make-skolem nil (some-var expr) nil)))
                          (push (cons (some-var expr) skolem) renames)
                          (setq expr (subst-eq skolem (some-var expr)
                                               (some-expr expr)))))
                  (let* ((*proof-log* nil))
                    (setq result
                          (eq-lookup-in-egraph-true expr (if-test-index)))
                    (setq proof-log (save-proof-log)))
                  (when result
                    (dolist (rename renames)
                      (let ((sub (assoc-eq (cdr rename) *instantiation-list*)))
                        (cond ((null sub)
                               (push (cons (car rename) 0) instantiations))
                              ((contains-skolem-p (cdr sub)) (setq result nil))
                              (t (push sub log-sub)
                                 (push (cons (car rename) (cdr sub))
                                       instantiations))))))
                  (cond ((null result) formula)
                        (t
                         (when *record-proof-logs-flag*
                           (log-instantiations 'some nil instantiations index)
                           (setq *proof-log*
                                 (append
				  (mapcar #'(lambda (u)
					      (sublis-eq-log-entry log-sub u))
					  proof-log)
                                         *proof-log*))
                           (push-proof-log 'if-true index))
                         *true*))))
               (t formula)))
        (t formula)))

(defun expr-quantified-disjunction-p (expr)
  (cond ((all-p expr) (expr-quantified-disjunction-p (all-expr expr)))
        ((not (contains-quantifier expr))
         (generalized-disjunction-p expr))))

(defun generalized-disjunction-p (expr)
  (cond ((if-p expr)
         (cond ((true-p (if-left expr))
                (generalized-disjunction-p (if-right expr)))
               ((true-p (if-right expr))
                (generalized-disjunction-p (if-left expr)))))
        (t t)))

(defun expr-quantified-conjunction-p (expr)
  (cond ((some-p expr) (expr-quantified-conjunction-p (some-expr expr)))
        ((not (contains-quantifier expr))
         (generalized-conjunction-p expr))))

(defun generalized-conjunction-p (expr)
  (cond ((if-p expr)
         (cond ((false-p (if-left expr))
                (generalized-conjunction-p (if-right expr)))
               ((false-p (if-right expr))
                (generalized-conjunction-p (if-left expr)))))
        (t t)))

;;; These predicates are used to decide whether to backtrack when instantiating.

(defun inequality-p (formula)
  (or (>=-p formula)
      (and (if-p formula)
	   (>=-p (if-test formula))
	   (false-p (if-left formula))
	   (true-p (if-right formula)))))

(defun non-equality-p (formula)
  (and (if-p formula)
       (=-p (if-test formula))
       (false-p (if-left formula))
       (true-p (if-right formula))))



;;; This specifically queries the deductive database whether a formula
;;; is equivalent to (TRUE) in the current context.

(defun eq-lookup-in-egraph-true (formula index)
  (or (true-p formula)
      (is-inconsistent *true* index)
      (with-undo
	(cond
	  ((symbolp formula)
	   (let ((node (intern-expression formula)))
	     (or (is-inconsistent *true* index)
                 (cond ((eq (e-node-root node) (e-node-root *true-node*))
                        (when *record-proof-logs-flag*
                          (log-node-equality node *true-node* index))
                        t)
                       ((and (get formula 'variable)
                             (not (equivalent-to-non-var node)))
                        (merge-nodes node *true-node* 'instantiate)
                        (push (cons formula *true*) *instantiation-list*)
                        t)))))
	  ((if-p formula) (look-up-true-if formula index))
	  (t (let ((e-node (intern-expression formula)))
               (or (is-inconsistent *true* index)
                   (and (node-bool-p e-node)
                        (with-recover-undo-stack-always
                         (merge-nodes e-node *false-node* 'contradict)
                         (when *inconsistent*
                           (when *record-proof-logs-flag*
                             (log-proof-by-contradiction e-node index))
                           t)))
                   (and *variable-symbols*
                        *simplifier-instantiates-variables-flag*
                        (or (and (=-p (e-node-attribute e-node))
                                 (with-undo
                                  (when
                                   (match-and-merge (arg-1-node e-node)
                                                    (arg-2-node e-node))
                                   (when *record-proof-logs-flag*
                                     (log-node-equality (arg-1-node e-node)
                                                        (arg-2-node e-node)
                                                        (cons 1 index)))
                                   t))
                                 (progn (push-proof-log 'compute index) t))
                            (true-with-match e-node index))))))))))



;;; This specifically queries the deductive database whether a formula
;;; is equivalent to (FALSE) in the current context.

;;; eq-lookup-in-egraph-false searches for an instance that contradicts the
;;; formula.  If it finds one then it returns t, otherwise it returns nil.

(defun eq-lookup-in-egraph-false (formula index)
  (or (false-p formula)
      (is-inconsistent *false* index)
      (with-undo
	(cond
	  ((symbolp formula)
	   (let ((node (intern-expression formula)))
	     (or (is-inconsistent *false* index)
                 (cond ((eq (e-node-root node) (e-node-root *false-node*))
                        (when *record-proof-logs-flag*
                          (log-node-equality node *false-node* index))
                        t)
                       ((and (get formula 'variable)
                             (not (equivalent-to-non-var node)))
                        (merge-nodes node *false-node* 'instantiate)
                        (push (cons formula *false*) *instantiation-list*)
                        t)))))
	  ((if-p formula) (look-up-false-if formula index))
	  (t (let ((e-node (intern-expression formula)))
               (or (is-inconsistent *false* index)
                   (and (node-bool-p e-node)
                        (with-recover-undo-stack-always
                         (merge-nodes e-node *true-node* 'contradict)
                         (when *inconsistent*
                           (when *record-proof-logs-flag*
                             (log-refute-by-contradiction e-node index nil))
                           t)))
                   (and *variable-symbols*
                        *simplifier-instantiates-variables-flag*
                        (false-with-match e-node index)))))))))




;;; look-up-true-if checks to see if an if expression is true.

(defun look-up-true-if (formula index)
  (let ((test (if-test formula))
	(left (if-left formula))
	(right (if-right formula)))
    (cond
      ((and (true-p left) (false-p right))
       (when (eq-lookup-in-egraph-true test (if-test-index))
         (push-proof-log 'if-true index) t))
      ((and (false-p left) (true-p right))
       (when (eq-lookup-in-egraph-false test (if-test-index))
         (push-proof-log 'if-false index) t))
      ((false-p left)
       (and (eq-lookup-in-egraph-true right (if-right-index))
            (eq-lookup-in-egraph-false test (if-test-index))
            (progn (push-proof-log 'if-false index) t)))
      ((false-p right)
       (and (eq-lookup-in-egraph-true left (if-left-index))
            (eq-lookup-in-egraph-true test (if-test-index))
            (progn (push-proof-log 'if-true index) t))))))



;;; look-up-false-if checks to see if an if expression is false.

(defun look-up-false-if (formula index)
  (let ((test (if-test formula))
	(left (if-left formula))
	(right (if-right formula)))
    (cond
      ((and (true-p left) (false-p right))
       (when (eq-lookup-in-egraph-false test (if-test-index))
         (push-proof-log 'if-false index) t))
      ((and (false-p left) (true-p right))
       (when (eq-lookup-in-egraph-true test (if-test-index))
         (push-proof-log 'if-true index) t))
      ((true-p left)
       (and (eq-lookup-in-egraph-false right (if-right-index))
            (eq-lookup-in-egraph-false test (if-test-index))
            (progn (push-proof-log 'if-false index) t)))
      ((true-p right)
       (and (eq-lookup-in-egraph-false left (if-left-index))
            (eq-lookup-in-egraph-true test (if-test-index))
            (progn (push-proof-log 'if-true index) t))))))



;;; look-up-expr looks up to see if an expression is true, false, or may be
;;; simplified

(defun look-up-expr (expr index &optional (bool-context-p nil))
  (let ((e-node (if (or (neq (car *undo-stack*) *undo-push-mark*)
			(eq (cadr *undo-stack*) *blip*))
		    (intern-expression expr)
		    (progn (pop *undo-stack*)
			   (prog1 (intern-expression expr)
				  (push-undo *undo-push-mark*))))))
    (cond ((is-inconsistent *true* index)
           *true*)
          ((and (=-p expr)
                (eq (e-node-root (arg-1-node e-node))
                    (e-node-root (arg-2-node e-node))))
           (when *record-proof-logs-flag*
             (log-node-equality (arg-1-node e-node) (arg-2-node e-node)
                                (=-left-index))
             (push-proof-log 'compute index))
           *true*)
	  ((eq (e-node-root e-node) (e-node-root *true-node*))
           (when *record-proof-logs-flag*
             (log-node-equality e-node *true-node* index))
           *true*)
	  ((eq (e-node-root e-node) (e-node-root *false-node*))
           (when *record-proof-logs-flag*
             (log-node-equality e-node *false-node* index))
           *false*)
	  ((and (node-bool-p e-node)
		(with-recover-undo-stack-always
		  (merge-nodes e-node *false-node* 'contradict)
                  (when (and *record-proof-logs-flag* *inconsistent*)
                    (log-proof-by-contradiction e-node index))
                  *inconsistent*))
	   *true*)
	  ((and (or (node-bool-p e-node) bool-context-p)
		(with-recover-undo-stack-always
		  (merge-nodes e-node *true-node* 'contradict)
                  (when (and *record-proof-logs-flag* *inconsistent*)
                    (log-refute-by-contradiction e-node index bool-context-p))
                  *inconsistent*))
	   *false*)
	  ((and (>=-p expr) (sum-of-node e-node 0)
		(tableau-entry-is-restricted e-node 0))
           (when *record-proof-logs-flag*
             (log-true->=-from-restricted e-node index))
	   *true*)
	  ((and (>=-p expr) (sum-of-node e-node 1)
		(tableau-entry-is-restricted e-node 1))
           (when *record-proof-logs-flag*
             (log-false->=-from-restricted e-node index))
	   *false*)
	  ((integer-equality-is-true expr e-node index)
	   *true*)
          ((computable-arithmetic-p expr)
           (push-proof-log 'compute index)
           (compute-arithmetic expr))
	  ((and *variable-symbols*
		*simplifier-instantiates-variables-flag*
		(with-recover-undo-stack-always
                 (true-with-backchain e-node index)))
	   *true*)
	  ((and (node-bool-p e-node)
		*variable-symbols*
		*simplifier-instantiates-variables-flag*
		(with-recover-undo-stack-always
                 (false-with-backchain e-node index)))
	   *false*)
          (*simplifier-substitutes-equalities-flag*
           (return-simpler-expression expr e-node index))
	  (t expr))))



;;; Code to infer integer equality by contradicting strict inequalities.

(defun integer-equality-is-true (e-node expr index)
  (and (=-p expr) (sum-of-node e-node 0)
       (let ((saved-log (save-proof-log)))
         (and (with-recover-undo-stack-always
               (restrict-node e-node 2 'contradict)
                (when (and *inconsistent* *record-proof-logs-flag*)
                 (log-sum-conversion-of-= e-node index)
                 ;; (= sum 0)
                 (let ((sum (raw-expr-of-sum (sum-of-node e-node 0))))
                   (push-proof-log 'if-equal index (make->= sum 0) t)
                   ;; (if (>= sum 0) (= sum 0) (+ sum 0))
                   (push-proof-log
                    'if-equal (if-left-index) (make->= (make-negate sum) 0) t)
                   ;; (if (>= sum 0)
                   ;;     (if (>= (negate sum) 0) (= sum 0) (= sum 0))
                   ;;     (= sum 0))
                   (log-conclude-=-zero sum (cons 2 (if-left-index)))
                   ;; (if (>= sum 0)
                   ;;     (if (>= (negate sum) 0) (true) (= sum 0))
                   ;;     (= sum 0))
                   (log-push-negate-into-sum sum (list* 1 1 (if-left-index)))
                   (log-contradict-sum-restriction
                    (sum-of-node e-node 1) (sum-of-node e-node 2)
                    (cons 1 (if-left-index)))
                   ;; (if (>= sum 0)
                   ;;     (if (true) (true) (= sum 0))
                   ;;     (= sum 0))
                   (push-proof-log 'if-true (if-left-index))
                   ;; (if (>= sum 0) (true) (= sum 0))
                   ))
               *inconsistent*)
              (with-recover-undo-stack-always
               ;; At this point we know it is <=.
               (restrict-node e-node 3 'contradict)
               (cond ((and *inconsistent* *record-proof-logs-flag*)
                      (log-contradict-sum-restriction
                       (sum-of-node e-node 0) (sum-of-node e-node 3)
                       (if-left-index))
                      ;; (if (true) (true) (= sum 0))
                      (push-proof-log 'if-true index)
                      ;; (true)
                      )
                     (t (restore-proof-log saved-log)))
               *inconsistent*)))))



;;; Code to ``compute'' arithmetic expressions.

(defun computable-arithmetic-p (expr)
  (and (consp expr)
       (member-eq (car expr) '(+ - * div mod rem negate))
       (every #'integerp (cdr expr))
       (cond ((member-eq (car expr) '(div mod rem))
              (not (zerop (third expr))))
             (t t))))

(defun compute-arithmetic (expr)
  (case (car expr)
    (+ (+ (second expr) (third expr)))
    (- (- (second expr) (third expr)))
    (negate (- (second expr)))
    (* (* (second expr) (third expr)))
    (div (truncate (second expr) (third expr)))
    (mod (mod (second expr) (third expr)))
    (rem (rem (second expr) (third expr)))))



;;; return-simpler-expression returns a simpler expression if there is one.

(defun return-simpler-expression (expression e-node index)
  (cond ((litconst-p expression) expression)
	((symbolp expression)
	 (do ((curr (e-node-eqclass e-node) (e-node-eqclass curr)))
	     ((eq curr e-node) expression)
	   (let ((expr (e-node-attribute curr)))
	     (when (and (litconst-p expr) (not (contains-skolem-p expr)))
               (when *record-proof-logs-flag*
                 (log-node-equality e-node curr index))
               (return expr)))))
	(t (let ((ref-expr expression)
		 (eqv-expr nil)
                 (eqv-node nil))
	     (do ((curr (e-node-eqclass e-node) (e-node-eqclass curr)))
		 ((eq curr e-node)
                  (cond (eqv-expr
                         (when *record-proof-logs-flag*
                           (log-node-equality e-node eqv-node index))
                         eqv-expr)
                        ((arithmetic-expression-p expression)
                         (return-simpler-integer-expression
                          expression e-node index))
                        (t expression)))
	       (let ((expr (e-node-attribute curr)))
		 (cond ((and (litconst-p expr) (not (contains-skolem-p expr)))
                        (when *record-proof-logs-flag*
                          (log-node-equality e-node curr index))
			(return expr))
		       ((and (not (contains-skolem-p expr))
			     (expr-occurs expr ref-expr))
			(setq eqv-expr expr)
                        (setq eqv-node curr)
			(setq ref-expr expr)))))))))



;;; match-true-formula-in-egraph checks to see if a formula is true with
;;; match.  However, it is not a decision procedure (it may fail even if
;;; the formula is true).  It returns the substitutions and a success
;;; indicator.

(defun match-true-formula-in-egraph (var-list formula index)
  (if var-list
      (let ((new-vars nil)
	    (subst-list-1 nil)
	    (undo-stack *undo-stack*)
            (log-sub nil)
            (subst-list-3 nil) success proof-log)
        (let ((*proof-log* nil))
          (push-undo *undo-push-mark*)
          (push-proof-log 'marker index '(match-true start))
          (dolist (var var-list)
            (let ((skolem (make-skolem nil var nil)))
              (push skolem new-vars)
              (push (cons var skolem) subst-list-1)))
          (setq success (eq-lookup-in-egraph-true
                         (sublis-eq subst-list-1 formula) index))
          (when success
            (dolist (v subst-list-1)
              (let ((sub (assoc-eq (cdr v) *instantiation-list*)))
                (cond ((null sub)
                       (when (occurs-in (car v) formula)
                         (push (cons (car v) 0) subst-list-3)))
                      ((contains-skolem-p (cdr sub))
                       (return (setq success nil)))
                      (t (push sub log-sub)
                         (push (cons (car v) (cdr sub)) subst-list-3))))))
          (loop until (eq undo-stack *undo-stack*)
                do (pop-undo))
          (push-proof-log 'marker index '(match-true end (true)))
          (setq proof-log (save-proof-log)))
        (cond (success
               (setq *proof-log*
                     (append (sublis-eq log-sub proof-log) *proof-log*))
               (values subst-list-3 t))
              (t (values nil nil))))
    (values nil (eq-lookup-in-egraph-true formula index))))

;;; match-false-formula-in-egraph is the dual of match-true-formula.

(defun match-false-formula-in-egraph (var-list formula index)
  (if var-list
      (let ((new-vars nil)
	    (subst-list-1 nil)
	    (undo-stack *undo-stack*)
            (log-sub nil)
            (subst-list-3 nil) success proof-log)
        (let ((*proof-log* nil))
          (push-undo *undo-push-mark*)
          (push-proof-log 'marker index '(match-false start))
          (dolist (var var-list)
            (let ((skolem (make-skolem nil var nil)))
              (push skolem new-vars)
              (push (cons var skolem) subst-list-1)))
          (setq success (eq-lookup-in-egraph-false
                         (sublis-eq subst-list-1 formula) index))
          (when success
            (dolist (v subst-list-1)
              (let ((sub (assoc-eq (cdr v) *instantiation-list*)))
                (cond ((null sub)
                       (push (cons (car v) 0) subst-list-3))
                      ((contains-skolem-p (cdr sub))
                       (return (setq success nil)))
                      (t (push sub log-sub)
                         (push (cons (car v) (cdr sub)) subst-list-3))))))
          (loop until (eq undo-stack *undo-stack*)
                do (pop-undo))
          (push-proof-log 'marker index '(match-false end (false)))
          (setq proof-log (save-proof-log)))
        (cond (success
               (setq *proof-log*
                     (append (sublis-eq log-sub proof-log) *proof-log*))
               (values subst-list-3 t))
              (t (values nil nil))))
    (values nil (eq-lookup-in-egraph-false formula index))))



;;; Function called by return-simpler-expression.
(defun return-simpler-integer-expression (expr e-node index)
  (cond ((non-trivial-product-p expr) expr)
        (t (let ((saved-log (save-proof-log))
                 result)
             (when *record-proof-logs-flag* (log-collect-terms expr index))
             (setq result (expr-of-sum (sum-of-node e-node 0) index))
             (cond ((equal result expr)
                    (setq *proof-log* saved-log)
                    expr)
                   (t result))))))

;;; Produce an integer expression from a linear sum.
(defun expr-of-sum (linear-sum index)
  (let ((constant (car linear-sum))
	(rest-of-sum (cdr linear-sum)))
    (cond ((null rest-of-sum) constant)
          ((zerop constant)
           (let ((rest (raw-expr-of-sum-aux rest-of-sum)))
             (when *record-proof-logs-flag*
               (log-use-axiom-as-rewrite
                `(+ 0 ,rest) '+.zero.left
		`((= |)X| ,rest)) index)
               ;; (if (= (type-of rest) (int)) rest (+ 0 rest))
               (log-type-of-expr rest (cons 1 (if-test-index)))
               (push-proof-log 'compute (if-test-index))
               (push-proof-log 'if-true index))
             (expr-of-sum-aux rest-of-sum nil index)))
          (t (expr-of-sum-aux rest-of-sum constant index)))))

(defun expr-of-sum-aux (sum left index)
  (let ((next (make-* (cdar sum)
                      (if (e-node-p (caar sum))
                          (e-node-attribute (caar sum))
                        (make-times-from-bag (caar sum))))))
    (cond
     ((null (cdr sum))
      (cond
       ((= (cdar sum) 1)
        (cond
         ((not (null left))
          (when *record-proof-logs-flag*
            ;; (+ left (* 1 factor))
            (log-use-axiom-as-rewrite
             `(+ ,left ,next) 'from.+.times.1.right
	     `((= |)X| ,left) (= |)Y| ,(*-right next)))
             index))
          (cond ((and (e-node-p (caar sum))
                      (ord-p (e-node-attribute (caar sum))))
                 (when *record-proof-logs-flag*
                       (log-use-axiom-as-rewrite
                        `(+ ,left ,(*-right next)) '+.ord.right
                        `((= |)X| ,left) (= |)Y| ,(ord-expr (*-right next))))
			index))
                 `(+ ,left ,(ord-expr (*-right next))))
                (t `(+ ,left ,(*-right next)))))
         ((and (e-node-p (caar sum))
               (eq (e-node-root *int-node*)
                   (e-node-root (e-node-type (caar sum)))))
          (when *record-proof-logs-flag*
            ;; (* 1 factor)
            (log-use-axiom-as-rewrite
             next '*.one.left `((= |)X| ,(*-right next))) index)
            ;; (if (= (type-of factor) (int)) factor (* 1 factor))
            (log-node-equality (e-node-type (caar sum)) *int-node*
                               (cons 1 (if-test-index)))
            (push-proof-log 'compute (if-test-index))
            (push-proof-log 'if-true index))
          (cond ((and (e-node-p (caar sum))
                      (ord-p (e-node-attribute (caar sum)))
                      (eq (e-node-root *int-node*)
                          (e-node-root
                           (e-node-type (arg-1-node (caar sum))))))
                 (when *record-proof-logs-flag*
                   (log-use-axiom-as-rewrite
                    (*-right next) 'ord.int.internal
                    `((= |)X| ,(ord-expr (*-right next)))) index)
                   ;; (if (= (type-of factor) (int)) factor (ord factor))
                   (log-node-equality (e-node-type (arg-1-node (caar sum)))
                                      *int-node* (cons 1 (if-test-index)))
                   (push-proof-log 'compute (if-test-index))
                   (push-proof-log 'if-true index))
                 (ord-expr (*-right next)))
                (t (*-right next))))
         (t next)))
       ((null left)
        (cond ((and (e-node-p (caar sum))
                    (ord-p (e-node-attribute (caar sum))))
               ;; (* c (ord factor))
               (when *record-proof-logs-flag*
                 (log-use-axiom-as-rewrite
                  next '*.ord.right
                  `((= |)X| ,(*-left next)) (= |)Y| ,(ord-expr (*-right next))))
		  index))
               `(* ,(*-left next) ,(ord-expr (*-right next))))
              (t next)))
       (t
        (cond ((and (e-node-p (caar sum))
                    (ord-p (e-node-attribute (caar sum))))
               ;; (+ left (* c (ord factor)))
               (when *record-proof-logs-flag*
                 (log-use-axiom-as-rewrite
                  next '*.ord.right
                  `((= |)X| ,(*-left next)) (= |)Y| ,(ord-expr (*-right next))))
		  (cons 2 index)))
               `(+ ,left (* ,(*-left next) ,(ord-expr (*-right next)))))
              (t `(+ ,left ,next))))))
    ((= (cdar sum) 1)
     (let ((rest (raw-expr-of-sum-aux (cdr sum))))
       (cond ((null left)
              ;; (+ (* 1 factor) rest)
              (log-use-axiom-as-rewrite
               `(+ ,next ,rest) 'from.+.times.1.left
	       `((= |)X| ,(*-right next)) (= |)Y| ,rest))
               index)
              (cond ((and (e-node-p (caar sum))
                          (ord-p (e-node-attribute (caar sum))))
                     (when *record-proof-logs-flag*
                       (log-use-axiom-as-rewrite
                        `(+ ,(*-right next) ,rest) '+.ord.left
                        `((= |)X| ,(ord-expr (*-right next))) (= |)Y| ,rest))
			index))
                     (expr-of-sum-aux
                      (cdr sum) (ord-expr (*-right next)) index))
                    (t (expr-of-sum-aux (cdr sum) (*-right next) index))))
             (t
              ;; (+ left (+ (* 1 factor) rest))
              (log-use-axiom-as-rewrite
               `(+ ,next ,rest) 'from.+.times.1.left
	       `((= |)X| ,(*-right next)) (= |)Y| ,rest))
               (cons 2 index))
              (cond ((and (e-node-p (caar sum))
                          (ord-p (e-node-attribute (caar sum))))
                     (when *record-proof-logs-flag*
                       (log-use-axiom-as-rewrite
                        `(+ ,(*-right next) ,rest) '+.ord.left
                        `((= |)X| ,(ord-expr (*-right next))) (= |)Y| ,rest))
			(cons 2 index)))
                     `(+ ,left ,(expr-of-sum-aux
                                 (cdr sum) (ord-expr (*-right next))
                                 (cons 2 index))))
                    (t `(+ ,left ,(expr-of-sum-aux
                                  (cdr sum) (*-right next)
                                  (cons 2 index)))))))))
    ((null left)
     ;; (+ next rest)
     (cond ((and (e-node-p (caar sum))
                 (ord-p (e-node-attribute (caar sum))))
            ;; (+ (* c (ord factor)) rest)
            (when *record-proof-logs-flag*
              (log-use-axiom-as-rewrite
               next '*.ord.right
               `((= |)X| ,(*-left next)) (= |)Y| ,(ord-expr (*-right next))))
	       (cons 1 index)))
            (expr-of-sum-aux
             (cdr sum) `(* ,(*-left next) ,(ord-expr (*-right next))) index))
           (t (expr-of-sum-aux (cdr sum) next index))))
    (t
     ;; (+ left (+ next rest))
     (cond ((and (e-node-p (caar sum))
                 (ord-p (e-node-attribute (caar sum))))
            ;; (+ left (+ (* c (ord factor)) rest))
            (when *record-proof-logs-flag*
              (log-use-axiom-as-rewrite
               next '*.ord.right
               `((= |)X| ,(*-left next)) (= |)Y| ,(ord-expr (*-right next))))
	       (list* 1 2 index)))
            `(+ ,left
                ,(expr-of-sum-aux
                  (cdr sum) `(* ,(*-left next) ,(ord-expr (*-right next)))
                  (cons 2 index))))
           (t `(+ ,left ,(expr-of-sum-aux
                          (cdr sum) next (cons 2 index)))))))))


;;; Function to find out if we are in an inconsistent state and
;;; generate log if required.

(defun is-inconsistent (result index)
  (and *inconsistent*
       (or (null *record-proof-logs-flag*)
           (progn (push-proof-log 'if-false index result t)
                  (log-inconsistent *inconsistent* (if-test-index))
                  (push-proof-log 'if-true index)))))


