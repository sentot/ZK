
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

(proclaim '(special *reduce-statistics*))

;;; ==================== Intern Expressions ====================

;;; Form internal representations of expressions. An expression will
;;; have a structure-shared representation in the egraph. In addition,
;;; if the expression is an integer arithmetic expression or is an
;;; integer relation, it will have entries in the tableau.

;;; ====================================================================

;;; The top level function is intern-expression.

(defun intern-expression (input-expression)
  (unless *inconsistent*
    (let ((node (intern-subexpression input-expression)))
      ;; The egraph and tableau may already be able to derive facts.
      (compute-closure)
      (unless *inconsistent*
	(apply-grules node)
	;; Need to derive facts from applying grules.
	(compute-closure))
      (and (not *inconsistent*) node))))

;;; Dispatch cases of expression.
(defun intern-subexpression (expression)
  (cond
    ((symbolp expression) (intern-symbol expression))
    ((integerp expression) (intern-integer expression))
    ((or (all-p expression) (some-p expression))
     (intern-quantification expression))
    ((consp expression) (intern-function-application expression))
    (t (error "Can't integrate '~A'." expression))))



;;; ==================== Application of Grules ====================

;;; Try to apply grules to e-node. A grule is applied to an e-node if it
;;; is enabled, accessible, has not been applied, and all of its subgoals
;;; are satisfied.
(defun apply-grules (e-node)
  (let ((expr (e-node-attribute e-node)))
    (unless (atom expr)
      (let ((grules (get-grules expr)))
	(dolist (grule grules)
	  (when (and (grule-enabled grule)
		     (not (event-inaccessible-p grule))
		     (not (member-eq grule (e-node-grules-applied-p e-node))))
	    ;; Pattern match is just matching function symbol.
	    (let ((substitutions (pairlis (cdr (grule-pattern grule))
                                          (cdr expr)))
                  (results nil)
		  (failed nil))
	      (let ((subgoals (grule-subgoals grule)))
		;; Try satisfy subgals.
		(dolist (subgoal subgoals)
		  (setq subgoal (sublis-eq substitutions subgoal))
		  (let ((result (satisfy-subgoal subgoal)))
		    (cond ((or (null result) *inconsistent*)
			   (setq failed t)
			   (return t))
			  (t (push (car result) results)
                             (setq substitutions
                                   (append (cdr result) substitutions))))))
		(unless failed
		  ;; Apply grule.
		  (incf (stat-assumption *reduce-statistics*))
		  (update-grules grule)
		  (push-undo (list #'undo-set-grules-applied-p
				   (cons e-node
                                         (e-node-grules-applied-p e-node))))
		  (push grule (e-node-grules-applied-p e-node))
                  (let ((node (intern-subexpression
                               (sublis-eq substitutions
                                          (car (grule-value grule))))))
                    (push-fifo
                     (list (if (cdr (grule-value grule)) 'forbid 'merge)
                           node *true-node*
                           (list 'grule node grule substitutions
                                 (reverse results)))
                     *merge-list*)))
		(when *inconsistent* (return nil))))))))))



;;; -------------------- Grule Subgoal --------------------

;;; A grule may have subgoals, in which case the grule is applied only
;;; if all subgoals are satisfied.

;;; Try to satisfy subgoal. A successful find will return
;;;   ((TRUE e-node) . substitutions),
;;;   ((NOT-TRUE e-node justification) . substitutions),
;;;   (TRUE-VAR . substitutions) or
;;;   (FALSE-VAR . substitutions).
;;; Otherwise NIL is returned.
(defun satisfy-subgoal (subgoal)
  (let ((expr (first subgoal))
	(negated (second subgoal))
	(vars (third subgoal)))
    (cond ((null vars)
	   ;; No vars to instantiate.
	   (let ((e-node (intern-expression expr)))
	     (cond (*inconsistent* nil)
		   (negated
		    (if (check-forbid e-node *true-node*)
			(cons (list 'not-true e-node
                                    (get-forbid-justification
                                     (e-node-root e-node)
                                     (e-node-root *true-node*)))
                              nil)
			nil))
		   (t (if (eq (e-node-root e-node) (e-node-root *true-node*))
			  (cons (list 'true e-node) nil)
			  nil)))))
	  (t
	   ;; Need instantiations.
	   (satisfy-subgoal-with-instantiations expr negated vars)))))


;;; The case where instantiations are needed.
(defun satisfy-subgoal-with-instantiations (expr negated vars)
  (cond ((atom expr)				; must be a variable
	 (cons (if negated 'false-var 'true-var)
               (list (cons expr (if negated *false* *true*)))))
	(t (let ((car-node (intern-subexpression (car expr))))
	     (unless (null car-node)
	       (let ((e-node (e-node-e-pred car-node)))
		 (unless (null e-node)
		   (loop-over-nodes (e e-node e-node-samecar)
		     (multiple-value-bind (substs success)
			 (simple-pattern-match expr (e-node-attribute e) vars)
		       (when (and success
				  (if negated
				      (check-forbid (e-node-root e)
                                                    (e-node-root *true-node*))
				      (eq (e-node-root e)
                                          (e-node-root *true-node*))))
                         (if negated
                             (return (cons (list 'not-true e
                                                 (get-forbid-justification
                                                  (e-node-root e)
                                                  (e-node-root *true-node*)))
                                           substs))
                           (return (cons (list 'true e)
                                         substs)))))))))))))

;;; Pattern matcher used by satisfy-subgoal-with-instantiations.
;;; Only variables that occur in vars may be instantiated.
(defun simple-pattern-match (pattern expr vars)
  (cond ((member-eq pattern vars) (values (list (cons pattern expr)) t))
	((atom pattern) (values nil (equal pattern expr)))
	((atom expr) (values nil nil))
	(t (multiple-value-bind (substs1 success1)
	       (simple-pattern-match (car pattern) (car expr) vars)
	     (if success1
		 (multiple-value-bind (substs2 success2)
		     (simple-pattern-match
		       (sublis-eq substs1 (cdr pattern))
		       (sublis-eq substs1 (cdr expr))
		       vars)
		   (if success2
		       (values (append substs1 substs2) t)
		         (values nil nil)))
		 (values nil nil))))))

;;; -------------------- End of Grule Subgoal --------------------

;;; ==================== End of Application of Grules ====================



;;; -------------------- Auxiliary Functions --------------------

;;; Integrate (TYPE-OF (e-node-attribute node)).
(defun create-type-of-node (node)
  (create-e-node
   *type-of-node*
   (create-aux-node node *enil*)
   (make-type-of (e-node-attribute node))
   (make-an-e-node nil nil (gensym) nil)))

;;; Create a non-leaf e-node.
(defun create-e-node (its-ecar its-ecdr its-attribute its-type)
  (let ((new-node (and (e-node-e-pred its-ecar)
		       (aux-node-e-pred its-ecdr)
		       (find-e-node (aux-node-e-pred its-ecdr)
				    its-ecar
				    its-ecdr))))
    (unless new-node
      (setq new-node (make-an-e-node its-ecar its-ecdr its-attribute its-type))
      (cond ((null (e-node-e-pred its-ecar))
	     (push-undo (list #'undo-set-e-pred its-ecar))
	     (setf (e-node-e-pred its-ecar) new-node)
             (let ((car-root (e-node-root its-ecar)))
               (unless (eq its-ecar car-root)
                 (cond ((null (e-node-e-pred car-root))
                        (push-undo (list #'undo-set-e-pred car-root))
                        (setf (e-node-e-pred car-root) new-node))
                       (t (swap-samecar
                           new-node (e-node-e-pred car-root)))))))
	    (t (swap-samecar new-node (e-node-e-pred its-ecar))))
      (cond ((null (aux-node-e-pred its-ecdr))
	     (push-undo (list #'undo-set-e-pred-aux its-ecdr))
	     (setf (aux-node-e-pred its-ecdr) new-node)
             (let ((cdr-root (aux-node-root its-ecdr)))
               (unless (eq its-ecdr cdr-root)
                 (cond ((null (aux-node-e-pred cdr-root))
                        (push-undo (list #'undo-set-e-pred-aux cdr-root))
                        (setf (aux-node-e-pred cdr-root) new-node))
                       (t (swap-samecdr
                           new-node (aux-node-e-pred cdr-root)))))))
	    (t (swap-samecdr new-node (aux-node-e-pred its-ecdr))))
      (check-for-equivalence new-node))
    new-node))



;;; Create a non-leaf aux-node.
(defun create-aux-node (its-ecar its-ecdr)
  (let ((new-node (and (e-node-aux-pred its-ecar)
		       (aux-node-aux-pred its-ecdr)
		       (find-aux-node (aux-node-aux-pred its-ecdr)
				      its-ecar
				      its-ecdr))))
    (unless new-node
      (setq new-node (make-auxiliary-node its-ecar its-ecdr))
      (cond ((null (e-node-aux-pred its-ecar))
	     (push-undo (list #'undo-set-aux-pred its-ecar))
	     (setf (e-node-aux-pred its-ecar) new-node)
             (let ((car-root (e-node-root its-ecar)))
               (unless (eq its-ecar car-root)
                 (cond ((null (e-node-aux-pred car-root))
                        (push-undo (list #'undo-set-aux-pred car-root))
                        (setf (e-node-aux-pred car-root) new-node))
                       (t (swap-samecar-aux
                           new-node (e-node-aux-pred car-root)))))))
	    (t (swap-samecar-aux new-node (e-node-aux-pred its-ecar))))
      (cond ((null (aux-node-aux-pred its-ecdr))
	     (push-undo (list #'undo-set-aux-pred-aux its-ecdr))
	     (setf (aux-node-aux-pred its-ecdr) new-node)
             (let ((cdr-root (aux-node-root its-ecdr)))
               (unless (eq its-ecdr cdr-root)
                 (cond ((null (aux-node-aux-pred cdr-root))
                        (push-undo (list #'undo-set-aux-pred-aux cdr-root))
                        (setf (aux-node-aux-pred cdr-root) new-node))
                       (t (swap-samecdr-aux
                           new-node (aux-node-aux-pred cdr-root)))))))
	    (t (swap-samecdr-aux new-node (aux-node-aux-pred its-ecdr))))
      (check-for-equivalence-aux new-node))
    new-node))

;;; -------------------- End of Auxiliary Functions --------------------



;;; =============== Cases of Interning Subexpression ===============
  
;;; Create e-node representation of the given integer.
(defun intern-integer (integer)
  (or (get-integer-expression-table integer)
      (let ((e-node (make-an-e-node nil nil integer *int-node*)))
	(push-undo (list #'undo-intern-integer-expression integer))
	(put-integer-expression-table integer e-node)
	(setf (e-node-type e-node) (create-type-of-node e-node))
        (push-fifo `(merge ,(e-node-type e-node) ,*int-node* type-of)
                   *merge-list*)
	e-node)))

;;; Create e-node representation of the given symbol.
(defun intern-symbol (symbol)
  (or (get-symbol-expression-table symbol)
      (let* ((event (get-event symbol))
	     (e-node (make-an-e-node nil nil symbol nil)))
	(push-undo (list #'undo-intern-symbol-expression symbol))
	(when (member-eq symbol *variable-symbols*)
	  (setf (e-node-variable e-node) t))
	(put-symbol-expression-table symbol e-node)
	(setf (e-node-type e-node) (create-type-of-node e-node))
	e-node)))



;;; Create e-node representation of quantified formula.
;;; DeBruijn form is also checked and interned, and may cause
;;; equalities to be detected.
(defun intern-quantification (formula)
  (let* ((debruijn (debruijn-form formula))
         (debruijn-node (get-debruijn-table debruijn)))
    (cond ((null debruijn-node)
           (let ((node (make-an-e-node nil nil formula nil)))
             (push-undo (list #'undo-intern-quantification formula))
             (put-quantification-table formula node)
             (setf (e-node-type node) (create-type-of-node node))
             (push-undo (list #'undo-intern-debruijn debruijn))
             (put-debruijn-table debruijn node)
             (push-fifo `(merge ,(e-node-type node) ,*bool-node* type-of)
                        *merge-list*)
             node))
          (t
           (let ((node (get-quantification-table formula)))
             (when (null node)
               (setq node (make-an-e-node nil nil formula nil))
               (push-undo (list #'undo-intern-quantification formula))
               (put-quantification-table formula node)
               (setf (e-node-type node) (create-type-of-node node)))
             (push-fifo `(merge ,node ,debruijn-node debruijn) *merge-list*)
             (push-fifo `(merge ,(e-node-type node) ,*bool-node* type-of)
                        *merge-list*)
             node)))))

;;; Create e-node representation of a function application.
(defun intern-function-application (expression)
  (let* ((car-node (intern-subexpression (car expression)))
	 (cdr-node (intern-function-arguments (cdr expression))))
    (or (and (aux-node-e-pred cdr-node)
	     (find-e-node (aux-node-e-pred cdr-node) car-node cdr-node))
        (let ((e-node (create-e-node car-node cdr-node expression nil)))
          (setf (e-node-type e-node)
                (if (type-of-p expression)
                    (make-an-e-node nil nil (gensym) nil)
                  (create-type-of-node e-node)))
          (setf (e-node-operation e-node) (car expression))
          (cond
           ((=-p expression)
            (push-fifo `(merge ,(e-node-type e-node) ,*bool-node* type-of)
                       *merge-list*)
            (when (eq (e-node-root (arg-1-node e-node))
                      (e-node-root (arg-2-node e-node)))
              (push-fifo (list `merge e-node *true-node* '=-equal-arguments)
                         *merge-list*))
            (when (or (node-int-p (arg-1-node e-node))
                      (node-int-p (arg-2-node e-node)))
            (let* ((ord-args (mapcar #'wrap-ord (cdr expression)))
                   (ord-cdr-node (intern-function-arguments ord-args))
                   (ord-node (create-e-node car-node ord-cdr-node
                                               (cons (car expression) ord-args)
                                               nil)))
              (setf (e-node-type ord-node) (create-type-of-node ord-node))
              (setf (e-node-operation ord-node) (car expression))
              (intern-integer-equality-sum ord-node expression)
              (push-fifo `(merge ,(e-node-type ord-node) ,*bool-node* type-of)
                         *merge-list*)
              (when (eq (e-node-root (arg-1-node ord-node))
                        (e-node-root (arg-2-node ord-node)))
                (push-fifo (list `merge ord-node *true-node*
                                 '=-equal-arguments)
                           *merge-list*)))))
           ((>=-p expression)
            (push-fifo `(merge ,(e-node-type e-node) ,*bool-node* type-of)
                       *merge-list*)
            (let* ((ord-args (mapcar #'wrap-ord (cdr expression)))
                   (ord-cdr-node (intern-function-arguments ord-args))
                   (ord-node (create-e-node car-node ord-cdr-node
                                               (cons (car expression) ord-args)
                                               nil)))
              (setf (e-node-type ord-node) (create-type-of-node ord-node))
              (setf (e-node-operation ord-node) (car expression))
              (intern-integer-inequality-sum ord-node expression)
              (push-fifo `(merge ,(e-node-type ord-node) ,*bool-node* type-of)
                         *merge-list*)
              (when (eq (e-node-root (arg-1-node ord-node))
                        (e-node-root (arg-2-node ord-node)))
                (push-fifo (list 'merge ord-node *true-node* '>=-reflexive)
                           *merge-list*))))
           ((or (+-p expression) (--p expression) (*-p expression)
                (negate-p expression) (ord-p expression))
            (intern-integer-operation-sum e-node expression)
            (when (and (*-p expression)
                       (eq (e-node-root (arg-1-node e-node))
                           (e-node-root (arg-2-node e-node))))
              (push-fifo (list 'restrict e-node 0 `(square ,e-node))
                         *tableau-list*))
            (when (*-p expression)
              (let (left)
                (cond ((setq left (node-is-strictly-positive-p
                                   (arg-1-node e-node)))
                       (propagate-positive-left left e-node))
                      ((setq left (node-is-strictly-negative-p
                                   (arg-1-node e-node)))
                       (propagate-negative-left left e-node))
                      ((setq left (node-is-non-negative-p
                                   (arg-1-node e-node)))
                       (propagate-non-negative-left left e-node))
                      ((setq left (node-is-negative-or-zero-p
                                   (arg-1-node e-node)))
                       (propagate-negative-or-zero-left left e-node)))))
            (push-fifo `(merge ,(e-node-type e-node) ,*int-node* type-of)
                       *merge-list*))
           ((if-p expression)
            (cond ((true-p (if-test expression))
                   (push-fifo
                    `(merge ,e-node ,(arg-2-node e-node) (if-true ,e-node))
                    *merge-list*))
                  ((false-p (if-test expression))
                   (push-fifo
                    `(merge ,e-node ,(arg-3-node e-node) (if-false ,e-node))
                    *merge-list*))
                  ((equal (if-left expression) (if-right expression))
                   (push-fifo
                    `(merge ,e-node ,(arg-2-node e-node) (if-equal ,e-node))
                    *merge-list*))
                  (t
                   (let ((test (if-test expression))
                         (left (if-left expression))
                         (right (if-right expression)))
                     (intern-subexpression (make-if *true* left right))
                     (intern-subexpression (make-if *false* left right))
                     (intern-subexpression (make-if test left left)))))))
	  (let ((event (get-event (car expression))))
	    (let ((type
		   (cond ((and (ufunction-p event)
			       (not (event-inaccessible-p event)))
			  (ufunction-type event))
			 ((and (function-stub-p event)
			       (not (event-inaccessible-p event)))
			  (function-stub-type event)))))
	      (cond ((equal type *int-type*)
		     (push-fifo
		      `(merge ,(e-node-type e-node) ,*int-node* type-of)
		      *merge-list*))
		    ((equal type *bool-type*)
		     (push-fifo
		      `(merge ,(e-node-type e-node) ,*bool-node* type-of)
		      *merge-list*)))))
          e-node))))


;;; Create the representation for arguments of a function application.
(defun intern-function-arguments (rest-of-list)
  (if (null rest-of-list)
      *enil*
    (create-aux-node (intern-subexpression (car rest-of-list))
		     (intern-function-arguments (cdr rest-of-list)))))


(defun intern-integer-operation-sum (e-node expression)
  (unless (aref (e-node-tableau-entry e-node) 1)
    (let* ((sum-0 (collect-terms expression))
	   (sum-1 (negative-sum sum-0)))
      (unless (aref (e-node-tableau-entry e-node) 0)
	(intern-sum e-node 0 sum-0))
      (intern-sum e-node 1 sum-1)
      (intern-sum e-node 2 (opposite-sum sum-1))
      (intern-sum e-node 3 (opposite-sum sum-0)))))


(defun intern-integer-inequality-sum (e-node expression)
  (unless (aref (e-node-tableau-entry e-node) 0)
    (let* ((left (>=-left expression))
	   (right (>=-right expression))
	   (initial-sum (collect-terms (make-- left right)))
	   (sum-0 (make-stronger (collect-terms (make-- left right))))
	   (sum-1 (opposite-sum sum-0))
           (the-gcd (apply #'gcd (mapcar #'cdr (cdr initial-sum)))))
      (unless (and (> the-gcd 1)
                   (not (zerop (rem (car initial-sum) the-gcd))))
	(setf (e-node-not-shifted e-node)
              t))	; inequality not shifted in rationals.
      (intern-sum e-node 0 sum-0)
      (intern-sum e-node 1 sum-1)
      (check-if-manifestly-negative (cons 0 e-node))
      (check-if-manifestly-negative (cons 1 e-node)))))


(defun intern-integer-equality-sum (e-node expression)
  (unless (aref (e-node-tableau-entry e-node) 0)
    (let* ((left (=-left expression))
	   (right (=-right expression))
	   (sum (collect-terms (make-- left right)))
	   (the-gcd (apply #'gcd (mapcar #'cdr (cdr sum)))))
      (cond ((or (zerop (car sum))
                 (and (cdr sum) (zerop (rem (car sum) the-gcd))))
	     (let* ((sum-0 (if (or (zerop (car sum)) (= the-gcd 1)) sum
			       (cons (quotient (car sum) the-gcd)
				     (mapcar
				       #'(lambda (u)
					   (cons (car u)
                                                 (quotient (cdr u) the-gcd)))
				       (cdr sum)))))
		    (sum-1 (negative-sum sum-0))
		    (sum-2 (opposite-sum sum-1))
		    (sum-3 (opposite-sum sum-0)))
	       (intern-sum e-node 0 sum-0)
	       (intern-sum e-node 1 sum-1)
	       (intern-sum e-node 2 sum-2)
	       (intern-sum e-node 3 sum-3)))
	    (t (push-fifo (list 'merge e-node *false-node*
                                (list '=-no-integer-solution sum))
                          *merge-list*))))))



;;; swap-samecar put swaps the samecars of the nodes

(defun swap-samecar (node1 node2)
  (push-undo (list #'undo-swap-samecar node1 node2))
  (swapf (e-node-samecar node1) (e-node-samecar node2)))

(defun swap-samecdr (node1 node2)
  (push-undo (list #'undo-swap-samecdr node1 node2))
  (swapf (e-node-samecdr node1) (e-node-samecdr node2)))

(defun swap-samecar-aux (node1 node2)
  (push-undo (list #'undo-swap-samecar-aux node1 node2))
  (swapf (aux-node-samecar node1) (aux-node-samecar node2)))

(defun swap-samecdr-aux (node1 node2)
  (push-undo (list #'undo-swap-samecdr-aux node1 node2))
  (swapf (aux-node-samecdr node1) (aux-node-samecdr node2)))



;;; Check to see if an e-node with the specified ecar and ecdr is already
;;; in the egraph in the same samecdr circle as v's.  If it is already in
;;; the egraph, then the e-node is returned; otherwise nil is returned.
(defun find-e-node (v its-ecar its-ecdr)
  (loop-over-nodes (next-v v e-node-samecdr)
    (and (eq (e-node-ecar next-v) its-ecar)
	 (eq (e-node-ecdr next-v) its-ecdr)
	 (return next-v))))

;;; Check to see if an aux-node with the specified ecar and ecdr is already
;;; in the egraph in the same samecdr circle as v's.  If it is already in
;;; the egraph, then the aux-node is returned; otherwise nil is returned.
(defun find-aux-node (v its-ecar its-ecdr)
  (loop-over-nodes (next-v v aux-node-samecdr)
    (and (eq (aux-node-ecar next-v) its-ecar)
	 (eq (aux-node-ecdr next-v) its-ecdr)
	 (return next-v))))

;;; Check to see if the new e-node should belong to an existing
;;; equivalent class. Put it in the class if so.
(defun check-for-equivalence (node)
  (let ((ecar-root (e-node-root (e-node-ecar node)))
	(ecdr-root (aux-node-root (e-node-ecdr node))))
    (or (loop-over-nodes-excluding (v node e-node-samecdr)
	  (when (eq (e-node-root (e-node-ecar v)) ecar-root)
	    (return (push-fifo (list 'merge node v 'congruence)
                               *merge-list*))))
	(loop-over-nodes-excluding (u node e-node-samecar)
	  (when (eq (aux-node-root (e-node-ecdr u)) ecdr-root)
	    (return (push-fifo (list 'merge node u 'congruence)
                               *merge-list*)))))))

;;; Check to see if the new aux-node should belong to an existing
;;; equivalent class. Put it in the class if so.
(defun check-for-equivalence-aux (node)
  (let ((ecar-root (e-node-root (aux-node-ecar node)))
	(ecdr-root (aux-node-root (aux-node-ecdr node))))
    (or (loop-over-nodes-excluding (v node aux-node-samecdr)
	  (when (eq (e-node-root (aux-node-ecar v)) ecar-root)
	    (return (push-fifo (list 'merge-aux node v nil)
                               *merge-list*))))
	(loop-over-nodes-excluding (u node aux-node-samecar)
	  (when (eq (aux-node-root (aux-node-ecdr u)) ecdr-root)
	    (return (push-fifo (list 'merge-aux node u nil)
                               *merge-list*)))))))
