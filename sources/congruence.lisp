
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


;;; An implementation of an enhanced version of the congruence closure
;;; algorithm, based on the algorithm in Greg Nelson's thesis.

;;; The algorithm is incremental and "undoable": merges and forbids
;;; may be performed incrementally and may be undone incrementally.

;;; In addition to being a decision procedure for the theory of
;;; equalities with uninterpreted function symbols, the algorithm
;;; cooperates with a tableau for integer reasoning by propagating
;;; equalities to the tableau. The algorithm can also be "programmed"
;;; using frules and grules to become decision procedures or
;;; near decision procedures for various simple theories including
;;; constructor-accessor type of theories.


;;; ==================== Top Level ====================


;;; The top level function is process-merge-list.

;;; Perform merges and forbids as specified by "to do" entries in *merge-list*.
;;; Note that calling merge-pair-of-nodes or forbid-merge may result in new
;;; "to do" entries added to *merge-list* and/or *tableau-list*.
(defun process-merge-list ()
  (loop while (and *merge-list* (not *inconsistent*))
	do
	(let ((entry (pop-fifo *merge-list*)))
	  (let ((entry-kind (first entry))
		(arg-1 (second entry))
		(arg-2 (third entry))
		(justification (fourth entry)))
	    (cond
	     ((eq entry-kind 'merge)
	      (merge-e-nodes arg-1 arg-2 justification))
	     ((eq entry-kind 'merge-aux)
	      (merge-aux-nodes arg-1 arg-2))
	     ((eq entry-kind 'forbid)
	      (forbid-merge arg-1 arg-2 justification))
	     ((eq entry-kind 'create-integer-and-merge)
	      (merge-e-nodes
	       (intern-integer arg-1) arg-2 justification)))))))

;;; ==================== End of Top Level ====================


;;; -------------------- Helper Functions --------------------

;;; Check if the merge of two e-node classes is forbidden (by checking
;;; to see if one of the classes appear in the other's forbid list).
(defun check-forbid (u v)
  (let* ((u-root (e-node-root u))
	 (v-root (e-node-root v))
	 (p (e-node-forbid u-root))
	 (q (e-node-forbid v-root)))
    (and p q (or (eq (e-node-root (fnode-enode p)) v-root)
		 (eq (e-node-root (fnode-enode q)) u-root)
		 (do ((plink (fnode-link p) (fnode-link plink)))
		     ((eq (fnode-link plink) plink)
		      (eq (e-node-root (fnode-enode plink)) v-root))
		     (when (eq (e-node-root (fnode-enode plink)) v-root)
		       (return t)))
		 (do ((qlink (fnode-link q) (fnode-link qlink)))
		     ((eq (fnode-link qlink) qlink)
		      (eq (e-node-root (fnode-enode qlink)) u-root))
		     (when (eq (e-node-root (fnode-enode qlink)) u-root)
		       (return t)))))))

;;; Integrate an equality expression derived from merging e-nodes into the
;;; deductive database.
(defun intern-derived-equality (e1 e2)
  (intern-subexpression (make-= (e-node-attribute e1)
                                   (e-node-attribute e2))))

;;; -------------------- End of Helper Functions --------------------



;;; ==================== Propagate Merges (Internal) ====================



;;; Propagate merges to predecessor nodes, as part of a decision
;;; procedure for the theory of equalities with uninterpreted function
;;; symbols. There are 4 kinds of propagation to predecessor nodes:
;;; - aux-nodes to e-nodes,
;;; - e-nodes to e-nodes,
;;; - aux-nodes to aux-nodes,
;;; - e-nodes to aux-nodes.

;;; --------------- Mark, Merge, Unmark ---------------

;;; Each kind of propagation is performed by 3 functions:
;;; - a setup function (prefixed with "mark") that sets back pointers,
;;; - a processing function (prefixed with "merge"),
;;; - a cleanup function (prefixed with "unmark") that clears back pointers.

;;; ----- case 1: from an aux-node to e-nodes
;;; Check e-nodes with same ecdr to see if it has equivalent ecar.

(defsubst mark-predecessors-ecar (e1)
  (loop-over-nodes (e e1 e-node-samecdr)
    (setf (e-node-back (e-node-root (e-node-ecar e))) e)))

(defsubst merge-predecessors-ecar (e2)
  (loop-over-nodes (e e2 e-node-samecdr)
    (let ((back (e-node-back (e-node-root (e-node-ecar e)))))
      (or (null back)
          (push-fifo (list 'merge e back 'congruence) *merge-list*)))))

(defsubst unmark-predecessors-ecar (e1)
  (loop-over-nodes (e e1 e-node-samecdr)
    (setf (e-node-back (e-node-root (e-node-ecar e))) nil)))

;;; ----- case 2: from an e-node to e-nodes
;;; Check e-nodes with same ecar to see if it has equivalent ecdr.

(defsubst mark-predecessors-ecdr (e1)
  (loop-over-nodes (e e1 e-node-samecar)
    (setf (aux-node-back (aux-node-root (e-node-ecdr e))) e)))

(defsubst merge-predecessors-ecdr (e2)
  (loop-over-nodes (e e2 e-node-samecar)
    (let ((back (aux-node-back (aux-node-root (e-node-ecdr e)))))
      (or (null back)
          (push-fifo (list 'merge e back 'congruence) *merge-list*)))))

(defsubst unmark-predecessors-ecdr (e1)
  (loop-over-nodes (e e1 e-node-samecar)
    (setf (aux-node-back (aux-node-root (e-node-ecdr e))) nil)))

;;; ----- case 3: from an aux-node to aux-nodes
;;; Check aux-nodes with same ecdr to see if it has equivalent ecar.

(defsubst mark-predecessors-ecar-aux (e1)
  (loop-over-nodes (e e1 aux-node-samecdr)
    (setf (e-node-back (e-node-root (aux-node-ecar e))) e)))

(defsubst merge-predecessors-ecar-aux (e2)
  (loop-over-nodes (e e2 aux-node-samecdr)
    (let ((back (e-node-back (e-node-root (aux-node-ecar e)))))
      (or (null back)
          (push-fifo (list 'merge-aux e back nil) *merge-list*)))))

(defsubst unmark-predecessors-ecar-aux (e1)
  (loop-over-nodes (e e1 aux-node-samecdr)
    (setf (e-node-back (e-node-root (aux-node-ecar e))) nil)))

;;; ----- case 4: from an e-node to aux-nodes
;;; Check aux-nodes with same ecar to see if it has equivalent ecdr.

(defsubst mark-predecessors-ecdr-aux (e1)
  (loop-over-nodes (e e1 aux-node-samecar)
    (setf (aux-node-back (aux-node-root (aux-node-ecdr e))) e)))

(defsubst merge-predecessors-ecdr-aux (e2)
  (loop-over-nodes (e e2 aux-node-samecar)
    (let ((back (aux-node-back (aux-node-root (aux-node-ecdr e)))))
      (or (null back) (push-fifo (list 'merge-aux e back nil) *merge-list*)))))

(defsubst unmark-predecessors-ecdr-aux (e1)
  (loop-over-nodes (e e1 aux-node-samecar)
    (setf (aux-node-back (aux-node-root (aux-node-ecdr e))) nil)))

;;; --------------- End of Mark, Merge, Unmark ---------------



;;; --------------- Check and Propagate ---------------

;;; Check to see if need to propagate before calling actual propagation
;;; code. In each of the 4 cases, u and v are roots of original classes
;;; and v is the root of the resulting class.

;;; ----- case 1: from aux-nodes to e-nodes

(defsubst check-e-pred-aux (u v)
  (let ((u-pred (aux-node-e-pred u)) (v-pred (aux-node-e-pred v)))
    (cond ((null u-pred) t)		; Nothing to do.
	  ((null v-pred)		; Set pred of the new class.
           (push-undo (list #'undo-set-e-pred-aux v))
	   (setf (aux-node-e-pred v) u-pred))
	  (t
	   ;; Both u and v have predecessors.
	   (mark-predecessors-ecar u-pred)
	   ;; Merge predecessorss that have equivalent ecar.
	   (merge-predecessors-ecar v-pred)
	   (unmark-predecessors-ecar u-pred)
	   ;; Adjust samecdr of the merged u and v.
	   (push-undo (list #'undo-swap-samecdr u-pred v-pred))
	   (swapf (e-node-samecdr u-pred) (e-node-samecdr v-pred))))))

;;; ----- case 2: from e-nodes to e-nodes

(defsubst check-e-pred (u v)
  (let ((u-pred (e-node-e-pred u)) (v-pred (e-node-e-pred v)))
    (cond ((null u-pred) t)		; Nothing to do.
	  ((null v-pred)		; Set pred of the new class.
           (push-undo (list #'undo-set-e-pred v))
	   (setf (e-node-e-pred v) u-pred))
	  (t
	   ;; Both u and v have predecessors.
	   (mark-predecessors-ecdr u-pred)
	   ;; Merge predecessorss that have equivalent ecdr.
	   (merge-predecessors-ecdr v-pred)
	   (unmark-predecessors-ecdr u-pred)
	   ;; Adjust samecar of the merged u and v.
	   (push-undo (list #'undo-swap-samecar u-pred v-pred))
	   (swapf (e-node-samecar u-pred) (e-node-samecar v-pred))))))

;;; ----- case 3: from aux-nodes to aux-nodes

(defsubst check-aux-pred-aux (u v)
  (let ((u-pred (aux-node-aux-pred u)) (v-pred (aux-node-aux-pred v)))
    (cond ((null u-pred) t)		; Nothing to do.
	  ((null v-pred)		; Set pred of the new class.
           (push-undo (list #'undo-set-aux-pred-aux v))
	   (setf (aux-node-aux-pred v) u-pred))
	  (t
	   ;; Both u and v have predecessors.
	   (mark-predecessors-ecar-aux u-pred)
	   ;; Merge predecessorss that have equivalent ecar.
	   (merge-predecessors-ecar-aux v-pred)
	   (unmark-predecessors-ecar-aux u-pred)
	   ;; Adjust samecdr of the merged u and v.
	   (push-undo (list #'undo-swap-samecdr-aux u-pred v-pred))
	   (swapf (aux-node-samecdr u-pred) (aux-node-samecdr v-pred))))))

;;; ----- case 4: from e-nodes to aux-nodes

(defsubst check-aux-pred (u v)
  (let ((u-pred (e-node-aux-pred u)) (v-pred (e-node-aux-pred v)))
    (cond ((null u-pred) t)		; Nothing to do.
	  ((null v-pred)		; Set pred of the new class.
           (push-undo (list #'undo-set-aux-pred v))
	   (setf (e-node-aux-pred v) u-pred))
	  (t
	   ;; Both u and v have predecessors.
	   (mark-predecessors-ecdr-aux u-pred)
	   ;; Merge predecessorss that have equivalent ecdr.
	   (merge-predecessors-ecdr-aux v-pred)
	   (unmark-predecessors-ecdr-aux u-pred)
	   ;; Adjust samecar of the merged u and v.
	   (push-undo (list #'undo-swap-samecar-aux u-pred v-pred))
	   (swapf (aux-node-samecar u-pred) (aux-node-samecar v-pred))))))

;;; --------------- End of Check and Propagate ---------------

;;; =============== End of Propagate Merges (Internal) ===============



;;; ==================== Merge Nodes ====================


;;; Merge the e-node class of e-node u with the e-node-class of e-node v
;;; producing a single e-node class. Root of the bigger class becomes the
;;; new root, unless the classes are of the same size, in which case
;;; the root of v's class becomes the new root.
(defun merge-e-nodes (u v justification)
  (let ((u1 (e-node-root u)) (v1 (e-node-root v)))
    (unless (eq u1 v1)			; Nothing to do if the same class.
      ;; Swap if needed so class of v not smaller than class of u.
      (cond ((> (e-node-size u1)
		(e-node-size v1))
	     (swapf u1 v1)
             (swapf u v)))
      ;; Check forbids for consistency.
      (cond ((null (e-node-forbid u1)) t)
	    ((null (e-node-forbid v1))
	     ;; Set forbid.
	     (setf (e-node-forbid v1) (e-node-forbid u1)))
	    ((check-forbid u1 v1)
	     ;; Merge is forbidden,
	     (set-inconsistent (list 'merge-forbid u v justification
                                     (get-forbid-justification u1 v1))))
	    (t
	     ;; Merge is not forbidden, merge the forbids.
	     (do ((l (e-node-forbid v1) (fnode-link l)))
		 ((eq l (fnode-link l))
		  (setf (fnode-link l) (e-node-forbid u1))))))
      (unless *inconsistent*
	;; Modify witness information.
	(reverse-witness-links u u1)
        (push-undo (list #'undo-reverse-witness u u1))
        (setf (e-node-witness-link u) v)
        (setf (e-node-witness-info u) justification)
        (when (eq u u1) (push-undo (list #'undo-set-witness u)))
	;; Propagate merge at the level of cooperating decision procedures.
        (propagate-merge u1 v1)
	;; Do the union.
	(class-union u1 v1)
	(push-undo (list #'undo-merge u1))
	;; Check and propagate merge at the level of congruence closure
	;; (propagate to predecessors).
	(check-e-pred u1 v1)
	(check-aux-pred u1 v1)))))

;;; Merge aux-node class of u with aux-node class of v.
(defun merge-aux-nodes (u v)
  (let ((u1 (aux-node-root u)) (v1 (aux-node-root v)))
    (unless (eq u1 v1)			; Nothing to do if the same class.
      ;; Swap if needed to make v1's class the bigger class.
      (cond ((> (aux-node-size u1)
		(aux-node-size v1))
	     (swapf u1 v1)))
      ;; Do the union.
      (class-union-aux u1 v1)
      (push-undo (list #'undo-merge-aux u1))
      ;; Check and propagate merge.
      (check-e-pred-aux u1 v1)
      (check-aux-pred-aux u1 v1))))



;;; Perform union of the class of u and the class of v.
;;; The root of the class of v becomes the root of the union class.
(defun class-union (u v)
  ;; Reroot the first old class.
  (reroot u v)
  ;; Adjust the size.
  (setf (e-node-size v)
	(+ (e-node-size u) (e-node-size v)))
  ;; Perform the union (splice together two circular lists).
  (swapf (e-node-eqclass u) (e-node-eqclass v)))

;;; Reroot the class of e-node u.
(defun reroot (u new-root)
  (loop-over-nodes (v u e-node-eqclass)
    (setf (e-node-root v) new-root)))

;;; Union of classes of aux-nodes.
(defun class-union-aux (u v)
  ;; Reroot the first old class.
  (reroot-aux u v)
  ;; Adjust the size.
  (setf (aux-node-size v)
	(+ (aux-node-size u) (aux-node-size v)))
  ;; Splice together the two class circular lists.
  (swapf (aux-node-eqclass u) (aux-node-eqclass v)))

;;; Reroot the class of aux-node u.
(defun reroot-aux (u new-root)
  (loop-over-nodes (v u aux-node-eqclass)
    (setf (aux-node-root v) new-root)))

(proclaim '(special *reduce-statistics*))

;;; Code to apply forward rules.

;;; Apply matching frules that are enabled, have the right sense, and
;;; accessible..
(defun apply-frules (e-node negate justification)
  (let ((expr (e-node-attribute e-node)))
    (unless (atom expr)
      ;; Get potentially matching frules.
      (let ((frules (get-frules expr)))
	;; Go through the frules.
	(dolist (frule frules)
	  ;; Enabled, right sense and accessible?
	  (when (and (frule-enabled frule)
		     (eq negate (frule-negate frule))
		     (not (event-inaccessible-p frule)))
	    ;; Does frule match?
	    (multiple-value-bind (substitutions match-success)
		(match-pattern-formula (frule-pattern frule) expr)
	     (when match-success
	       ;; Success, apply the frule.
	       (incf (stat-forward *reduce-statistics*))
	       (update-frules frule)
               (let ((i 0))
		 (dolist (v (frule-values frule))
                   (let ((node (intern-subexpression
				(sublis-eq substitutions (car v)))))
		     (push-fifo
		      (list (if (cdr v) 'forbid 'merge)
			    node *true-node*
			    (list 'frule e-node node frule i substitutions
				  justification))
		      *merge-list*))
		   (incf i)))))))))))

;;; ==================== End of Merge Nodes ====================



;;; ========== Propagate Merges (Cooperating DPs) ===========

;;; Propagate merges to *merge-list* and/or *tableau-list* resulting from
;;; a merge of e-node classes. This is needed to get cooperating DPs.
(defun propagate-merge (u v)
  (let ((true-root (e-node-root *true-node*))
	(false-root (e-node-root *false-node*))
	(zero-root (e-node-root *zero-node*)))
    (cond
      ((eq u true-root) (propagate-merge-true v))
      ((eq v true-root) (propagate-merge-true u))
      ((eq u false-root) (propagate-merge-false v))
      ((eq v false-root) (propagate-merge-false u))
      ((eq u zero-root) (propagate-merge-zero v))
      ((eq v zero-root) (propagate-merge-zero u))
      ((eq u (e-node-root *int-node*)) (propagate-int-node v))
      ((eq v (e-node-root *int-node*)) (propagate-int-node u))
      ((or (equiv-to-node-int-p u) (equiv-to-node-int-p v))
       (let ((*-node (e-node-e-pred (intern-symbol '*))))
	 (and *-node
	      (loop-over-nodes (next *-node e-node-samecar)
		(when (or (and (eq (e-node-root (arg-1-node next)) u)
			       (eq (e-node-root (arg-2-node next)) v))
			  (and (eq (e-node-root (arg-1-node next)) v)
			       (eq (e-node-root (arg-2-node next)) u)))
		  (return (push-fifo (list 'restrict next 0
                                           (list 'square-nonneg next))
                                     *tableau-list*))))))
       (or (loop-over-nodes-excluding (node *zero-node* e-node-eqclass)
	     (when (and (eq (e-node-operation node) '*)
			(or (and (eq (e-node-root (arg-1-node node)) u)
				 (eq (e-node-root (arg-2-node node)) v))
			    (and (eq (e-node-root (arg-1-node node)) v)
				 (eq (e-node-root (arg-2-node node)) u))))
	       (return (push-fifo (list 'merge u *zero-node*
                                        (list 'square-zero node))
                                  *merge-list*))))
           (let ((node (intern-derived-equality u v)))
             (push-fifo (list 'merge node *true-node* '=-equal-arguments)
                        *merge-list*)))))
    (let ((=-node (e-node-e-pred (intern-symbol '=))))
      (and =-node
           (loop-over-nodes (next =-node e-node-samecar)
             (when (or (and (eq (e-node-root (arg-1-node next)) u)
                            (eq (e-node-root (arg-2-node next)) v))
                       (and (eq (e-node-root (arg-1-node next)) v)
                            (eq (e-node-root (arg-2-node next)) u)))
               (push-fifo (list 'merge next *true-node* '=-equal-arguments)
                          *merge-list*)))))))

(defun equiv-to-node-int-p (e-node)
  (loop-over-nodes (next e-node e-node-eqclass)
    (when (node-int-p next) (return t))))


;;; Propagate merges resulting from merging an e-node with the e-node
;;; for (TRUE).
(defun propagate-merge-true (e)
  (loop-over-nodes (e1 e e-node-eqclass)
    (apply-frules e1 nil nil)
    (case (e-node-operation e1)
      (= (when (aref (e-node-tableau-entry e1) 0)
	   (push-fifo (list 'kill e1 (list '=-true e1)) *tableau-list*))
	 (push-fifo
          (list 'merge (arg-1-node e1) (arg-2-node e1) (list '=-true e1))
          *merge-list*))
      (>= (when (aref (e-node-tableau-entry e1) 0)
	    (push-fifo (list 'restrict e1 0 (list '>=-true e1))
                       *tableau-list*)))
      (in (when (type-predicate-p (e-node-attribute e1))
	    (push-fifo
             (list 'merge (arg-2-node e1) (e-node-type (arg-1-node e1))
                   (list 'in-=-type-of e1))
             *merge-list*))))))




;;; Propagate merges resulting from merging an e-node with the e-node
;;; for (FALSE).
(defun propagate-merge-false (e)
  (loop-over-nodes (e1 e e-node-eqclass)
    (apply-frules e1 t (list *false-node* *true-node* 'true-not-false))
    (case (e-node-operation e1)
      (= (when (aref (e-node-tableau-entry e1) 0)
	   (check-and-shift-restriction e1))
	 (push-fifo (list 'forbid (arg-1-node e1) (arg-2-node e1)
                          (list '=-false e1))
                    *merge-list*))
      (>= (when (aref (e-node-tableau-entry e1) 0)
	    (push-fifo (list 'restrict e1 1 (list '>=-false e1))
                       *tableau-list*)))
      (in (when (type-predicate-p (e-node-attribute e1))
	    (push-fifo
             (list 'forbid (arg-2-node e1) (e-node-type (arg-1-node e1))
                   (list 'type-predicate e1))
             *merge-list*))))))

;;; Check to see if a non-equality shifts an inequality (i.e. make it a
;;; strict one), with node representing an equality being denied
(defun check-and-shift-restriction (node)
  (let ((header1 (aref (e-node-tableau-entry node) 0)))
    (cond
      ((row-p header1)
       (if (eq (row-restriction header1) 'restricted)
	   (push-fifo (list 'restrict node 2 (list 'shift node 0))
                      *tableau-list*)
	   (let ((header2 (aref (e-node-tableau-entry node) 1)))
	     (if (row-p header2)
		 (when (eq (row-restriction header2) 'restricted)
		   (push-fifo (list 'restrict node 3 (list 'shift node 1))
                              *tableau-list*))
		 (when (eq (col-restriction header2) 'restricted)
		   (push-fifo (list 'restrict node 3 (list 'shift node 1))
                              *tableau-list*))))))
      ((col-p header1)
       (if (eq (col-restriction header1) 'restricted)
	   (push-fifo (list 'restrict node 2 (list 'shift node 0))
                      *tableau-list*)
	   (let ((header2 (aref (e-node-tableau-entry node) 1)))
	     (if (row-p header2)
		 (when (eq (row-restriction header2) 'restricted)
		   (push-fifo (list 'restrict node 3 (list 'shift node 1))
                              *tableau-list*))
		 (when (eq (col-restriction header2) 'restricted)
		   (push-fifo (list 'restrict node 3 (list 'shift node 1))
                              *tableau-list*)))))))))


;;; Propagate merges resulting from merging an e-node with the e-node for 0.
(defun propagate-merge-zero (v)
  (when (aref (e-node-tableau-entry v) 0)
    (push-fifo (list 'kill v (list 'zero v)) *tableau-list*))
  (loop-over-nodes (v1 v e-node-eqclass)
    (when (eq (e-node-operation v1) '*)
      (let ((left-node (arg-1-node v1))
	    (right-node (arg-2-node v1)))
	(cond ((eq (e-node-root left-node) (e-node-root right-node))
	       (push-fifo (list 'merge left-node *zero-node*
                                (list 'square-zero v1))
                          *merge-list*))
	      ((and (node-int-p left-node) (node-int-p right-node)
                    (check-forbid left-node *zero-node*))
               (push-fifo (list 'merge right-node *zero-node*
                                (list 'product-zero-right v1
                                      (get-forbid-justification
                                       left-node *zero-node*)))
                          *merge-list*))
	      ((and (node-int-p left-node) (node-int-p right-node)
                    (check-forbid right-node *zero-node*))
               (push-fifo (list 'merge left-node *zero-node*
                                (list 'product-zero-left v1
                                      (get-forbid-justification
                                       right-node *zero-node*)))
                          *merge-list*))))))
  (let ((pred-v (e-node-aux-pred v)))
    (when pred-v
      (loop-over-nodes (v1 pred-v aux-node-samecar)
	(make-products-zero v1)))))

;;; Make products with the expression represented by v zero because
;;; v represents an expression that currently has a value of 0.
(defun make-products-zero (v)
  (let ((e-pred-v (aux-node-e-pred v))
	(aux-pred-v (aux-node-aux-pred v)))
    (when e-pred-v ; first argument is zero
      (loop-over-nodes (v1 e-pred-v e-node-samecdr)
	(when (eq (e-node-operation v1) '*)
	  (push-fifo (list 'merge v1 *zero-node* 'times-zero-left)
                     *merge-list*))))
    (when aux-pred-v ; second argument is zero
      (loop-over-nodes (v1 aux-pred-v aux-node-samecdr)
	(let ((v2 (aux-node-e-pred v1)))
	  (when (and v2 (eq (e-node-operation v2) '*))
	    (push-fifo (list 'merge v2 *zero-node* 'times-zero-right)
                       *merge-list*)))))))

;;; Propagate merges resulting from merging an e-node with the e-node for (INT).
(defun propagate-int-node (node)
  (loop-over-nodes (u node e-node-eqclass)
    (when (type-of-p (e-node-attribute u))
      (let* ((e-node (arg-1-node u))
             (expr (e-node-attribute e-node)))
        (unless (ord-p expr)
          (let ((ord-node (intern-subexpression (make-ord expr)))
                (=-node (e-node-e-pred (intern-symbol '=))))
            (and =-node
                 (loop-over-nodes (next =-node e-node-samecar)
                   (when (or (eq (arg-1-node next) e-node)
                             (eq (arg-2-node next) e-node))
                     (let* ((args (mapcar #'wrap-ord
                                          (cdr (e-node-attribute next))))
                            (cdr-node (intern-function-arguments args))
                            (=-expr-node
                             (create-e-node (intern-symbol '=) cdr-node
					    (cons '= args) nil)))
                       (setf (e-node-type =-expr-node)
                             (create-type-of-node =-expr-node))
                       (setf (e-node-operation =-expr-node) '=)
                       (intern-integer-equality-sum
                        =-expr-node (e-node-attribute next))
                       (push-fifo (list 'merge (e-node-type =-expr-node)
                                        *bool-node* 'type-of)
                                  *merge-list*)))))
            (push-fifo (list 'merge ord-node e-node 'ord-int)
                       *merge-list*)))))))

;;; ========== End of Propagate Merges (Cooperating DPs) ===========



;;; ==================== Forbid Merge ====================

;;; Forbid the merge of u and v.
(defun forbid-merge (u v justification)
  (let ((u1 (e-node-root u)) (v1 (e-node-root v)))
    (cond ((eq u1 v1)
           (set-inconsistent
            (list 'forbid-merge u v (list u v justification))))
	  ((null (check-forbid u1 v1))
	   (add-forbid u1 v1 (list u v justification))
	   (add-forbid v1 u1 (list u v justification))
	   (push-undo (list #'undo-forbid u1))
	   (propagate-forbid-merge u1 v1 (list u v justification))))))


;;; Propagate information via *merge-list* and/or *tableau-list*
;;; resulting from a forbid merge.
(defun propagate-forbid-merge (u v justification)
  (cond
    ((eq u (e-node-root *zero-node*))
     (propagate-forbid-merge-zero v justification))
    ((eq v (e-node-root *zero-node*))
     (propagate-forbid-merge-zero u justification))
    ((and (eq u (e-node-root *true-node*)) (node-bool-p v))
     (push-fifo (list 'merge v *false-node* (list 'forbid-true justification))
                *merge-list*))
    ((and (eq v (e-node-root *true-node*)) (node-bool-p u))
     (push-fifo (list 'merge u *false-node* (list 'forbid-true justification))
                *merge-list*))
    ((and (eq u (e-node-root *false-node*)) (node-bool-p v))
     (push-fifo (list 'merge v *true-node* (list 'forbid-false justification))
                *merge-list*))
    ((and (eq v (e-node-root *false-node*)) (node-bool-p u))
     (push-fifo (list 'merge u *true-node* (list 'forbid-false justification))
                *merge-list*))
    (t (when (and (equiv-to-node-int-p u) (equiv-to-node-int-p v))
         (let ((node (intern-derived-equality u v)))
           (push-fifo (list 'merge *false-node* node
                            (list '=-forbid-arguments justification))
                      *merge-list*)))
       (cond ((eq v (e-node-root *true-node*))
	      (loop-over-nodes (u1 u e-node-eqclass)
		(apply-frules u1 t justification)))
	     ((eq u (e-node-root *true-node*))
	      (loop-over-nodes (v1 v e-node-eqclass)
		(apply-frules v1 t justification)))))))



;;; Propagate information via *merge-list* and/or *tableau-list*
;;; resulting from a forbid merge of u with the node representing 0.
(defun propagate-forbid-merge-zero (u justification)
  (let ((node (intern-derived-equality u *zero-node*)))
    (push-fifo (list 'merge node *false-node*
                     (list 'forbid-zero justification))
               *merge-list*))
  (loop-over-nodes-excluding (node *zero-node* e-node-eqclass)
    (when (eq (e-node-operation node) '*)
      (cond ((and (eq (e-node-root (arg-1-node node)) u)
                  (node-int-p (arg-1-node node))
                  (node-int-p (arg-2-node node)))
             (push-fifo (list 'merge (arg-2-node node) *zero-node*
                              (list 'product-zero-right node justification))
                        *merge-list*))
	    ((and (eq (e-node-root (arg-2-node node)) u)
                  (node-int-p (arg-1-node node))
                  (node-int-p (arg-2-node node)))
             (push-fifo (list 'merge (arg-1-node node) *zero-node*
                              (list 'product-zero-left node justification))
                        *merge-list*))))))
