
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


;;; ==================== Undo Functions ====================

;;; Needed Files: data-structure, pivot

;;; Various undo functions that get pushed along with their arguments
;;; onto *undo-stack*.

;;; These functions undo e-graph/tableau operations.

(defun undo-set-type (e-node type)
  (setf (e-node-type e-node) type))

(defun undo-inconsistent (saved-value)
  (setq *inconsistent* saved-value))

(defun undo-set-e-pred (e-node)
  (setf (e-node-e-pred e-node) nil))

(defun undo-set-aux-pred (e-node)
  (setf (e-node-aux-pred e-node) nil))

(defun undo-set-e-pred-aux (aux-node)
  (setf (aux-node-e-pred aux-node) nil))

(defun undo-set-aux-pred-aux (aux-node)
  (setf (aux-node-aux-pred aux-node) nil))

(defun undo-swap-samecar (u v)
  (swapf (e-node-samecar u) (e-node-samecar v)))

(defun undo-swap-samecdr (u v)
  (swapf (e-node-samecdr u) (e-node-samecdr v)))

(defun undo-swap-samecar-aux (u v)
  (swapf (aux-node-samecar u) (aux-node-samecar v)))

(defun undo-swap-samecdr-aux (u v)
  (swapf (aux-node-samecdr u) (aux-node-samecdr v)))

(defun undo-set-grules-applied-p (pair)
  (setf (e-node-grules-applied-p (car pair)) (cdr pair)))

(defun undo-restrict (owner)
  (let ((header (aref (e-node-tableau-entry (cdr owner)) (car owner))))
    (cond ((col-p header)
           (setf (col-restriction header) nil)
           (setf (col-reason-restricted header) nil))
          (t (setf (row-restriction header) nil)
             (setf (row-reason-restricted header) nil)))))

(defun undo-kill (pair)
  (cond ((row-p (car pair))
         (setf (row-restriction (car pair)) (cdr pair))
         (setf (row-reason-killed (car pair)) nil))
        (t (setf (col-restriction (car pair)) (cdr pair))
           (setf (col-reason-killed (car pair)) nil))))

(defun undo-intern-integer-expression (expression)
  (remove-integer-expression-table expression))

(defun undo-intern-symbol-expression (expression)
  (remove-symbol-expression-table expression))

(defun undo-intern-debruijn (expression)
  (remove-debruijn-table expression))

(defun undo-intern-quantification (expression)
  (remove-quantification-table expression))



(defun undo-add-e-node (owner)
  (let ((header (prog1 (aref (e-node-tableau-entry (cdr owner)) (car owner))
		       (setf (aref (e-node-tableau-entry (cdr owner))
                                   (car owner))
                             nil))))
    (cond
      ((row-p header)
       (when (or (neq (aref *rows* (row-index header)) header)
		 (not (equal (pop (row-owners header)) owner)))
	 (error "database in bad state during undo add-e-node"))
       (pop (row-sums header))
       (when (null (row-owners header))
	 (unless (< (row-index header) (fill-pointer *rows*))
	   (error "database in bad state during undo add-e-node"))
	 (unless (zerop (row-index header))
           (delete-row header))))
      (t
       (when (not (equal (pop (col-owners header)) owner))
	 (error "database in bad state during undo add-e-node"))
       (pop (col-sums header))
       (when (and (null (col-owners header))
		  (not (= (col-index header) 0)))
	 (if (null (col-cprev header))
	     (delete-column header)
	     (let ((pivot-element (find-pivot-given-column header)))
	       (pivot pivot-element)
               (unless (zerop (row-index (element-row pivot-element)))
                 (delete-row (element-row pivot-element))))))))))



(defun undo-merge (u)
  (let ((v (e-node-root u)))
    (setf (e-node-size v) (- (e-node-size v) (e-node-size u)))
    (swapf (e-node-eqclass u) (e-node-eqclass v))
    (reroot u u)
    (cond
      ((null (e-node-forbid u)) t)
      ((eq (e-node-forbid u) (e-node-forbid v))
       (setf (e-node-forbid v) nil))
      (t
       (do ((l (e-node-forbid v) (fnode-link l)))
	   ((eq (fnode-link l) (e-node-forbid u)) (setf (fnode-link l) l)))))))


(defun undo-merge-aux (u)
  (let ((v (aux-node-root u)))
    (setf (aux-node-size v) (- (aux-node-size v) (aux-node-size u)))
    (swapf (aux-node-eqclass u) (aux-node-eqclass v))
    (reroot-aux u u)))

(defun undo-forbid (u)
  (undo-add-forbid (fnode-enode (fnode-link (e-node-forbid u))))
  (undo-add-forbid u))

(defun undo-add-forbid (u)
  (let* ((f1 (e-node-forbid u))
	 (f2 (fnode-link f1)))
    (if (eq f2 f1)
	(setf (e-node-forbid u) nil)
	(setf (fnode-link f1)
	      (if (eq (fnode-link f2) f2) f1 (fnode-link f2))))))



(defun undo-chain-rule (goal-node index rules)
  (setf (aref (e-node-chain-rules goal-node) index) rules))


;;; undo the reverse of witness links

(defun undo-reverse-witness (e-node root)
  (reverse-witness-links root e-node))

;;; undo-set-witness simply sets the witness-link and witness-info slots
;;; to nil.

(defun undo-set-witness (e-node)
  (setf (e-node-witness-link e-node) nil)
  (setf (e-node-witness-info e-node) nil))
