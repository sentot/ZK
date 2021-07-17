
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

;;; ==================== Reset Egraph and Tableau ====================


;;; ---------- Top Level Reset ----------

(defun reset-deductive-database ()
  (declare (special *pending-assumptions-stack*))
  (setq *inconsistent* nil)
  (setq *undo-stack* nil *pending-assumptions-stack* nil)
  (setq *instantiation-list* nil)
  (setq *substitution-list* nil)
  (reset-e-graph))


;;; Reset the Egraph.
(defun reset-e-graph ()
  ;; Clear tables.
  (setq *variable-symbols* nil)
  (clear-integer-expression-table)
  (clear-symbol-expression-table)
  (clear-debruijn-table)
  (clear-quantification-table)
  ;; Predefined nodes.
  (setq *enil* (make-auxiliary-node nil nil))
  (setq *bool-node*
        (make-special-node 'bool (make-an-e-node nil nil (gensym) nil)))
  (setq *int-node*
        (make-special-node 'int (make-an-e-node nil nil (gensym) nil)))
  (setq *true-node* (make-special-node 'true *bool-node*))
  (setq *false-node* (make-special-node 'false *bool-node*))
  (setq *type-of-node* (make-type-of-node))
  (setq *zero-node* (make-zero-node))
  (setq *one-node* (make-one-node))
  (setq *merge-list* nil)
  ;; Also reset the tableau.
  (reset-tableau)
  ;; Initial non-equalities.
  (add-forbid *bool-node* *int-node*
              (list *bool-node* *int-node* 'bool-not-int))
  (add-forbid *int-node* *bool-node*
              (list *int-node* *bool-node* 'bool-not-int))
  (add-forbid *true-node* *false-node*
              (list *true-node* *false-node* 'true-not-false))
  (add-forbid *false-node* *true-node*
              (list *false-node* *true-node* 'true-not-false))
  ;; Initial equalities.
  (merge-nodes (create-e-node
		*type-of-node*
		(create-aux-node *true-node* *enil*)
		(make-type-of *true*)
		(make-an-e-node nil nil (gensym) nil))
	       *bool-node*
	       'true-is-bool)
  (merge-nodes (create-e-node
		*type-of-node*
		(create-aux-node *false-node* *enil*)
		(make-type-of *false*)
		(make-an-e-node nil nil (gensym) nil))
	       *bool-node*
	       'false-is-bool)
  (merge-nodes (create-e-node
		*type-of-node*
		(create-aux-node *zero-node* *enil*)
		(make-type-of 0)
		(make-an-e-node nil nil (gensym) nil))
	       *int-node*
	       'zero-is-int)
  (merge-nodes (create-e-node
		*type-of-node*
		(create-aux-node *one-node* *enil*)
		(make-type-of 1)
		(make-an-e-node nil nil (gensym) nil))
	       *int-node*
	       'one-is-int))

;;; Reset the tableau.
(defun reset-tableau ()
  (setq *rows* (initialize-rows))
  (setq *cols* (initialize-columns))
  (setq *tableau-list* nil))
