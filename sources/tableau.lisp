
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


;;; ========== Tableau for Cooperating Decision Procedures ==========

;;; Implementation of an enhancement of Greg Nelson's simplex-based
;;; tableau for integer reasoning.

;;; Top level routine is process-tableau-list.


;;; ---------------------------------------------------------------------

;;; Global symbols used.

(proclaim '(special *tableau-list* *merge-list* *inconsistent*
                    *true-node* *false-node*))

;;; Iterate over elements of *tableau-list* restricting and/or killing rows
;;; and/or columns based on what the elements specify. Restricting or
;;; killing a row/column may have side effects to the *merge-list* and
;;; *tableau-list* (this is how equalities and inequalities are propagated).
(defun process-tableau-list ()
  (do () ((or (null *tableau-list*) *inconsistent*))
    (let ((cmd (pop-fifo *tableau-list*)))
      (if (eq (first cmd) 'restrict)
	  (restrict (second cmd) (third cmd) (fourth cmd))
	  (kill (second cmd) (third cmd))))))



;;; Restrict a linear sum to be non-negative.
(defun restrict (e-node index justification)
  (let ((header (aref (e-node-tableau-entry e-node) index)))
    (or (null header)
	;; nothing to do if already restricted or dead.
        (and (col-p header) (or (eq (col-restriction header) 'dead)
                                (eq (col-restriction header) 'restricted)
                                (zerop (col-index header))))
        (and (row-p header) (or (eq (row-restriction header) 'dead)
                                (eq (row-restriction header) 'restricted)
                                (zerop (row-index header))))
	;; now the interesting part, it is not yet restricted
        (let ((hdr (if (row-p header) header
                     ;; must be represented by a row to detect non-minimality.
                     (let ((pivot-element
                            (find-pivot-given-column header)))
                       (pivot pivot-element)
                       (element-row pivot-element)))))
          (cond
           ;; Ok to restrict if sample value is strictly positive.
           ((row-is-positive hdr)
            (restrict-row hdr justification))
           ;; Otherwise try to pivot to raise the sample value.
           (t (do ((pivot-element (find-pivot-to-raise hdr)
                                  (find-pivot-to-raise hdr)))
                  (nil)
                  (cond
                   (pivot-element       ; there is a pivot,
                    (pivot pivot-element)
                    (cond
                     ;; Ok to restrict if pivot was on row of concern.
                     ((eq (element-row pivot-element) hdr)
                      (return (restrict-column
                               (element-col pivot-element)
                               justification)))
                     ;; Ok to restrict if sample value strictly positive.
                     ((row-is-positive hdr)
                      (return (restrict-row hdr justification)))))
                   (t (cond
                       ;; Can't pivot and sample value is negative,
                       ;; an inconsistent state.
                       ((row-is-negative hdr)
                        (return (set-inconsistent
                                 (list 'inconsistent-restrictions
                                       'restrict
                                       (car (row-owners hdr))
                                       justification
                                       (justify-maximized hdr)))))
                       ;; Can't pivot, and sample value is 0,
                       ;; tableau is non-minimal, kill the row
		       ;; and propagate equality.
                       (t (kill-row hdr (list 'anti-symmetric
                                              justification
                                              (justify-maximized hdr)))
                          (return (propagate-row-equalities
                                   (minimize-tableau hdr))))))))))))))



;;; Return t if the sample value of the row is strictly positive.
(defun row-is-positive (row-header)
  (let ((el (row-rnext row-header)))
    (and el (zerop (col-index (element-col el)))
         (rational-plusp (element-coeff el)))))

;;; Return t if the sample value of the row is negative.
(defun row-is-negative (row-header)
  (let ((el (row-rnext row-header)))
    (and el (zerop (col-index (element-col el)))
         (rational-minusp (element-coeff el)))))

;;; Return t if row has a non-dead column entry.
(defun row-not-dead (header)
  (do ((el (row-rnext header) (element-rnext el)))
      ((null el) nil)
    (unless (eq (col-restriction (element-col el)) 'dead) (return t))))

;;; Check if a linear sum is restricted or not.
(defun is-restricted (e-node index)
  (let* ((header (aref (e-node-tableau-entry e-node) index))
	 (restriction (cond ((row-p header) (row-restriction header))
			    ((col-p header) (col-restriction header)))))
    (or (eq restriction 'restricted) (eq restriction 'dead))))

;;; Return t if all column entries are restricted and have (strictly)
;;; positive coefficients.
(defun row-becomes-restricted (row)
  (do ((element (row-rnext row) (element-rnext element)))
      ((null element) t)
    (let ((coeff (element-coeff element))
	  (restriction (col-restriction (element-col element))))
      (when (or (rational-minusp coeff) (null restriction)) (return nil)))))

;;; A linear sum is restricted if its entry is restricted, dead, or
;;; is a row that becomes restricted.
(defun tableau-entry-is-restricted (e-node index)
  (let* ((header (aref (e-node-tableau-entry e-node) index))
	 (restriction (cond ((row-p header) (row-restriction header))
			    ((col-p header) (col-restriction header)))))
    (or (eq restriction 'restricted)
	(eq restriction 'dead)
	(and (row-p header) (row-becomes-restricted header)))))



;;; Restrict row to be non-negative.
(defun restrict-row (row-header justification)
  (let ((index (caar (row-owners row-header)))
        (e-node (cdar (row-owners row-header))))
    (push-undo (list #'undo-restrict (cons index e-node)))
    (setf (row-restriction row-header) 'restricted)
    (setf (row-reason-restricted row-header) justification)
    ;; Propagate restriction (including to egraph).
    (dolist (owner (row-owners row-header))
      (propagate-restriction (car owner) (cdr owner)))
    ;; Manifestly negative means the opposite can be restricted.
    (dolist (owner (list-of-embedded-owners-with-negative-values))
       (check-if-manifestly-negative owner))))

;;; List of owners with negative sample values.
(defun list-of-embedded-owners-with-negative-values ()
  (let ((result nil))
    (do ((el (col-cprev (aref *cols* 0)) (element-cprev el)))
        ((null el) t)
        (and (rational-minusp (element-coeff el))
             (let ((subresult nil))
               (dolist (owner (row-owners (element-row el)))
                 (when (and (eq (e-node-operation (cdr owner)) '>=)
                            (e-node-aux-pred (cdr owner)))
                   (push owner subresult)))
               (when subresult (push (car subresult) result)))))
    result))

;;; Check sum with negative sample value to see if it is
;;; manifestly negative. If so, its opposite can ba restricted.
(defun check-if-manifestly-negative (owner)
  (let ((header (aref (e-node-tableau-entry (cdr owner)) (car owner))))
    (and (row-p header)
         (row-is-negative header)
         (do ((pivot-element (find-pivot-to-raise header)
                             (find-pivot-to-raise header)))
             (nil)
             (cond
              (pivot-element            ; there is a pivot,
               (pivot pivot-element)
               (cond
                ;; not manifestly negative if row was pivoted.
                ((eq (element-row pivot-element) header)
                 (return t))
                ;; not manifestly negative if sample value not negative.
                ((not (row-is-negative header))
                 (return t))))
              ;; can't pivot, and sample value is -,
              ;; manifestly negative
              (t (push-fifo
                  (list 'restrict (cdr owner)
                        (opposite-index (cdr owner) (car owner))
                        (list 'opposite-manifestly-negative
                              (cons (opposite-index (cdr owner) (car owner))
                                    (cdr owner))
                              (collect-row-triples header)))
                  *tableau-list*)
                 (return t)))))))

;;; Restrict column to be non-negative.
(defun restrict-column (col-header justification)
  (let ((index (caar (col-owners col-header)))
        (e-node (cdar (col-owners col-header))))
    (push-undo (list #'undo-restrict (cons index e-node)))
    (setf (col-restriction col-header) 'restricted)
    (setf (col-reason-restricted col-header) justification)
    (dolist (owner (col-owners col-header))
            (propagate-restriction (car owner) (cdr owner)))
    (dolist (owner (list-of-embedded-owners-with-negative-values))
       (check-if-manifestly-negative owner))))

;;; Propagate restriction to egraph part.
(defun propagate-restriction (index e-node)
  (cond ((=-p (e-node-attribute e-node))
	 (if (<= index 1)
	     (if (eq (e-node-root e-node) (e-node-root *false-node*))
		 ;; = is false, >= or <=, therefore > or < is true.
		 (push-fifo (list 'restrict e-node (+ index 2)
                                  (list 'shift e-node index))
                            *tableau-list*)
		 (when (is-restricted e-node (- 1 index))
		   ;; >= and <=, therefore = is true.
		   (push-fifo (list 'merge e-node *true-node* 'anti-symmetric)
                              *merge-list*)))
           ;; > or <, therefore = is false.
           (push-fifo (list 'merge e-node *false-node* (list 'strict index))
                      *merge-list*)))
        ;; the inequality becomes either true or false,
        ;; depending on the value of index.
	((>=-p (e-node-attribute e-node))
         (push-fifo
          (list 'merge e-node (if (zerop index) *true-node* *false-node*)
                'restrict)
          *merge-list*))
	((zerop index) (propagate-non-negative e-node))
        ((= index 1) (propagate-negative-or-zero e-node))
        ((= index 2) (propagate-strictly-positive e-node))
        (t (propagate-strictly-negative e-node))))



;;; Minimize the tableau given that a row is manifestly maximized or
;;; minimized at 0.
(defun minimize-tableau (row-header)
  ;; Iterate over elements of the row.
  (do ((el (row-rnext row-header) (element-rnext el))
       (column-killed nil))
      ((null el) column-killed)
    (let ((col-header (element-col el)))
      ;; If element in non-dead column, kill the column and mark affected
      ;; rows. Note that the column must have been previously restricted.
      (unless (eq (col-restriction col-header) 'dead)
	(kill-column col-header (justify-minimized-col row-header col-header))
	(setq column-killed t)
	(do ((prev (col-cprev col-header) (element-cprev prev)))
	    ((null prev))
	  (setf (row-mark (element-row prev)) t))))))

;;; Propagate facts derived from equalities of rows with other rows
;;; and/or columns.
(defun propagate-row-equalities (column-killed)
  (when column-killed
    (multiple-value-bind (marked-rows unmarked-rows) (separate-marked-rows)
     (unless *inconsistent*
       (loop for mr in marked-rows
	     do
            ;; For each marked rows, see if it is equal to an unmarked row
	    ;; or checked marked row.
	    (let ((in-the-list nil))
	      (setq unmarked-rows
		    (mapcar
		     #'(lambda (ur)
			 (cond ((or in-the-list (not (equal (cdr ur) (cdr mr))))
				ur)
			       (t (setq in-the-list t)
				  (dolist (header (car ur))
				    (when (propagate-equality header (caar mr))
				      (return t)))
				  (cons (cons (caar mr) (car ur))
					(cdr ur)))))
		     unmarked-rows))
	      (unless in-the-list (push mr unmarked-rows))))))))




;;; Separate non-dead marked rows from unmarked rows, while representations
;;; of the rows are compactified (dead column entries are deleted).
;;; Dead rows are ignored, and if any of the following conditions are true,
;;; a marked row is not put in the marked row list:
;;;    - the row does not have any non-zero entry.
;;;    - the row is restricted and is manifestly maximized at zero.
;;;    - the row's only non-zero entry is in the constant column.
;;;    - the row is detected to be equal to a column, and invoking
;;;      propagate-equality is successful.
;;; Afterwards, all rows are unmarked (including dead rows).
(defun separate-marked-rows ()
  ;; Repeat if there is a column killed.
  (do ((marked-rows nil) (unmarked-rows nil) (column-killed t))
      ((not column-killed) (values marked-rows unmarked-rows))
    (setq column-killed nil)
    ;; Go through all rows.
    ;; For each row, nz-list will be list of non-zero columns with coefficients.
    (dotimes (i (1- (fill-pointer *rows*)))
      (let* ((nz-list nil)
	     (row-header (aref *rows* i))
             (restriction (row-restriction row-header)))
	(unless (or (eq restriction 'dead) *inconsistent*)
	  ;; Go through all columns of the row.
	  (loop for next = (row-rnext row-header) then (element-rnext next)
		until (null next)
		;; If column not dead, add (column . coefficient) to nz-list.
		unless (eq (col-restriction (element-col next)) 'dead)
		do (push (cons (element-col next) (element-coeff next)) nz-list)
		finally
		;; Now, if row is marked, check the non-zero entries.
		(cond
		 ((row-mark row-header)
		  (let ((col-1 (caar nz-list))
			(coeff-1 (cdar nz-list))
			(rest-of-list (cdr nz-list)))
		    (cond ((null nz-list)
			   ;;(null col-1)
			   ;; No non-zero entries, kill the row.
			   (kill-row row-header (justify-constant row-header)))
			  ((and (eq restriction 'restricted)
				(manifestly-maximized-at-zero nz-list))
			   ;; Sum of non-zero-entries manifestly maximized
			   ;; at 0. Kill the row.
			   (kill-row row-header
				     (list 'anti-symmetric
					   (row-reason-restricted row-header)
					   (justify-maximized row-header)))
			   (dolist (m marked-rows)
			     (setf (row-mark (car (car m))) t))
			   ;; Since all columns in nz-list must have
			   ;; been restricted, we can kill them.
			   (dolist (e nz-list)
			     (kill-column
			      (car e)
			      (justify-minimized-col row-header (car e)))
			     ;; Mark all rows that has killed column.
			     (do ((prev (col-cprev (car e))
					(element-cprev prev)))
				 ((null prev))
				 (setf (row-mark (element-row prev)) t)))
			   (setq column-killed t)
			   (setq marked-rows (setq unmarked-rows nil)))
			  ((and (null rest-of-list) (zerop (col-index col-1)))
			   (propagate-equal-constant row-header coeff-1))
			  ((and (null rest-of-list)
				(plusp (col-index col-1))
				(rational-= coeff-1 1))
			   (or (propagate-equality row-header col-1)
			       (push (cons (list row-header) nz-list)
				     marked-rows)))
			  (t (push (cons (list row-header) nz-list)
				   marked-rows)))))
		 (t
		  (push (cons (list row-header) nz-list) unmarked-rows)))))
	;; Unmark the row.
	(setf (row-mark row-header) nil)
	(when column-killed (return t))))))



;;; Check to see if a row is manifestly maximized at zero by checking
;;; the compactified row. All entries must have negative coefficients
;;; and belong to restricted columns.
(defun manifestly-maximized-at-zero (nz-list)
  (not (dolist (e nz-list)
	 (when (or (rational-plusp (cdr e))
                   (neq (col-restriction (car e)) 'restricted))
	   (return t)))))

;;; Propagate the fact that the sum represented by header is
;;; equal to a constant value (note that the value is non-zero).
(defun propagate-equal-constant (header value)
  (dolist (owner (row-owners header))
    (propagate-constant (car owner) (cdr owner) value)))

(defun propagate-constant (index e-node value)
  (let* ((header (aref (e-node-tableau-entry e-node) index))
         (justification (cond ((col-p header)
                               ;; must be the constant column (thus value
                               ;; must be 1)
                               'sum-is-one)
                              (t (justify-constant header)))))
    (cond ((=-p (e-node-attribute e-node))
           (when (<= index 1)
             (push-fifo (list 'merge e-node *false-node*
                              (list '=-constant index justification))
                        *merge-list*)))
          ((>=-p (e-node-attribute e-node))
           (when (rational-plusp value)
             (push-fifo (list 'merge e-node
                              (if (zerop index) *true-node* *false-node*)
                              (list '>=-constant index justification))
                        *merge-list*)))
          ((integerp value)
           (when (zerop index)
             (push-fifo (list 'create-integer-and-merge value e-node
                              (list 'integer justification))
                        *merge-list*)))
          ;; an integer can not be a fraction.
          (t (set-inconsistent
              (list 'non-integer e-node index value justification))))))



;;; Propagate the fact that a (compactified) row is equal to some other
;;; (compactified) row or column.
(defun propagate-equality (header-1 header-2)
  (let ((owners-1 (row-owners header-1))
	(owners-2 (if (row-p header-2)
                      (row-owners header-2)
                    (col-owners header-2)))
	(restriction-1 (row-restriction header-1))
	(restriction-2 (if (row-p header-2) (row-restriction header-2)
			   (col-restriction header-2)))
	(justification (justify-equal header-1 header-2)))
    (cond ((and (null restriction-1) (eq restriction-2 'restricted))
	   (push-fifo (list 'restrict (cdar owners-1) (caar owners-1)
                            (list 'equal-restrict (car owners-1) (car owners-2)
                                  justification))
                      *tableau-list*))
	  ((and (null restriction-2) (eq restriction-1 'restricted))
	   (push-fifo (list 'restrict (cdar owners-2) (caar owners-2)
                            (list 'equal-restrict (car owners-2) (car owners-1)
                                  justification))
                      *tableau-list*)))
    ;; propagate a "useful" equality if any.
    (dolist (owner-1 owners-1)
      (when (and (not (node-is-relation-p (cdr owner-1)))
		 (zerop (car owner-1)))
	(when (dolist (owner-2 owners-2)
		(when (and (not (node-is-relation-p (cdr owner-2)))
			   (zerop (car owner-2)))
		  (push-fifo
                   (list 'merge (cdr owner-1) (cdr owner-2)
                         (list '=-sums (cdr owner-1) justification))
                   *merge-list*)
		  (return t)))
	      (return t))))))

;;; Equate a linear sum to zero.
(defun kill (e-node justification)
  (let ((header (aref (e-node-tableau-entry e-node) 0)))
    (cond
     ;; the linear sum is represented by a column.
     ((col-p header)
      (cond ((zerop (col-index header))
	     (set-inconsistent (list 'kill-one justification)))
	    ((or (eq (col-restriction header) 'restricted)
		 (null (col-restriction header)))
	     ;; Column not already dead. Kill the column.
	     (kill-column header justification)
	     ;; Propagate facts.
	     (do ((el (col-cprev header) (element-cprev el)))
		 ((null el) (propagate-row-equalities t))
		 (let ((row-header (element-row el)))
		   (or (eq (row-restriction row-header) 'dead)
		       (and (row-not-dead row-header)
			    (setf (row-mark row-header) t))
		       (kill-row row-header
				 (justify-constant row-header))))))))
     ((row-p header)
      (unless (eq (row-restriction header) 'dead)
        ;; Row not already dead.
        (and
         ;; Try to raise the sample value to strictly positive.
         (raise-to-kill header justification)
         ;; If sample value can be strictly positive, try to lower
         ;; the sample value and kill the row.
         (lower-to-kill header justification)))))))



;;; Try to raise the sample value of the specified row to be strictly
;;; positive. If row is already strictly positive return non-nil.
;;; Otherwise there are 4 scenarios:
;;; - Row is manifestly maximized at a negative value.
;;;   Inconsistent state. Return nil.
;;; - Row is manifestly maximized at 0. Equality discovered. Return nil.
;;; - Can pivot the row. Pivot and kill the resulting column. Return nil.
;;; - Can raise the sample value to strictly positive, return t.
(defun raise-to-kill (header justification)
  (or
   ;; Don't kill if the sample value is strictly positive.
   (row-is-positive header)
   ;; Try to pivot.
   (do () (nil)
       (let ((pivot-element (find-pivot-to-raise header)))
         (cond
	  ((null pivot-element)
	   (cond
            ;; Can't pivot and sample value is negative, an inconsistent state.
            ((row-is-negative header)
             (set-inconsistent
              (list 'inconsistent-restrictions 'kill
                    (car (row-owners header))
                    justification
                    (justify-maximized header)))
             (return nil))
            ;; Can't pivot and sample value is 0, tableau is non-minimal.
            (t (kill-row header justification)
               (propagate-row-equalities (minimize-tableau header))
               (return nil))))
          ;; Can pivot the row, pivot and kill.
	  ((eq (element-row pivot-element) header)
	   (pivot-and-kill pivot-element justification)
	   (return nil))
          ;; Pivot some other row.
	  (t (pivot pivot-element)
	     (when (row-is-positive header) (return t))))))))



;;; Knowing the sample value can be strictly positive, try to
;;; lower the sample value of a row to a negative value.
(defun lower-to-kill (header justification)
  (do ()  (nil)
    ;; Try to pivot.
    (let ((pivot-element (find-pivot-to-lower header)))
      (cond
	((null pivot-element)
	 (cond
          ;; Can't pivot and sample value is strictly positive,
          ;; an inconsistent state.
          ((row-is-positive header)
           (return (set-inconsistent
                    (list 'inconsistent-restrictions 'kill
                          (car (row-owners header))
                          justification
                          (justify-minimized header)))))
          ;; Can't pivot and sample value is 0, tableau is non-minimal.
          (t (kill-row header justification)
             (return (propagate-row-equalities (minimize-tableau header))))))
        ;; Can pivot row, pivot and kill.
	((eq (element-row pivot-element) header)
         (return (pivot-and-kill pivot-element justification)))
        ;; Pivot some other row.
	(t (pivot pivot-element)
	   (when (row-is-negative header)
             ;; If sample value becomes negative, pivot and kill.
	     (return (pivot-and-kill (find-pivot-given-row header)
                                     justification))))))))



;;; Kill a row given the row header.
(defun kill-row (header justification)
  ;; nothing to do if row already dead.
  (unless (eq (row-restriction header) 'dead)
    (push-undo (list #'undo-kill (cons header (row-restriction header))))
    (setf (row-restriction header) 'dead)
    (setf (row-reason-killed header) justification)
    (dolist (owner (row-owners header))
      (propagate-zero (car owner) (cdr owner)))))

;;; Kill a column given the column header.
(defun kill-column (header justification)
  (cond ((zerop (col-index header))
         (set-inconsistent (list 'kill-one justification)))
        (t
         ;; nothing to do if column already dead.
         (unless (eq (col-restriction header) 'dead)
           (push-undo (list #'undo-kill
                            (cons header (col-restriction header))))
           (setf (col-restriction header) 'dead)
           (setf (col-reason-killed header) justification)
           (dolist (owner (col-owners header))
                   (propagate-zero (car owner) (cdr owner)))))))

;;; Propagate the fact that a tableau entry is zero to the e-graph part.
(defun propagate-zero (index node)
  (cond ((=-p (e-node-attribute node))
         (push-fifo
          (list 'merge node (if (<= index 1) *true-node* *false-node*)
                (list 'zero index))
          *merge-list*))
        ;; must also propagate equalities
	((>=-p (e-node-attribute node))
         ;; inequality was not shifted
	 (when (and (e-node-not-shifted node)
		    (zerop index))
	   (push-fifo (list 'merge (arg-1-node node) (arg-2-node node)
                            (list 'zero-sum node))
                      *merge-list*))
         (push-fifo
          (list 'merge node (if (zerop index) *true-node* *false-node*)
                (list 'zero index))
          *merge-list*))
        ((<= index 1)
         (push-fifo (list 'merge node *zero-node* (list 'zero index))
                    *merge-list*))
        ((= index 2) (propagate-strictly-positive node))
        (t (propagate-strictly-negative node))))

;;; Pivot a row into a column and kill the column, given that the row can be
;;; pivoted into the column.
(defun pivot-and-kill (pivot-element justification)
  (pivot pivot-element)				; pivot,
  (kill-column (element-col pivot-element) justification) ; kill,
						; and propagate facts.
  (do ((el (col-cprev (element-col pivot-element)) (element-cprev el)))
      ((null el) (propagate-row-equalities t))
    (let ((row-header (element-row el)))
      (or (eq (row-restriction row-header) 'dead)
	  (if (row-not-dead row-header)
	      (setf (row-mark row-header) t)
            (kill-row row-header (justify-constant row-header)))))))



;;; Propagate the fact that a node is non-negative.
(defun propagate-non-negative (e-node)
  (let ((root (e-node-root e-node))
	(*-node (e-node-e-pred (intern-symbol '*))))
    (and *-node
	 (loop-over-nodes (next *-node e-node-samecar)
	   (cond
            ((eq (e-node-root (arg-1-node next)) root)
             (propagate-non-negative-left e-node next))
            ((eq (e-node-root (arg-2-node next)) root)
             (propagate-non-negative-right e-node next))
            ((eq (e-node-root next) root)
             (propagate-non-negative-product e-node next)))))))

;;; Propagate the fact that the left argument of a product is non-negative
;;; upwards.
(defun propagate-non-negative-left (left product)
  (let ((right (arg-2-node product))
        node)
    (cond ((setq node (node-is-non-negative-p right))
           ;; (implies (and (>= x 0) (>= y 0)) (>= (* x y) 0))
           (push-fifo (list 'restrict product 0
                            (list '*-up 0 0 product left node))
                      *tableau-list*))
          ((setq node (node-is-strictly-positive-p right))
           ;; (implies (and (>= x 0) (> y 0)) (>= (* x y) 0))
           (push-fifo (list 'restrict product 0
                            (list '*-up 0 2 product left node))
                      *tableau-list*)))
    (cond ((setq node (node-is-negative-or-zero-p right))
           ;; (implies (and (>= x 0) (>= 0 y)) (>= 0 (* x y)))
           (push-fifo (list 'restrict product 1
                            (list '*-up 0 1 product left node))
                      *tableau-list*))
          ((setq node (node-is-strictly-negative-p right))
           ;; (implies (and (>= x 0) (> 0 y)) (>= 0 (* x y)))
           (push-fifo (list 'restrict product 1
                            (list '*-up 0 3 product left node))
                      *tableau-list*)))))



;;; Propagate the fact that the right argument of a product is non-negative
;;; upwards.
(defun propagate-non-negative-right (right product)
  (let ((left (arg-1-node product))
        node)
    (cond ((setq node (node-is-non-negative-p left))
           ;; (implies (and (>= x 0) (>= y 0)) (>= (* x y) 0))
           (push-fifo (list 'restrict product 0
                            (list '*-up 0 0 product node right))
                      *tableau-list*))
          ((setq node (node-is-strictly-positive-p left))
           ;; (implies (and (> x 0) (>= y 0)) (>= (* x y) 0))
           (push-fifo (list 'restrict product 0
                            (list '*-up 2 0 product node right))
                      *tableau-list*)))
    (cond ((setq node (node-is-negative-or-zero-p left))
           ;; (implies (and (>= 0 x ) (>= y 0)) (>= 0 (* x y)))
           (push-fifo (list 'restrict product 1
                            (list '*-up 1 0 product node right))
                      *tableau-list*))
          ((setq node (node-is-strictly-negative-p left))
           ;; (implies (and (> 0 x ) (>= y 0)) (>= 0 (* x y)))
           (push-fifo (list 'restrict product 1
                            (list '*-up 3 0 product node right))
                      *tableau-list*)))))

;;; Propagate the fact that a product is non-negative downwards.
;;; Note that the conclusion can only be a non-strict inequality.
(defun propagate-non-negative-product (ref product)
  (let ((left (arg-1-node product))
        (right (arg-2-node product))
        node)
    (cond ((setq node (node-is-strictly-positive-p left))
           ;; (implies (and (>= (* x y) 0) (> x 0)) (>= y 0))
           (loop-over-nodes (r right e-node-eqclass)
             (when (aref (e-node-tableau-entry r) 0)
               (return
                (push-fifo (list 'restrict r 0
                                 (list '*-r 0 2 ref product node r))
                           *tableau-list*)))))
          ((setq node (node-is-strictly-positive-p right))
           ;; (implies (and (>= (* x y) 0) (> y 0)) (>= x 0))
           (loop-over-nodes (l left e-node-eqclass)
             (when (aref (e-node-tableau-entry l) 0)
               (return
                (push-fifo (list 'restrict l 0
                                 (list '*-l 0 2 ref product l node))
                           *tableau-list*)))))
          ((setq node (node-is-strictly-negative-p left))
           ;; (implies (and (>= (* x y) 0) (> 0 x)) (>= 0 y))
           (loop-over-nodes (r right e-node-eqclass)
             (when (aref (e-node-tableau-entry r) 1)
               (return
                (push-fifo (list 'restrict r 1
                                 (list '*-r 0 3 ref product node r))
                           *tableau-list*)))))
          ((setq node (node-is-strictly-negative-p right))
           ;; (implies (and (>= (* x y) 0) (> 0 y)) (>= 0 x))
           (loop-over-nodes (l left e-node-eqclass)
             (when (aref (e-node-tableau-entry l) 1)
               (return
                (push-fifo (list 'restrict l 1
                                 (list '*-l 0 3 ref product l node))
                           *tableau-list*))))))))
    


;;; Propagate the fact that a node is negative.
(defun propagate-negative-or-zero (e-node)
  (let ((root (e-node-root e-node))
	(*-node (e-node-e-pred (intern-symbol '*))))
    (and *-node
	 (loop-over-nodes (next *-node e-node-samecar)
	   (cond
            ((eq (e-node-root (arg-1-node next)) root)
             (propagate-negative-or-zero-left e-node next))
            ((eq (e-node-root (arg-2-node next)) root)
             (propagate-negative-or-zero-right e-node next))
            ((eq (e-node-root next) root)
             (propagate-negative-or-zero-product e-node next)))))))

;;; Propagate the fact that the left argument of a product is negative
;;; or zero upwards.
(defun propagate-negative-or-zero-left (left product)
  (let ((right (arg-2-node product))
        node)
    (cond ((setq node (node-is-non-negative-p right))
           ;; (implies (and (>= 0 x) (>= y 0)) (>= 0 (* x y)))
           (push-fifo (list 'restrict product 1
                            (list '*-up 1 0 product left node))
                      *tableau-list*))
          ((setq node (node-is-strictly-positive-p right))
           ;; (implies (and (>= 0 x) (> y 0)) (>= 0 (* x y)))
           (push-fifo (list 'restrict product 1
                            (list '*-up 1 2 product left node))
                      *tableau-list*)))
    (cond ((setq node (node-is-negative-or-zero-p right))
           ;; (implies (and (>= 0 x) (>= 0 y)) (>= (* x y) 0))
           (push-fifo (list 'restrict product 0
                            (list '*-up 1 1 product left node))
                      *tableau-list*))
          ((setq node (node-is-strictly-negative-p right))
           ;; (implies (and (>= 0 x) (> 0 y)) (>= (* x y) 0))
           (push-fifo (list 'restrict product 0
                            (list '*-up 1 3 product left node))
                      *tableau-list*)))))



;;; Propagate the fact that the right argument of a product is negative
;;; or zero upwards.
(defun propagate-negative-or-zero-right (right product)
  (let ((left (arg-1-node product))
        node)
    (cond ((setq node (node-is-non-negative-p left))
           ;; (implies (and (>= x 0) (>= 0 y)) (>= 0 (* x y)))
           (push-fifo (list 'restrict product 1
                            (list '*-up 0 1 product node right))
                      *tableau-list*))
          ((setq node (node-is-strictly-positive-p left))
           ;; (implies (and (> x 0) (>= 0 y)) (>= 0 (* x y)))
           (push-fifo (list 'restrict product 1
                            (list '*-up 2 1 product node right))
                      *tableau-list*)))
    (cond ((setq node (node-is-negative-or-zero-p left))
           ;; (implies (and (>= 0 x) (>= 0 y)) (>= (* x y) 0))
           (push-fifo (list 'restrict product 0
                            (list '*-up 1 1 product node right))
                      *tableau-list*))
          ((setq node (node-is-strictly-negative-p left))
           ;; (implies (and (> 0 x) (>= 0 y)) (>= (* x y) 0))
           (push-fifo (list 'restrict product 0
                            (list '*-up 3 1 product node right))
                      *tableau-list*)))))

;;; Propagate the fact that a product is negative or zero downwards.
;;; Note that the conclusion can only be a non-strict inequality.
(defun propagate-negative-or-zero-product (ref product)
  (let ((left (arg-1-node product))
        (right (arg-2-node product))
        node)
    (cond ((setq node (node-is-strictly-positive-p left))
           ;; (implies (and (>= 0 (* x y)) (> x 0)) (>= 0 y))
           (loop-over-nodes (r right e-node-eqclass)
             (when (aref (e-node-tableau-entry r) 1)
               (return
                (push-fifo (list 'restrict r 1
                                 (list '*-r 1 2 ref product node r))
                           *tableau-list*)))))
          ((setq node (node-is-strictly-positive-p right))
           ;; (implies (and (>= 0 (* x y)) (> y 0)) (>= 0 x))
           (loop-over-nodes (l left e-node-eqclass)
             (when (aref (e-node-tableau-entry l) 1)
               (return
                (push-fifo (list 'restrict l 1
                                 (list '*-l 1 2 ref product l node))
                           *tableau-list*)))))
          ((setq node (node-is-strictly-negative-p left))
           ;; (implies (and (>= 0 (* x y)) (> 0 x)) (>= y 0))
           (loop-over-nodes (r right e-node-eqclass)
             (when (aref (e-node-tableau-entry r) 0)
               (return
                (push-fifo (list 'restrict r 0
                                 (list '*-r 1 3 ref product node r))
                           *tableau-list*)))))
          ((setq node (node-is-strictly-negative-p right))
           ;; (implies (and (>= 0 (* x y)) (> 0 y)) (>= x 0))
           (loop-over-nodes (l left e-node-eqclass)
             (when (aref (e-node-tableau-entry l) 0)
               (return
                (push-fifo (list 'restrict l 0
                                 (list '*-l 1 3 ref product l node))
                           *tableau-list*))))))))



;;; Propagate the fact that a node is strictly positive.
(defun propagate-strictly-positive (e-node)
  (push-fifo (list 'forbid e-node *zero-node* `(positive ,e-node))
             *merge-list*)
  (let ((root (e-node-root e-node))
	(*-node (e-node-e-pred (intern-symbol '*))))
    (and *-node
	 (loop-over-nodes (next *-node e-node-samecar)
	   (cond ((eq (e-node-root (arg-1-node next)) root)
                  (propagate-positive-left e-node next))
		 ((eq (e-node-root (arg-2-node next)) root)
                  (propagate-positive-right e-node next))
		 ((eq (e-node-root next) root)
                  (propagate-positive-product e-node next)))))))

;;; Propagate the fact that the left argument of a product is positive
;;; upwards.
(defun propagate-positive-left (left product)
  (let ((right (arg-2-node product))
        node)
    (cond ((setq node (node-is-strictly-positive-p right))
           ;; (implies (and (> x 0) (> y 0)) (> (* x y) 0))
           (push-fifo (list 'restrict product 2
                            (list '*-up 2 2 product left node))
                      *tableau-list*))
          ((setq node (node-is-non-negative-p right))
           ;; (implies (and (> x 0) (>= y 0)) (>= (* x y) 0))
           (push-fifo (list 'restrict product 0
                            (list '*-up 2 0 product left node))
                      *tableau-list*)))
    (cond ((setq node (node-is-strictly-negative-p right))
           ;; (implies (and (> x 0) (> 0 y)) (> 0 (* x y)))
           (push-fifo (list 'restrict product 3
                            (list '*-up 2 3 product left node))
                      *tableau-list*))
          ((setq node (node-is-negative-or-zero-p right))
           ;; (implies (and (> x 0) (> 0 y)) (>= 0 (* x y)))
           (push-fifo (list 'restrict product 1
                            (list '*-up 2 1 product left node))
                      *tableau-list*)))
    (cond ((setq node (node-is-strictly-positive-p product))
           ;; (implies (and (> x 0) (> (* x y) 0)) (> y 0))
           (loop-over-nodes (r right e-node-eqclass)
             (when (aref (e-node-tableau-entry r) 2)
               (return
                (push-fifo (list 'restrict r 2
                                 (list '*-r 2 2 node product left r))
                           *tableau-list*)))))
          ((setq node (node-is-non-negative-p product))
           ;; (implies (and (> x 0) (>= (* x y) 0)) (>= y 0))
           (loop-over-nodes (r right e-node-eqclass)
             (when (aref (e-node-tableau-entry r) 0)
               (return
                (push-fifo (list 'restrict r 0
                                 (list '*-r 0 2 node product left r))
                           *tableau-list*))))))
    (cond ((setq node (node-is-strictly-negative-p product))
           ;; (implies (and (> x 0) (> 0 (* x y))) (> 0 y))
           (loop-over-nodes (r right e-node-eqclass)
             (when (aref (e-node-tableau-entry r) 3)
               (return
                (push-fifo (list 'restrict r 3
                                 (list '*-r 3 2 node product left r))
                           *tableau-list*)))))
          ((setq node (node-is-negative-or-zero-p product))
           ;; (implies (and (> x 0) (>= 0 (* x y))) (>= 0 y))
           (loop-over-nodes (r right e-node-eqclass)
             (when (aref (e-node-tableau-entry r) 1)
               (return
                (push-fifo (list 'restrict r 1
                                 (list '*-r 1 2 node product left r))
                           *tableau-list*))))))))



;;; Propagate the fact that the right argument of a product is positive
;;; upwards.
(defun propagate-positive-right (right product)
  (let ((left (arg-1-node product))
        node)
    (cond ((setq node (node-is-strictly-positive-p left))
           ;; (implies (and (> x 0) (> y 0)) (> (* x y) 0))
           (push-fifo (list 'restrict product 2
                            (list '*-up 2 2 product node right))
                      *tableau-list*))
          ((setq node (node-is-non-negative-p left))
           ;; (implies (and (>= x 0) (> y 0)) (>= (* x y) 0))
           (push-fifo (list 'restrict product 0
                            (list '*-up 0 2 product node right))
                      *tableau-list*)))
    (cond ((setq node (node-is-strictly-negative-p left))
           ;; (implies (and (> 0 x) (> y 0)) (> 0 (* x y)))
           (push-fifo (list 'restrict product 3
                            (list '*-up 3 2 product node right))
                      *tableau-list*))
          ((setq node (node-is-negative-or-zero-p left))
           ;; (implies (and (>= 0 x) (> y 0)) (>= 0 (* x y)))
           (push-fifo (list 'restrict product 1
                            (list '*-up 1 2 product node right))
                      *tableau-list*)))
    (cond ((setq node (node-is-strictly-positive-p product))
           ;; (implies (and (> y 0) (> (* x y) 0)) (> x 0))
           (loop-over-nodes (l left e-node-eqclass)
             (when (aref (e-node-tableau-entry l) 2)
               (return
                (push-fifo (list 'restrict l 2
                                 (list '*-l 2 2 node product l right))
                           *tableau-list*)))))
          ((setq node (node-is-non-negative-p product))
           ;; (implies (and (> y 0) (>= (* x y) 0)) (>= x 0))
           (loop-over-nodes (l left e-node-eqclass)
             (when (aref (e-node-tableau-entry l) 0)
               (return
                (push-fifo (list 'restrict l 0
                                 (list '*-l 0 2 node product l right))
                           *tableau-list*))))))
    (cond ((setq node (node-is-strictly-negative-p product))
           ;; (implies (and (> y 0) (> 0 (* x y))) (> 0 x))
           (loop-over-nodes (l left e-node-eqclass)
             (when (aref (e-node-tableau-entry l) 3)
               (return
                (push-fifo (list 'restrict l 3
                                 (list '*-l 3 2 node product l right))
                           *tableau-list*)))))
          ((setq node (node-is-negative-or-zero-p product))
           ;; (implies (and (> y 0) (>= 0 (* x y))) (>= 0 x))
           (loop-over-nodes (l left e-node-eqclass)
             (when (aref (e-node-tableau-entry l) 1)
               (return
                (push-fifo (list 'restrict l 1
                                 (list '*-l 1 2 node product l right))
                           *tableau-list*))))))))



;;; Propagate the fact that a product is positive downwards.
(defun propagate-positive-product (ref product)
  (let ((left (arg-1-node product))
        (right (arg-2-node product))
        node)
    (cond ((setq node (node-is-strictly-positive-p left))
           ;; (implies (and (> (* x y) 0) (> x 0)) (> y 0))
           (loop-over-nodes (r right e-node-eqclass)
             (when (aref (e-node-tableau-entry r) 2)
               (return
                (push-fifo (list 'restrict r 2
                                 (list '*-r 2 2 ref product node r))
                           *tableau-list*)))))
          ((setq node (node-is-non-negative-p left))
           ;; (implies (and (> (* x y) 0) (>= x 0)) (> x 0))
           (push-fifo (list 'restrict node 2
                            (list '*-ll 2 0 ref product node))
                      *tableau-list*)
           ;; (implies (and (> (* x y) 0) (>= x 0)) (> y 0))
           (loop-over-nodes (r right e-node-eqclass)
             (when (aref (e-node-tableau-entry r) 2)
               (return
                (push-fifo (list 'restrict r 2
                                 (list '*-r 2 0 ref product node r))
                           *tableau-list*))))))
    (cond ((setq node (node-is-strictly-positive-p right))
           ;; (implies (and (> (* x y) 0) (> y 0)) (> x 0))
           (loop-over-nodes (l left e-node-eqclass)
             (when (aref (e-node-tableau-entry l) 2)
               (return
                (push-fifo (list 'restrict l 2
                                 (list '*-l 2 2 ref product l node))
                           *tableau-list*)))))
          ((setq node (node-is-non-negative-p right))
           ;; (implies (and (> (* x y) 0) (>= y 0)) (> y 0))
           (push-fifo (list 'restrict node 2 (list '*-rr 2 0 ref product node))
                      *tableau-list*)
           ;; (implies (and (> (* x y) 0) (>= y 0)) (> x 0))
           (loop-over-nodes (l left e-node-eqclass)
             (when (aref (e-node-tableau-entry l) 2)
               (return
                (push-fifo (list 'restrict l 2
                                 (list '*-l 2 0 ref product l node))
                           *tableau-list*))))))
    (cond ((setq node (node-is-strictly-negative-p left))
           ;; (implies (and (> (* x y) 0) (> 0 x)) (> 0 y))
           (loop-over-nodes (r right e-node-eqclass)
             (when (aref (e-node-tableau-entry r) 3)
               (return
                (push-fifo (list 'restrict r 3
                                 (list '*-r 2 3 ref product node r))
                           *tableau-list*)))))
          ((setq node (node-is-negative-or-zero-p left))
           ;; (implies (and (> (* x y) 0) (>= 0 x)) (> 0 x))
           (push-fifo (list 'restrict node 3 (list '*-ll 2 1 ref product node))
                      *tableau-list*)
           ;; (implies (and (> (* x y) 0) (>= 0 x)) (> 0 y))
           (loop-over-nodes (r right e-node-eqclass)
             (when (aref (e-node-tableau-entry r) 3)
               (return
                (push-fifo (list 'restrict r 3
                                 (list '*-r 2 1 ref product node r))
                           *tableau-list*))))))
    (cond ((setq node (node-is-strictly-negative-p right))
           ;; (implies (and (> (* x y) 0) (> 0 y)) (> 0 x))
           (loop-over-nodes (l left e-node-eqclass)
             (when (aref (e-node-tableau-entry l) 3)
               (return
                (push-fifo (list 'restrict l 3
                                 (list '*-l 2 3 ref product l node))
                           *tableau-list*)))))
          ((setq node (node-is-negative-or-zero-p right))
           ;; (implies (and (> (* x y) 0) (>= 0 y)) (> 0 y))
           (push-fifo (list 'restrict node 3 (list '*-rr 2 1 ref product node))
                      *tableau-list*)
           ;; (implies (and (> (* x y) 0) (>= 0 y)) (> 0 x))
           (loop-over-nodes (l left e-node-eqclass)
             (when (aref (e-node-tableau-entry l) 3)
               (return
                (push-fifo (list 'restrict l 3
                                 (list '*-l 2 1 ref product l node))
                           *tableau-list*))))))))



;;; Propagate the fact that a node is strictly negative.
(defun propagate-strictly-negative (e-node)
  (push-fifo (list 'forbid e-node *zero-node* `(negative ,e-node))
             *merge-list*)
  (let ((root (e-node-root e-node))
	(*-node (e-node-e-pred (intern-symbol '*))))
    (and *-node
	 (loop-over-nodes (next *-node e-node-samecar)
	   (cond ((eq (e-node-root (arg-1-node next)) root)
                  (propagate-negative-left e-node next))
                 ((eq (e-node-root (arg-2-node next)) root)
                  (propagate-negative-right e-node next))
		 ((eq (e-node-root next) root)
                  (propagate-negative-product e-node next)))))))

;;; Propagate the fact that the left argument of a product is negative
;;; upwards.
(defun propagate-negative-left (left product)
  (let ((right (arg-2-node product))
        node)
    (cond ((setq node (node-is-strictly-positive-p right))
           ;; (implies (and (> 0 x) (> y 0)) (> 0 (* x y)))
           (push-fifo (list 'restrict product 3
                            (list '*-up 3 2 product left node))
                      *tableau-list*))
          ((setq node (node-is-non-negative-p right))
           ;; (implies (and (> 0 x) (>= y 0)) (>= 0 (* x y)))
           (push-fifo (list 'restrict product 1
                            (list '*-up 3 0 product left node))
                      *tableau-list*)))
    (cond ((setq node (node-is-strictly-negative-p right))
           ;; (implies (and (> 0 x) (> 0 y)) (> (* x y) 0))
           (push-fifo (list 'restrict product 2
                            (list '*-up 3 3 product left node))
                      *tableau-list*))
          ((setq node (node-is-negative-or-zero-p right))
           ;; (implies (and (> 0 x) (>= 0 y)) (>= (* x y) 0))
           (push-fifo (list 'restrict product 0
                            (list '*-up 3 1 product left node))
                      *tableau-list*)))
    (cond ((setq node (node-is-strictly-positive-p product))
           ;; (implies (and (> 0 x) (> (* x y) 0)) (> 0 y))
           (loop-over-nodes (r right e-node-eqclass)
             (when (aref (e-node-tableau-entry r) 3)
               (return
                (push-fifo (list 'restrict r 3
                                 (list '*-r 2 3 node product left r))
                           *tableau-list*)))))
          ((setq node (node-is-non-negative-p product))
           ;; (implies (and (> 0 x) (>= (* x y) 0)) (>= 0 y))
           (loop-over-nodes (r right e-node-eqclass)
             (when (aref (e-node-tableau-entry r) 1)
               (return
                (push-fifo (list 'restrict r 1
                                 (list '*-r 0 3 node product left r))
                           *tableau-list*))))))
    (cond ((setq node (node-is-strictly-negative-p product))
           ;; (implies (and (> 0 x) (> 0 (* x y))) (> y 0))
           (loop-over-nodes (r right e-node-eqclass)
             (when (aref (e-node-tableau-entry r) 2)
               (return
                (push-fifo (list 'restrict r 2
                                 (list '*-r 3 3 node product left r))
                           *tableau-list*)))))
          ((setq node (node-is-negative-or-zero-p product))
           ;; (implies (and (> 0 x) (>= 0 (* x y))) (>= y 0))
           (loop-over-nodes (r right e-node-eqclass)
             (when (aref (e-node-tableau-entry r) 0)
               (return
                (push-fifo (list 'restrict r 0
                                 (list '*-r 1 3 node product left r))
                           *tableau-list*))))))))



;;; Propagate the fact that the right argument of a product is negative
;;; upwards.
(defun propagate-negative-right (right product)
  (let ((left (arg-1-node product))
        node)
    (cond ((setq node (node-is-strictly-positive-p left))
           ;; (implies (and (> x 0) (> 0 y)) (> 0 (* x y)))
           (push-fifo (list 'restrict product 3
                            (list '*-up 2 3 product node right))
                      *tableau-list*))
          ((setq node (node-is-non-negative-p left))
           ;; (implies (and (>= x 0) (> 0 y)) (>= 0 (* x y)))
           (push-fifo (list 'restrict product 1
                            (list '*-up 0 3 product node right))
                      *tableau-list*)))
    (cond ((setq node (node-is-strictly-negative-p left))
           ;; (implies (and (> 0 x) (> 0 y)) (> (* x y) 0))
           (push-fifo (list 'restrict product 2
                            (list '*-up 3 3 product node right))
                      *tableau-list*))
          ((setq node (node-is-negative-or-zero-p left))
           ;; (implies (and (>= 0 x) (> 0 y)) (>= (* x y) 0))
           (push-fifo (list 'restrict product 0
                            (list '*-up 1 3 product node right))
                      *tableau-list*)))
    (cond ((setq node (node-is-strictly-positive-p product))
           ;; (implies (and (> 0 y) (> (* x y) 0)) (> 0 x))
           (loop-over-nodes (l left e-node-eqclass)
             (when (aref (e-node-tableau-entry l) 3)
               (return
                (push-fifo (list 'restrict l 3
                                 (list '*-l 2 3 node product l right))
                           *tableau-list*)))))
          ((setq node (node-is-non-negative-p product))
           ;; (implies (and (> 0 y) (>= (* x y) 0)) (>= 0 x))
           (loop-over-nodes (l left e-node-eqclass)
             (when (aref (e-node-tableau-entry l) 1)
               (return
                (push-fifo (list 'restrict l 1
                                 (list '*-l 0 3 node product l right))
                           *tableau-list*))))))
    (cond ((setq node (node-is-strictly-negative-p product))
           ;; (implies (and (> 0 y) (> 0 (* x y))) (> x 0))
           (loop-over-nodes (l left e-node-eqclass)
             (when (aref (e-node-tableau-entry l) 2)
               (return
                (push-fifo (list 'restrict l 2
                                 (list '*-l 3 3 node product l right))
                           *tableau-list*)))))
          ((setq node (node-is-negative-or-zero-p product))
           ;; (implies (and (> 0 y) (>= 0 (* x y))) (>= x 0))
           (loop-over-nodes (l left e-node-eqclass)
             (when (aref (e-node-tableau-entry l) 0)
               (return
                (push-fifo (list 'restrict l 0
                                 (list '*-l 1 3 node product l right))
                           *tableau-list*))))))))



;;; Propagate the fact that a product is negative downwards.
(defun propagate-negative-product (ref product)
  (let ((left (arg-1-node product))
        (right (arg-2-node product))
        node)
    (cond ((setq node (node-is-strictly-positive-p left))
           ;; (implies (and (> 0 (* x y)) (> x 0)) (> 0 y))
           (loop-over-nodes (r right e-node-eqclass)
             (when (aref (e-node-tableau-entry r) 3)
               (return
                (push-fifo (list 'restrict r 3
                                 (list '*-r 3 2 ref product node r))
                           *tableau-list*)))))
          ((setq node (node-is-non-negative-p left))
           ;; (implies (and (> 0 (* x y)) (>= x 0)) (>= 0 y))
           (push-fifo (list 'restrict node 2 (list '*-ll 3 0 ref product node))
                      *tableau-list*)
           (loop-over-nodes (r right e-node-eqclass)
             (when (aref (e-node-tableau-entry r) 3)
               (return
                (push-fifo (list 'restrict r 3
                                 (list '*-r 3 0 ref product node r))
                           *tableau-list*))))))
    (cond ((setq node (node-is-strictly-positive-p right))
           ;; (implies (and (> 0 (* x y)) (> y 0)) (> 0 x))
           (loop-over-nodes (l left e-node-eqclass)
             (when (aref (e-node-tableau-entry l) 3)
               (return
                (push-fifo (list 'restrict l 3
                                 (list '*-l 3 2 ref product l node))
                           *tableau-list*)))))
          ((setq node (node-is-non-negative-p right))
           ;; (implies (and (> 0 (* x y)) (>= y 0)) (>= 0 x))
           (push-fifo (list 'restrict node 2 (list '*-rr 3 0 ref product node))
                      *tableau-list*)
           (loop-over-nodes (l left e-node-eqclass)
             (when (aref (e-node-tableau-entry l) 3)
               (return
                (push-fifo (list 'restrict l 3
                                 (list '*-l 3 0 ref product l node))
                           *tableau-list*))))))
    (cond ((setq node (node-is-strictly-negative-p left))
           ;; (implies (and (> 0 (* x y)) (> 0 x)) (> y 0))
           (loop-over-nodes (r right e-node-eqclass)
             (when (aref (e-node-tableau-entry r) 2)
               (return
                (push-fifo (list 'restrict r 2
                                 (list '*-r 3 3 ref product node r))
                           *tableau-list*)))))
          ((setq node (node-is-negative-or-zero-p left))
           ;; (implies (and (> 0 (* x y)) (>= 0 x)) (> 0 x))
           (push-fifo (list 'restrict node 3 (list '*-ll 3 1 ref product node))
                      *tableau-list*)
           ;; (implies (and (> 0 (* x y)) (>= 0 x)) (> y 0))
           (loop-over-nodes (r right e-node-eqclass)
             (when (aref (e-node-tableau-entry r) 2)
               (return
                (push-fifo (list 'restrict r 2
                                 (list '*-r 3 1 ref product node r))
                           *tableau-list*))))))
    (cond ((setq node (node-is-strictly-negative-p right))
           ;; (implies (and (> 0 (* x y)) (> 0 y)) (> x 0))
           (loop-over-nodes (l left e-node-eqclass)
             (when (aref (e-node-tableau-entry l) 2)
               (return
                (push-fifo (list 'restrict l 2
                                 (list '*-l 3 3 ref product l node))
                           *tableau-list*)))))
          ((setq node (node-is-negative-or-zero-p right))
           ;; (implies (and (> 0 (* x y)) (>= 0 y)) (> 0 y))
           (push-fifo (list 'restrict node 3
                            (list '*-rr 3 1 ref product node))
                      *tableau-list*)
           ;; (implies (and (> 0 (* x y)) (>= 0 y)) (> x 0))
           (loop-over-nodes (l left e-node-eqclass)
             (when (aref (e-node-tableau-entry l) 2)
               (return
                (push-fifo (list 'restrict l 2
                                 (list '*-l 3 1 ref product l node))
                           *tableau-list*))))))))



(defun node-is-non-negative-p (e-node)
  (loop-over-nodes (node e-node e-node-eqclass)
    (when (is-restricted node 0) (return node))))

(defun node-is-negative-or-zero-p (e-node)
  (loop-over-nodes (node e-node e-node-eqclass)
    (when (is-restricted node 1) (return node))))

(defun node-is-strictly-positive-p (e-node)
  (loop-over-nodes (node e-node e-node-eqclass)
    (when (is-restricted node 2) (return node))))

(defun node-is-strictly-negative-p (e-node)
  (loop-over-nodes (node e-node e-node-eqclass)
    (when (is-restricted node 3) (return node))))

(defun reason-restricted (e-node index)
  (let ((header (aref (e-node-tableau-entry e-node) index)))
    (cond ((row-p header) (row-reason-restricted header))
          (t (col-reason-restricted header)))))


;;; Function to grab the triples of coefficient, column owner, and
;;; restriction status.  It is called by the justify fubctions below.
(defun collect-row-triples (row-header)
  (let ((triples nil))
    (do ((element (row-rnext row-header) (element-rnext element)))
        ((null element) triples)
      (push (list (element-coeff element)
                  (car (col-owners (element-col element)))
                  (col-restriction (element-col element)))
            triples))))

(defun justify-maximized (row-header)
  (list 'maximized (car (row-owners row-header))
        (collect-row-triples row-header)))

(defun justify-minimized (row-header)
  (list 'minimized (car (row-owners row-header))
        (collect-row-triples row-header)))

(defun justify-minimized-col (row-header col-header)
  (list 'minimized-col (car (row-owners row-header))
        (car (col-owners col-header)) (collect-row-triples row-header)))

(defun justify-constant (row-header)
  (list 'constant-sum (car (row-owners row-header))
        (collect-row-triples row-header)))

(defun justify-equal (row-header header)
  (list '=-sums
        (car (row-owners row-header))
        (car (if (row-p header) (row-owners header) (col-owners header)))
        (collect-row-triples row-header)
        (if (col-p header)
            (list (list 1 (car (col-owners header)) (col-restriction header)))
          (collect-row-triples header))))
