
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

;;; ==================== Pivoting the Tableau ====================


;;; Code for pivoting the tableau and for finding candidates for
;;; pivoting.

;;; The pivoting algorithm used is the sparse matrix pivoting algorithm
;;; described in Knuth's "The Art of Computer Programming - v 1"
;;; pp. 301-302.

;;; --------------------------------------------------------------------

;;; Global symbols used.

(proclaim '(special *rows* *cols*))

;;; Top level pivoting routine.

;;; Pivot the tableau given the pivoting element.
(defun pivot (p-element)
  (let ((pivot-row (element-row p-element))
	(pivot-col (element-col p-element))
	(alpha	(rdiv -1 (element-coeff p-element))))	; set alpha to -1/a
    ;; set coefficient of pivot element to -1.
    (setf (element-coeff p-element) -1)
    ;; process elements of pivot row first.
    (process-pivot-row pivot-row alpha)
    ;; now, process non-pivot rows.
    (process-non-pivot-rows p-element pivot-row pivot-col alpha)
    ;; switch attributes of pivot row and column.
    (swapf (row-owners pivot-row) (col-owners pivot-col))
    (swapf (row-restriction pivot-row) (col-restriction pivot-col))
    (swapf (row-reason-restricted pivot-row) (col-reason-restricted pivot-col))
    (swapf (row-reason-killed pivot-row) (col-reason-killed pivot-col))
    (swapf (row-sums pivot-row) (col-sums pivot-col))
    (dolist (owner (row-owners pivot-row))
      (setf (aref (e-node-tableau-entry (cdr owner)) (car owner)) pivot-row))
    (dolist (owner (col-owners pivot-col))
      (setf (aref (e-node-tableau-entry (cdr owner)) (car owner)) pivot-col))))

;;; Multiply coefficients of the elements of the pivot row by -1/a (alpha).
(defun process-pivot-row (pivot-row alpha)
  ;; Iterate over elements of pivot row and multiply the coefficient by -1/a.
  (do ((current (row-rnext pivot-row) (element-rnext current)))
      ((null current))
    (setf (element-coeff current) (rational-* alpha (element-coeff current)))))

;;; Iterate over non-pivot rows invoking process-row.
(defun process-non-pivot-rows (pivot-element pivot-row pivot-col alpha)
  (do ((current (col-cprev pivot-col) (element-cprev current)))
      ((null current))
    (or (eq current pivot-element) ; don't process pivot row.
	(process-row current pivot-row pivot-col alpha))))

;;; Process elements of a non-pivot row changing the coefficients.
;;; The formulas used to change the coefficients are:
;;; - for the pivot-column element: - c/a
;;; - for non-pivot-column elements: d - bc/a
;;; where
;;; a is coefficient of the pivoting element before pivot
;;; b is coefficient of corresponding element in pivot row before pivot
;;; c is coefficient of pivot-column element before pivot
;;; d is coefficient of current element before pivot
(defun process-row (pivot-col-element pivot-row pivot-col alpha)
  ;; Main loop iterates over elements of the row.
  (do ((p-element (row-rnext pivot-row) (element-rnext p-element))
       (previous (element-row pivot-col-element))
       (current (row-rnext (element-row pivot-col-element)))
       (pivot-index (col-index pivot-col))
       (c-index))
      ((null p-element)
       ;; Finally c becomes c/a
       (setf (element-coeff pivot-col-element)
	     (rational-* (rational-minus alpha)
                         (element-coeff pivot-col-element))))
    (let ((p-index (col-index (element-col p-element))))
      ;; synchronize iteration over elements of current row with
      ;; iteration over elements of pivot row (the coefficient of
      ;; an element in the current row that do not have a
      ;; corresponding element in the pivot row remains the same
      ;; according to the formula: d - bc/a).
      (do ()
	  ((or (null current)
               (>= (setq c-index (col-index (element-col current))) p-index)))
	(setq previous current)
	(setq current (element-rnext current)))
      ;; need to create new element?
      (unless (= c-index p-index)
        (setq current (insert-element previous p-index)))
      (unless (= p-index pivot-index) ; c remains c
	(setf (element-coeff current) ; d becomes d - bc/a
	      (rational-+ (element-coeff current)
			  (rational-* (element-coeff pivot-col-element)
				      (element-coeff p-element)))))
      ;; need to delete element?
      (when (rational-zerop (element-coeff current))
	(delete-element previous current p-index)
	(setq current
              (if (row-p previous)
                  (row-rnext previous)
                (element-rnext previous)))))))

;;; Find a pivot element given the header of a row whose sample value
;;; is to be raised.
(defun find-pivot-to-raise (header)
  (let ((ref-element (find-reference-element header t)))
    (when ref-element
      (do ((chal (col-cprev (element-col ref-element)) ; the challenger.
		 (element-cprev chal))
	   (champ ref-element)) ; champ is the champion.
	  ((null chal) champ) ; no more challenger?
	(unless	(or (eq chal ref-element)
		    (null (row-restriction (element-row chal))))
	  (when (rational-minusp ; is challenger bonafide?
		  (rational-* (element-coeff chal)
                              (element-coeff ref-element)))
	    (if (eq champ ref-element)
		(setq champ chal) ; challenger wins by default
		(setq champ (break-tie champ chal))))))))) ; break the tie

;;; Find a pivot element given the header of a row whose sample value is to
;;; be lowered.
(defun find-pivot-to-lower (header)
  (let ((ref-element (find-reference-element header nil)))
    (when ref-element
      (do ((chal (col-cprev (element-col ref-element)) ; the challenger.
		 (element-cprev chal))
	   (champ ref-element)) ; champ is the champ.
	  ((null chal) champ) ; no more challenger?
	(unless (or (eq chal ref-element)
		    (null (row-restriction (element-row chal))))
	  (when (rational-plusp ; is challenger bonafide?
		  (rational-* (element-coeff chal)
                              (element-coeff ref-element)))
	    (if (eq champ ref-element)
		(setq champ chal) ; challenger wins by default
		(setq champ (break-tie champ chal))))))))) ; break the tie

;;; Find a pivot element given the header of the row to be pivoted.
;;; It assumes that it is ok to pivot the row.
(defun find-pivot-given-row (header)
  (do ((el (row-rnext header) (element-rnext el)))
      ((null el) (error "Finding pivot found the database in a bad state"))
    (let ((column-restriction (col-restriction (element-col el))))
      (when (or (null column-restriction) (eq column-restriction 'restricted))
	(return el)))))

;;; Find a pivot element given the header of the column to be pivoted.
(defun find-pivot-given-column (header)
  (let* ((ref-element (col-cprev header))
	 (sign (if (rational-plusp (element-coeff ref-element)) 1 -1)))
    (do ((chal (element-cprev ref-element) ; the challenger.
	       (element-cprev chal))
	 (champ ref-element)) ; champ is the champ.
	((null chal) champ) ; no more challenger?
      (when (and (eq (row-restriction (element-row chal)) 'restricted)
		 (rational-minusp ; is challenger bonafide?
		   (rational-* (element-coeff chal) sign)))
	(if (eq champ ref-element)
	    (setq champ chal) ; challenger wins by default
	    (setq champ (break-tie champ chal))))))) ; break the tie

;;; Find a reference element in a row that determines the pivot column.
(defun find-reference-element (r-row raising)
  (do ((next (row-rnext r-row) (element-rnext next))
       (reference nil))
      ;; prefer an unrestricted column.
      ((or (null next) (null (col-restriction (element-col next))))
       (or next reference))
      ;; otherwise, a restricted column that has the right sign will do.
    (when (and (null reference)
	       (eq (col-restriction (element-col next)) 'restricted)
	       (if raising
		   (rational-plusp (element-coeff next))
		   (rational-minusp (element-coeff next))))
      (setq reference next))))

;;; Determine the winner between two rows competing to become the pivot row.
(defun break-tie (champ chal)
  (let ((champ-abs-value (rational-abs (element-coeff champ)))
	(chal-abs-value (rational-abs (element-coeff chal))))
    (do ((c-champ (row-rnext (element-row champ)) (element-rnext c-champ))
	 (c-chal (row-rnext (element-row chal))	(element-rnext c-chal))
	 (new-champ))
	((or
          ;; entry in champion's row is zero - the tie is broken.
          (and (null c-champ) (null c-chal) (setq new-champ champ)) ; ****
          (and (null c-champ)
               (setq new-champ
                     (if (rational-plusp (element-coeff c-chal)) champ chal)))
          ;; entry in challenger's row is zero - the tie is broken.
          (and (null c-chal)
               (setq new-champ
                     (if (rational-plusp (element-coeff c-champ)) chal champ)))
	   
          (let ((champ-index (col-index (element-col c-champ)))
                (chal-index (col-index (element-col c-chal))))
            (or
             ;; entry in challenger's row is zero - the tie is broken.
             (and (rational-< champ-index chal-index)
                  (setq new-champ
                        (if (rational-plusp (element-coeff c-champ))
                            chal
                          champ)))
             ;; entry in champion's row is zero - the tie is broken.
             (and (rational-> champ-index chal-index)
                  (setq new-champ
                        (if (rational-plusp (element-coeff c-chal))
                            champ
                          chal)))
	       (let ((champ-ratio (rdiv (element-coeff c-champ)
                                        champ-abs-value))
		     (chal-ratio (rdiv (element-coeff c-chal) chal-abs-value)))
                 ;; both entries non-zero; check ratios.
		 (or
                  ;; champion wins.
                  (and (rational-< champ-ratio chal-ratio)
                       (setq new-champ champ))
                  ;; challenger wins.
                  (and (rational-> champ-ratio chal-ratio)
                       (setq new-champ chal)))))))
	 new-champ))))

;;; Insert an element as the rnext of previous at the column specified
;;; by c-index, where previous is a row header or an element and
;;; c-index is a column index.
(defun insert-element (previous c-index)
  (let ((new (make-element))
	(r-index (if (row-p previous)
		     (row-index previous)
		     (row-index (element-row previous)))))
    (setf (element-coeff new) 0) ; set the coefficient of new element to 0.
    (cond
     ;; previous is a row header, the element is
     ;; inserted at the beginning of the row.
     ((row-p previous)
      (setf (element-rnext new) (row-rnext previous))
      (setf (row-rnext previous) new)
      (setf (element-row new) previous))
     ;; previous is an element, the element is inserted after previous.
     ((element-p previous)
      (setf (element-rnext new) (element-rnext previous))
      (setf (element-rnext previous) new)
      (setf (element-row new) (element-row previous))))
    (do* ((next (aref *cols* c-index) current)
	  (current (col-cprev next) (element-cprev current)))
	 ((or (null current) (< (row-index (element-row current)) r-index))
	  (cond
           ;; next is a column header, the element is inserted at the end
           ;; of the column.
           ((col-p next)
            (setf (col-cprev next) new)
            (setf (element-cprev new) current)
            (setf (element-col new) next))
           ;; next is an element, the element is inserted before next.
           ((element-p next)
            (setf (element-cprev next) new)
            (setf (element-cprev new) current)
            (setf (element-col new) (element-col next))))
	  new))))

;;; Delete the tableau element specified by current where
;;; - previous is a row header or an element whose rnext is current
;;; - c-index is the column index of current.
(defun delete-element (previous current c-index)
  (cond
   ;; previous is a row header, the deleted element was at the
   ;; beginning of the row.
   ((row-p previous) (setf (row-rnext previous) (element-rnext current)))
   ;; previous is an element, modify rnext of previous.
   ((element-p previous)
    (setf (element-rnext previous) (element-rnext current))))
  ;; search up the column
  (do* ((next (aref *cols* c-index) curr)
	(curr (col-cprev next) (element-cprev curr)))
       ((eq curr current)
	(cond
         ;; next is a column header, the deleted element was at the end
         ;; of the col.
         ((col-p next) (setf (col-cprev next) (element-cprev current)))
         ;; next is an element, modify cprev of next.
         ((element-p next)
          (setf (element-cprev next) (element-cprev current)))))))

;;; Delete a non-empty column whose header is d-col.
(defun delete-column (d-col)
  (loop for i from (1+ (col-index d-col)) ; move column to the end,
	      to (1- (fill-pointer *cols*))
	do (let ((i-col (aref *cols* i)))
	     (setf (col-index i-col) (1- i))
	     (setf (aref *cols* (1- i)) i-col)))
  (decrease-size-of-array *cols*)) ; and then delete it.

;;; Delete row whose header is d-row.
(defun delete-row (d-row)
  ;; delete all elements of the row.
  (do ((current (row-rnext d-row) (element-rnext current)))
      ((null current))
    (delete-element d-row current (col-index (element-col current))))
  (loop for i from (1+ (row-index d-row)) ; move row to the bottom,
	      to (1- (fill-pointer *rows*))
	do (let ((i-row (aref *rows* i)))
	     (setf (row-index i-row) (1- i))
	     (setf (aref *rows* (1- i)) i-row)))
  (decrease-size-of-array *rows*)) ; and then delete it.
