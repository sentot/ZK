
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



(proclaim '(special *rows* *cols* *zero-node* *merge-list*))

;;; Intern a sum associated with an e-node into the tableau, where index
;;; is 0, 1, 2 or 3, and the input sum is a list. The interned sum is
;;; then stored in (aref (e-node-tableau-entry e-node) index).
(defun intern-sum (e-node index input-sum)
  ;; Intern the non-constant parts of the non-constant terms.
  (let* ((intermediate-sum-1
	   (mapcar #'(lambda (u)
                       (cons (intern-subexpression
                              (wrap-ord (make-times-from-bag (car u))))
                             (cdr u)))
		   (cdr input-sum)))
         ;; Add header to each e-node resulting from above intern.
	 ;; The result is an intermediate sum in terms of headers.
	 (intermediate-sum-2
	   (mapcar #'add-header-to-e-node intermediate-sum-1))
         ;; Get the index for new row.
	 (r-index (fill-pointer *rows*)))
    ;; Nothing to do if (aref (e-node-tableau-entry e-node) index) is set.
    (unless (aref (e-node-tableau-entry e-node) index)
      ;; Initially, the interned sum will be a new row.
      (add-row *rows*)
      (let ((new-row (aref *rows* r-index)))
        ;; Intern the coefficents of intermediate sum.
        (mapc #'(lambda (u) (intern-coeff u new-row))
              intermediate-sum-2)
	;; Intern the constant part of sum.
        (intern-constant-coeff (car input-sum) new-row)
	;; Check for special cases of the new row.
        (or
	 ;; If new row is trivial, it is deleted and the interned
	 ;; sum could be a row or a column of the tableau.
	 ;; Derived facts are propagated.
	 (row-is-trivial
	  (cons (car input-sum) intermediate-sum-1)
	  e-node index r-index)
	 ;; If row is not new, it is deleted and the interned sum
	 ;; is an existing row. Derived facts are propagated.
	 (row-is-not-really-new
	  (cons (car input-sum) intermediate-sum-1)
	  e-node index r-index)
	 ;; If new row is equivalent to existing row or column,
	 ;; derived facts are propagated.
	 (progn (push (cons index e-node) (row-owners new-row))
		(push (cons (car input-sum) intermediate-sum-1)
		      (row-sums new-row))
		(push-undo (list #'undo-add-e-node
				 (cons index e-node)))
		(setf (aref (e-node-tableau-entry e-node) index) new-row)
		(check-for-equivalent-row-or-column e-node index)))))))



;;; Takes (e-node . value) pair and return (header . value) pair.
;;; If a header does not exist yet, it is created.
(defun add-header-to-e-node (input-pair)
  (let ((e-node (car input-pair)))
    (cons (or (aref (e-node-tableau-entry e-node) 0)
              (let ((length (fill-pointer *cols*))
                    (new-col (add-column *cols*)))
                (setf (aref *cols* length) new-col)
                (push (cons 0 e-node) (col-owners new-col))
                (push (list 0 (cons (car input-pair) 1))
                      (col-sums new-col))
                (setf (aref (e-node-tableau-entry e-node) 0) new-col)
                (push-undo (list #'undo-add-e-node (cons 0 e-node)))
                new-col))
          (cdr input-pair))))

;;; Intern the constant coefficient value.
(defun intern-constant-coeff (value r-row)
  (unless (zerop value)
    (intern-coeff (cons (aref *cols* 0) value) r-row)))



;;; Intern the coefficient value at the appropriate tableau element entry.
(defun intern-coeff (input-pair r-row)
  (let ((s-header (car input-pair))
	(value (cdr input-pair)))
    (cond
     ;; Case where header is a row header, must add the row multiplied
     ;; by the coefficient to the new row.
     ((row-p s-header)
      (do ((current (row-rnext s-header) (element-rnext current))
           (curr (row-rnext r-row) (row-rnext r-row))
           (prev r-row r-row))
          ((null current))
        (let ((c-index (col-index (element-col current))))
          ;; Modify value of appropriate element in the new row, creating
          ;; the element if necessary.
          (do ()
              ((or (null curr) (>= (col-index (element-col curr)) c-index))
               (cond
                ((or (null curr) (> (col-index (element-col curr)) c-index))
                 (let ((new-element (insert-element prev c-index)))
                   (setf (element-coeff new-element)
                         (rational-* (element-coeff current) value))
                   (setq prev new-element)))
                (t
                 (setf (element-coeff curr)
                       (rational-+ (rational-* (element-coeff current) value)
                                   (element-coeff curr)))
                 (when (rational-zerop (element-coeff curr))
                       (delete-element prev curr c-index)))))
            (setq prev curr)
            (setq curr (element-rnext curr))))))
     ;; Case where header is a column header, must modify value of
     ;; appropriate element in the new row, creating the element if
     ;; necessary.
     ((col-p s-header)
      (let ((c-index (col-index s-header)))
        (do ((curr (row-rnext r-row) (element-rnext curr))
             (prev r-row curr))
            ((or (null curr) (>= (col-index (element-col curr)) c-index))
             (cond
              ((or (null curr) (> (col-index (element-col curr)) c-index))
               (let ((new-element (insert-element prev c-index)))
                 (setf (element-coeff new-element) value)))
              (t
               (setf (element-coeff curr)
                     (rational-+ (element-coeff curr) value))
               (when (rational-zerop (element-coeff curr))
                     (delete-element prev curr c-index)))))))))))



;;; Check to see if the row is a trivial row. If it is then it gets deleted.
;;; Case where it gets deleted:
;;; - It is equivalent to the zero row: propagate this fact.
;;; - It is equivalent to a column, subcases:
;;;   - Column is constant column: propagate this fact.
;;;   - Column is dead: propagate this fact.
;;;   - Column is restricted: propagate this fact.
(defun row-is-trivial (sum e-node index row-index)
  (let* ((l-row (aref *rows* row-index))
	 (first-element (row-rnext l-row)))
    (cond
     ((null first-element)
      ;; Equivalent to zero row.
       (push (cons index e-node) (row-owners (aref *rows* 0)))
       (push sum (row-sums (aref *rows* 0)))
       (push-undo (list #'undo-add-e-node (cons index e-node)))
       (delete-row l-row)
       (setf (aref (e-node-tableau-entry e-node) index) (aref *rows* 0))
       (propagate-zero index e-node)
       (aref *rows* 0))
      ((and (null (element-rnext first-element))
            (rational-= (element-coeff first-element) 1))
       ;; Equivalent to a column.
       (let ((e-col (element-col first-element)))
         (when (and (zerop index) (not (node-is-relation-p e-node)))
           (dolist (owner (col-owners e-col))
             (when (and (zerop (car owner))
                        (not (node-is-relation-p (cdr owner))))
               (push-fifo (list 'merge e-node (cdr owner) 'same-sum)
                          *merge-list*)
               (return t))))
         (unless (aref (e-node-tableau-entry e-node) index)
	   (push (cons index e-node) (col-owners e-col))
           (push sum (col-sums e-col))
           (push-undo (list #'undo-add-e-node (cons index e-node))))
         (setf (aref (e-node-tableau-entry e-node) index) e-col)
	 (cond ((zerop (col-index e-col))
		;; Constant column.
                (propagate-constant index e-node 1))
               ((eq (col-restriction e-col) 'dead)
		;; Dead column.
                (propagate-zero index e-node))
               ((eq (col-restriction e-col) 'restricted)
		;; Restricted column.
                (propagate-restriction index e-node)))
         (delete-row l-row)
         e-col)))))



;;; Check to see if row is identical to some other row. If it is then
;;; it gets deleted. Derived facts are propagated.
(defun row-is-not-really-new (sum e-node index row-index)
  (let ((same-row (row-is-not-really-new-aux (aref *rows* row-index))))
    (when same-row
      (push (cons index e-node) (row-owners same-row))
      (push sum (row-sums same-row))
      (push-undo (list #'undo-add-e-node (cons index e-node)))
      (delete-row (aref *rows* row-index))
      (setf (aref (e-node-tableau-entry e-node) index) same-row)
      (cond
	((eq (row-restriction same-row) 'dead)
	 (propagate-zero index e-node))
	(t (let ((reduced-row (reduce-row same-row)))
	     (cond ((null reduced-row)
                    (kill-row same-row (justify-constant same-row)))
		   ((and (zerop index)
                         (not (node-is-relation-p e-node))
                         ;; Find some other integer expression that
                         ;; shares the same row.
                         (dolist (owner (cdr (row-owners same-row)))
                           (and (zerop (car owner))
                                (not (node-is-relation-p (cdr owner)))
                                (return (push-fifo
                                         (list 'merge e-node (cdr owner)
                                               'same-sum)
                                         *merge-list*)))))
                    t)
                   ((null (cdr reduced-row))
                    (cond ((= (col-index (caar reduced-row)) 0)
                           (propagate-constant
                            index e-node (cdar reduced-row)))
                          ((and (zerop index) (not (node-is-relation-p e-node))
                                (rational-= (cdar reduced-row) 1))
                           (dolist (owner (col-owners (caar reduced-row)))
                             (and (zerop (car owner))
                                  (not (node-is-relation-p (cdr owner)))
                                  (return
                                   (push-fifo
                                    (list 'merge e-node (cdr owner)
                                          (list '=-sums e-node
                                                (justify-equal
                                                 same-row (caar reduced-row))))
                                    *merge-list*)))))))))))
      (when (eq (row-restriction same-row) 'restricted)
	(propagate-restriction index e-node))
      same-row)))

(defun row-is-not-really-new-aux (row)
  (let ((first-col (element-col (row-rnext row))))
    (do ((element (col-cprev first-col) (element-cprev element)))
	((null element) nil)
      (let ((next-row (element-row element)))
	(when (and (neq next-row row)
		   (equal-rows next-row row))
	  (return next-row))))))

(defun node-is-relation-p (e-node)
  (or (=-p (e-node-attribute e-node))
      (>=-p (e-node-attribute e-node))))

;;; Compare elements of the two rows to see if they are equal.
(defun equal-rows (row-1 row-2)
  (do ((element-1 (row-rnext row-1) (element-rnext element-1))
       (element-2 (row-rnext row-2) (element-rnext element-2)))
      ((or (null element-1) (null element-2))
       (and (null element-1) (null element-2)))
    (unless (and (rational-= (element-coeff element-1)
                             (element-coeff element-2))
		 (eq (element-col element-1) (element-col element-2)))
      (return nil))))



;;; Check if the last row is equivalent to another row or column.
;;; Propagate derived facts.
(defun check-for-equivalent-row-or-column (e-node index)
  (let* ((l-row (aref *rows* (1- (fill-pointer *rows*))))
         (reduced-row (reduce-row l-row)))
    (cond ((null reduced-row)
           (kill-row l-row (justify-constant l-row)))
          ((and (null (cdr reduced-row)) (= (col-index (caar reduced-row)) 0))
           (propagate-constant index e-node (cdar reduced-row)))
          ((and (zerop index) (not (node-is-relation-p e-node))
                (null (cdr reduced-row)) (rational-= (cdar reduced-row) 1))
           (dolist (owner (col-owners (caar reduced-row)))
             (and (zerop (car owner))
                  (not (node-is-relation-p (cdr owner)))
                  (return (push-fifo
                           (list 'merge e-node (cdr owner)
                                 (list '=-sums e-node
                                       (justify-equal
                                        l-row (caar reduced-row))))
                           *merge-list*)))))
          ((and (zerop index) (not (node-is-relation-p e-node)))
           (dotimes (i (- (fill-pointer *rows*) 2))
               (or (zerop i)
                   (not (equal reduced-row (reduce-row (aref *rows* i))))
                   (let ((merge-propagated nil))
                     (dolist (owner (row-owners (aref *rows* i)))
                       (when (and (zerop (car owner))
                                  (not (node-is-relation-p (cdr owner))))
                         (setq merge-propagated t)
                         (return (push-fifo
                                  (list 'merge e-node (cdr owner)
                                        (list '=-sums e-node
                                              (justify-equal
                                               l-row (aref *rows* i))))
                                  *merge-list*))))
                     (when merge-propagated (return t)))))))))

;;; Construct a list of non-dead entries for a row.
(defun reduce-row (header)
  (do ((el (row-rnext header) (element-rnext el))
       (reduced-row nil))
      ((null el) reduced-row)
    (unless (eq (col-restriction (element-col el)) 'dead)
      (push (cons (element-col el) (element-coeff el)) reduced-row))))

;;; Check to see if a row contains dead entries only.
(defun row-is-dead (header)
  (do ((el (row-rnext header) (element-rnext el)))
      ((null el) t)
    (unless (eq (col-restriction (element-col el)) 'dead) (return nil))))



;;; ==================== Produce Uninterned Sum ====================

;;; Produce uninterned sum.
(defun collect-terms (input-expression)
  (collect-terms-recursively input-expression t (list 0)))

(defun collect-terms-recursively (expr positive collected-terms)
  (cond ((symbolp expr)
	 (if positive
	     (collect-non-constant expr 1 collected-terms)
	     (collect-non-constant expr -1 collected-terms)))
	((integerp expr)
	 (if positive
	     (cons (+ expr (car collected-terms)) (cdr collected-terms))
	     (cons (- (car collected-terms) expr) (cdr collected-terms))))
	((consp expr)
	 (case (first expr)
	   (-
	     (collect-terms-recursively
	       (third expr)
	       (not positive)
	       (collect-terms-recursively
                (second expr) positive collected-terms)))
           (negate (collect-terms-recursively
                    (second expr) (not positive) collected-terms))
	   (+ (collect-terms-recursively
		(third expr)
		positive
		(collect-terms-recursively
                 (second expr) positive collected-terms)))
	   (* (collect-terms-for-multiplication expr positive collected-terms))
           (ord (collect-terms-recursively
		 (ord-expr expr) positive collected-terms))
	   (t (if positive
		  (collect-non-constant expr 1 collected-terms)
		  (collect-non-constant expr -1 collected-terms)))))
	(t (if positive
	       (collect-non-constant expr 1 collected-terms)
	       (collect-non-constant expr -1 collected-terms)))))



;;; Multiplication is handled specially.
(defun collect-terms-for-multiplication (expr positive collected-terms)
  (cond ((integerp (second expr))
	 (if (integerp (third expr))
	     (if positive
		 (cons (+ (car collected-terms) (* (second expr) (third expr)))
		       (cdr collected-terms))
		 (cons (- (car collected-terms) (* (second expr) (third expr)))
		       (cdr collected-terms)))
	     (add-collected-terms
	       (multiply-collected-terms-by-constant
		 (collect-terms (third expr))
                 (if positive (second expr) (- (second expr))))
	       collected-terms)))
	((integerp (third expr))
	 (add-collected-terms
	   (multiply-collected-terms-by-constant
	     (collect-terms (second expr))
             (if positive (third expr) (- (third expr))))
	   collected-terms))
	(t (multiply-and-collect-terms
	     (collect-terms (second expr))
	     (collect-terms (third expr))
	     positive
	     collected-terms))))

(defun multiply-collected-terms-by-constant (collected-terms constant)
  (cond ((zerop constant) (list 0))
	(t (cons (* (car collected-terms) constant)
		 (mapcar #'(lambda (u) (cons (car u) (* (cdr u) constant)))
			 (cdr collected-terms))))))



(defun multiply-and-collect-terms
  (collected-1 collected-2 positive collected-terms)
  (let ((collected-3 collected-terms)
	(c1 (car collected-1))
	(c2 (car collected-2)))
    (unless (zerop c1)
      (setq collected-3
            (add-collected-terms (multiply-collected-terms-by-constant
                                  collected-2
                                  (if positive c1 (- c1)))
                                 collected-3)))
    (unless (zerop c2)
      (setq collected-3
            (add-collected-terms (multiply-collected-terms-by-constant
                                  (cons 0 (cdr collected-1))
                                  (if positive c2 (- c2)))
                                 collected-3)))
    (dolist (pair-1 (cdr collected-1))
      (dolist (pair-2 (cdr collected-2))
	(setq collected-3
              (insert-term (coalesce-bags (car pair-1) (car pair-2))
                           (if positive (* (cdr pair-1) (cdr pair-2))
                             (- (* (cdr pair-1) (cdr pair-2))))
                           collected-3))))
    collected-3))

;;; Insert a term into collected terms.
(defun insert-term (factor coeff collected-terms)
  (cons (car collected-terms)
	(let ((leading-non-constants nil)
	      (trailing-non-constants (cdr collected-terms)))
	  (if (null trailing-non-constants)
	      (list (cons factor coeff))
	      (do ((term (car trailing-non-constants)
                         (car trailing-non-constants)))
		  ((null trailing-non-constants)
                   (nreconc leading-non-constants
                            (list (cons factor coeff))))
		(cond ((equal factor (car term))
		       (let ((new-coeff (+ coeff (cdr term))))
			 (if (zerop new-coeff)
			     (return (nreconc leading-non-constants
					      (cdr trailing-non-constants)))
			     (return (nreconc
                                      leading-non-constants
                                      (cons (cons factor new-coeff)
                                            (cdr trailing-non-constants)))))))
		      ((smaller-bag-p factor (car term))
		       (return (nreconc leading-non-constants
					(cons (cons factor coeff)
                                              trailing-non-constants))))
		      (t (push term leading-non-constants)
			 (pop trailing-non-constants))))))))



;;; Combine two collected terms.
(defun add-collected-terms (collected-1 collected-2)
  (cons (+ (car collected-1) (car collected-2))
	(add-collected-terms-recursively (cdr collected-1) (cdr collected-2))))

(defun add-collected-terms-recursively (collected-1 collected-2)
  (cond ((null collected-1) collected-2)
	((null collected-2) collected-1)
	(t (let ((term-1 (car collected-1))
		 (term-2 (car collected-2)))
	     (let ((factor-1 (car term-1))
		   (factor-2 (car term-2)))
	       (cond ((equal factor-1 factor-2)
		      (let ((new-coeff (+ (cdr term-1) (cdr term-2))))
			(if (zerop new-coeff)
			    (add-collected-terms-recursively (cdr collected-1)
							     (cdr collected-2))
			    (cons (cons factor-1 new-coeff)
				  (add-collected-terms-recursively
                                   (cdr collected-1)
                                   (cdr collected-2))))))
		     ((smaller-bag-p factor-1 factor-2)
		      (cons term-1 (add-collected-terms-recursively
                                    (cdr collected-1)
                                    collected-2)))
		     (t (cons term-2
			      (add-collected-terms-recursively
                               collected-1
                               (cdr collected-2))))))))))

;;; Combine two bags.
(defun coalesce-bags (bag-1 bag-2)
  (cond ((null bag-1) bag-2)
	((null bag-2) bag-1)
	((lexically-smaller-p (car bag-2) (car bag-1))
	 (cons (car bag-2) (coalesce-bags bag-1 (cdr bag-2))))
	(t (cons (car bag-1) (coalesce-bags (cdr bag-1) bag-2)))))



;;; Add a non-constant term to a sum of collected terms.
(defun collect-non-constant (expression coeff collected-terms)
  (if (zerop coeff)
      collected-terms
      (cons (car collected-terms)
	    (insert-non-constant
             (list expression) coeff (cdr collected-terms)))))

(defun insert-non-constant (bag coeff collected-terms)
  (cond ((null collected-terms) (list (cons bag coeff)))
	(t (let ((next-term (car collected-terms)))
	     (cond ((equal bag (car next-term))
		    (let ((new-coeff (+ coeff (cdr next-term))))
		      (if (zerop new-coeff)
			  (cdr collected-terms)
			  (cons (cons bag new-coeff) (cdr collected-terms)))))
		   ((smaller-bag-p bag (car next-term))
		    (cons (cons bag coeff) collected-terms))
		   (t (cons next-term
			    (insert-non-constant
                             bag coeff (cdr collected-terms)))))))))

;;; ==================== End of Produce Uninterned Sum ====================



;;; -------------------- Useful Functions for Sums --------------------

;;; Make a stronger inequality implied by the linear sum. The
;;; inequality is "shifted".
(defun make-stronger (collected-terms)
  (let ((the-gcd (apply #'gcd (mapcar #'cdr (cdr collected-terms)))))
    (cond ((> the-gcd 1)
           (cons (quotient (- (car collected-terms)
                              (mod (car collected-terms) the-gcd))
                           the-gcd)
                 (mapcar #'(lambda (u)
                             (cons (car u) (quotient (cdr u) the-gcd)))
                         (cdr collected-terms))))
          (t collected-terms))))

;;; Return the index to the opposite sum given an index and an e-node.
;;; An example of opposite sums are "b - a" and "a - b - 1" (the first
;;; sum represents "b >= a", while the second sum represents "a > b").
(defun opposite-index (e-node index)
  (let ((op (e-node-operation e-node)))
    (if (eq op '>=)
	(- 1 index)
	(- 3 index))))

;;; Return the opposite sum given a sum.
(defun opposite-sum (sum)
  (let ((intermediate-sum
	  (cons (- (- (car sum)) 1)
		(mapcar #'(lambda (u) (cons (car u) (- (cdr u))))
                        (cdr sum)))))
    (make-stronger intermediate-sum)))

;;; Return the arithmetic negation of a sum.
(defun negative-sum (sum)
  (cons (- (car sum))
        (mapcar #'(lambda (u) (cons (car u) (- (cdr u)))) (cdr sum))))

;;; Return a stricter sum (a sum that represents an equivalent integer
;;; inequality but may be a stronger rational inequality).
(defun stricter-sum (sum)
  (make-stronger (cons (- (car sum) 1) (cdr sum))))


;;; ---------- Useful functions for integer expressions ----------

;;; Predicate for non-trivial product (i.e., non-lnear expression).
(defsubst non-trivial-product-p (expr)
  (and (*-p expr)
       (not (integerp (*-left expr)))
       (not (integerp (*-right expr)))))

;;; Arithmetic negation of an integer expression.
(defun negate-integer-expression (expr)
  (cond ((integerp expr) (- expr))
	((negate-p expr) (second expr))
	((--p expr) (make-- (--right expr) (--left expr)))
	(t (make-negate expr))))

;;; Predicate for arithmetic expression.
(defun arithmetic-expression-p (expr)
  (or (+-p expr) (--p expr) (*-p expr) (negate-p expr)))


;;; ---------- Conversion from interned sum to integer expressions

(defun raw-expr-of-sum (sum)
  (cond ((null (cdr sum)) (car sum))
        (t (make-+ (car sum) (raw-expr-of-sum-aux (cdr sum))))))

(defun raw-expr-of-sum-aux (sum)
  (cond ((null (cdr sum))
         (make-* (cdar sum)
                 (if (e-node-p (caar sum))
                     (e-node-attribute (caar sum))
                   (make-times-from-bag (caar sum)))))
        (t (make-+ (make-* (cdar sum)
                           (if (e-node-p (caar sum))
                               (e-node-attribute (caar sum))
                             (make-times-from-bag (caar sum))))
                   (raw-expr-of-sum-aux (cdr sum))))))
