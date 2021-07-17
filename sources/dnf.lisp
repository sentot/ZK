
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

;;; =============== Conjunctive/Disjunctive Normal Forms ===============

;;; Code to do CNF/DNF using the Minato-Morreale technique. For our
;;; purposes, the technique is more than good enough. The BDD is based
;;; on Sentot's BDD implementation for a symbolic model checker.


(defconstant bdd-hash-table-size 131072)
(defconstant bdd-hash-table-mask (1- bdd-hash-table-size))
(defconstant recache-threshold 262144)

(defconstant hash-multiplier 5)
(defconstant second-hash-multiplier 3)

(defvar *atom-list* nil)

(defvar *bdd-entries* (make-array 8192 :initial-element nil))
(defvar *bdd-entries-size* 0)

(defsubst push-bdd-entry (bdd)
  (setf (aref *bdd-entries* *bdd-entries-size*) bdd)
  (let ((result *bdd-entries-size*))
    (setq *bdd-entries-size* (fixnum-op + *bdd-entries-size* 1))
    result))

(defsubst bdd-entry (index)
  (aref *bdd-entries* index))

(defsubst pop-bdd-entry ()
  (setf (aref *bdd-entries* *bdd-entries-size*) nil)
  (setq *bdd-entries-size* (fixnum-op - *bdd-entries-size* 1)))

(defvar *atom-array* (vector))

;;; The *if-hash-table* plays a vital role in ensuring that the BDD
;;; structures are shared.
;;; Each element of *if-hash-table* is a list of entries.
;;; Each entry is of the "if" form: (id test-id left-bdd right-bdd).

(defvar *if-hash-table* (make-array bdd-hash-table-size
                                    :initial-element nil))

(defvar *if-count* 0)
(defvar *recaching* nil)

;;; The *not-hash-table* also plays a vital role in ensuring that
;;; the BDD structures are shared.
;;; Each element of *not-hash-table* is a list of entries.
;;; Each entry is of the "not" form: (id unsigned-bdd),
;;; where the unsigned-bdd represents an "unsigned" formula.

(defvar *not-hash-table* (make-array bdd-hash-table-size
                                     :initial-element nil))

;;; The next two tables are for memoizing subfunction operations.
;;; The tables are not vital in that deleting entries in the
;;; tables does not effect the correct operation of the BDD.

(defvar *sub0-hash-table* (make-array bdd-hash-table-size
                                      :initial-element nil))

(defvar *sub1-hash-table* (make-array bdd-hash-table-size
                                      :initial-element nil))

;;; The *and-hash-table* is also for memoizing only:

(defvar *and-hash-table* (make-array bdd-hash-table-size
                                     :initial-element nil))

;;; The *recache-table* plays a vital role in ensuring the
;;; correct operation of the "garbage collector".

(defvar *recache-table* (make-array bdd-hash-table-size
                                    :initial-element nil))


(defvar *next-id* 2)
(defvar *number-of-atoms* 0)

(defvar *bdd-zero* 0)
(defparameter *bdd-one* (list 1 0))

(defsubst bdd-id (formula)
  (if (atom formula) formula (car formula)))

(defsubst bdd-negated-p (formula)
  (and (consp formula) (= (length formula) 2)))

(defsubst bdd-top (formula)
  (cond ((atom formula) formula)
        ((atom (second formula)) (second formula))
        (t (second (second formula)))))


;;; Hash consing and memoizing

;;; Haven't tried to "optimize" the hashing function to get a good
;;; distribution, except for *not-hash-table*.


(defun lookup-memo-for-and (left-id right-id)
  ;; andop is commutative, so normalize arguments to low, high
  (let ((low-id (fixnum-op min left-id right-id))
        (high-id (fixnum-op max left-id right-id)))
    (loop for x in 
          (unsafe-aref
           *and-hash-table*
           (fixnum-op logand
                      (fixnum-op +
                                 (fixnum-op * low-id hash-multiplier)
                                 high-id)
                      bdd-hash-table-mask))
	  when (and (fixnum-rel = low-id (caar x))
		    (fixnum-rel = high-id (cdar x)))
	  return (cdr x))))

(defsubst memoize-and (left-id right-id result)
  ;; andop is commutative, so normalize arguments to low, high
  (let ((low-id (fixnum-op min left-id right-id))
        (high-id (fixnum-op max left-id right-id)))
    (let ((index (fixnum-op
                  logand
                  (fixnum-op + (fixnum-op * low-id hash-multiplier) high-id)
                  bdd-hash-table-mask)))
      (setf (unsafe-aref *and-hash-table* index)
            (cons (cons (cons low-id high-id) result)
		  (unsafe-aref *and-hash-table* index))))))

;;; "nots" are not really memoized, but rather, they are hash-consed
;;; (to use J Moore's terminology).

(defsubst lookup-memo-for-not (formula)
  (let ((id (bdd-id formula)))
    (loop for x in
          (unsafe-aref *not-hash-table*
                       (fixnum-op logand id bdd-hash-table-mask))
          when (eq (second x) formula)
          return x)))

(defsubst memoize-not (formula result)
  (let* ((id (bdd-id formula))
         (index (fixnum-op logand id bdd-hash-table-mask)))
    (setf (unsafe-aref *not-hash-table* index)
          (cons result (unsafe-aref *not-hash-table* index)))))

(defsubst lookup-memo-for-sub0 (var formula)
  (let ((id (bdd-id formula)))
    (loop for x in 
          (unsafe-aref
           *sub0-hash-table*
           (fixnum-op logand
                      (fixnum-op + (fixnum-op * var hash-multiplier) id)
                      bdd-hash-table-mask))
	  when (and (fixnum-rel = var (caar x))
		    (fixnum-rel = id (cdar x)))
	  return (cdr x))))

(defsubst memoize-sub0 (var formula result)
  (let ((id (bdd-id formula)))
    (let ((index (fixnum-op
                  logand
                  (fixnum-op + (fixnum-op * var hash-multiplier) id)
                  bdd-hash-table-mask)))
      (setf (unsafe-aref *sub0-hash-table* index)
            (cons (cons (cons var id) result)
		  (unsafe-aref *sub0-hash-table* index))))))

(defsubst lookup-memo-for-sub1 (var formula)
  (let ((id (bdd-id formula)))
    (loop for x in 
          (unsafe-aref
           *sub1-hash-table*
           (fixnum-op logand
                      (fixnum-op + (fixnum-op * var hash-multiplier) id)
                      bdd-hash-table-mask))
	  when (and (fixnum-rel = var (caar x))
		    (fixnum-rel = id (cdar x)))
	  return (cdr x))))

(defsubst memoize-sub1 (var formula result)
  (let ((id (bdd-id formula)))
    (let ((index (fixnum-op
                  logand
                  (fixnum-op + (fixnum-op * var hash-multiplier) id)
                  bdd-hash-table-mask)))
      (setf (unsafe-aref *sub1-hash-table* index)
            (cons (cons (cons var id) result)
		  (unsafe-aref *sub1-hash-table* index))))))

;;; Reconstruction of bdds after "garbage collection" are really
;;; "hash-consing" operations.

(defsubst lookup-memo-for-recache (formula)
  (let ((id (bdd-id formula)))
    (loop for x in (unsafe-aref *recache-table*
                                (fixnum-op logand id bdd-hash-table-mask))
          when (fixnum-rel = id (car x))
          return (cdr x))))

(defsubst memoize-recache (id formula)
  (let ((index (fixnum-op logand id bdd-hash-table-mask)))
    (setf (unsafe-aref *recache-table* index)
          (cons (cons id formula)
                (unsafe-aref *recache-table* index)))))

;;; The top level function for "garbage collection":

(defun bdd-clear-and-recache ()
  ;(format t "~%Clearing and starting new cache~%")
  (dotimes (i bdd-hash-table-size)
    (setf (aref *if-hash-table* i) nil)
    (setf (aref *recache-table* i) nil)
    (setf (aref *not-hash-table* i) nil)
    (setf (aref *sub0-hash-table* i) nil)
    (setf (aref *sub1-hash-table* i) nil)
    (setf (aref *and-hash-table* i) nil))
  (setq *if-count* 0)
  (setq *next-id* (+ *number-of-atoms* 2))
  (let ((*recaching* t))
    (let ((results (loop for i from 0 to (- *bdd-entries-size* 1)
                         do (setf (aref *bdd-entries* i)
                                  (bdd-recache (aref *bdd-entries* i))))))
      (dotimes (i bdd-hash-table-size)
               (setf (aref *recache-table* i) nil))
      results)))

;;; Function to create the negation of a BDD node.

(defsubst bdd-negate (formula)
  (cond ((eq formula *bdd-zero*) *bdd-one*)
        ((eq formula *bdd-one*) *bdd-zero*)
        ((and (consp formula) (= (length formula) 2))
         (second formula))
        (t (or (lookup-memo-for-not formula)
               (let ((result (list *next-id* formula)))
                 (setq *next-id* (+ *next-id* 1))
                 (memoize-not formula result)
                 result)))))

;;; Function to create an "if" node in a BDD.

(defun bdd-make-if (test left right)
  (cond ((equal left right) left)
        ((and (consp right) (= (length right) 2))
         (let ((negated-left (bdd-negate left))
               (negated-right (bdd-negate right)))
           (let ((index (fixnum-op
                         logand
                         (fixnum-op + 
                                    (fixnum-op * (bdd-id test) hash-multiplier)
                                    (fixnum-op
                                     + (fixnum-op
                                        * (bdd-id negated-left)
                                        second-hash-multiplier)
                                     (bdd-id negated-right)))
                         bdd-hash-table-mask)))
             (bdd-negate
              (or (loop for x in (unsafe-aref *if-hash-table* index)
                        when (and (eq test (if-test x))
                                  (eq negated-left (if-left x))
                                  (eq negated-right (if-right x)))
                        return x)
                  (let ((need-to-recache (fixnum-op logand
                                                    recache-threshold
                                                    *if-count*)))
                    (cond
                     ((= need-to-recache 0)
                      (let ((if-form (list *next-id* test negated-left
                                           negated-right)))
                        (unless *recaching*
                          (setq *if-count* (+ *if-count* 1)))
                        (setq *next-id* (+ *next-id* 1))
                        (setf (unsafe-aref *if-hash-table* index)
                              (cons if-form
                                    (unsafe-aref *if-hash-table* index)))
                        if-form))
                     (t
                      (let ((left-index (push-bdd-entry negated-left))
                            (right-index (push-bdd-entry negated-right)))
                        (bdd-clear-and-recache)
                        (let ((if-form (list *next-id* test
                                             (bdd-entry left-index)
                                             (bdd-entry right-index)))
                              (index
                               (fixnum-op
                                logand
                                (fixnum-op
                                 +
                                 (fixnum-op * (bdd-id test) hash-multiplier)
                                 (fixnum-op
                                  + (fixnum-op
                                     * (bdd-id (bdd-entry left-index))
                                     second-hash-multiplier)
                                  (bdd-id (bdd-entry right-index))))
                                bdd-hash-table-mask)))
                          (pop-bdd-entry)
                          (pop-bdd-entry)
                          (unless *recaching*
                            (setq *if-count* (+ *if-count* 1)))
                          (setq *next-id* (+ *next-id* 1))
                          (setf (unsafe-aref *if-hash-table* index)
                                (cons if-form
                                      (unsafe-aref *if-hash-table* index)))
                          if-form))))))))))
	(t
         (let ((index (fixnum-op
                       logand
                       (fixnum-op + 
                                  (fixnum-op * (bdd-id test) hash-multiplier)
                                  (fixnum-op
                                   + (fixnum-op
                                      * (bdd-id left) second-hash-multiplier)
                                   (bdd-id right)))
                       bdd-hash-table-mask)))
           (or (loop for x in (unsafe-aref *if-hash-table* index)
                     when (and (eq test (if-test x))
                               (eq left (if-left x))
                               (eq right (if-right x)))
                     return x)
               (let ((need-to-recache (fixnum-op logand
                                                 recache-threshold
                                                 *if-count*)))
                 (cond
                  ((= need-to-recache 0)
                   (let ((if-form (list *next-id* test left right)))
                     (unless *recaching*
                       (setq *if-count* (+ *if-count* 1)))
                     (setq *next-id* (+ *next-id* 1))
                     (setf (unsafe-aref *if-hash-table* index)
                           (cons if-form
                                 (unsafe-aref *if-hash-table* index)))
                     if-form))
                  (t
                   (let ((left-index (push-bdd-entry left))
                         (right-index (push-bdd-entry right)))
                     (bdd-clear-and-recache)
                     (let ((result (list *next-id* test
                                         (bdd-entry left-index)
                                         (bdd-entry right-index)))
                           (index
                            (fixnum-op
                             logand
                             (fixnum-op
                              +
                              (fixnum-op * (bdd-id test) hash-multiplier)
                              (fixnum-op
                               + (fixnum-op
                                  * (bdd-id (bdd-entry left-index))
                                  second-hash-multiplier)
                               (bdd-id (bdd-entry right-index))))
                             bdd-hash-table-mask)))
                       (pop-bdd-entry)
                       (pop-bdd-entry)
                       (unless *recaching*
                         (setq *if-count* (+ *if-count* 1)))
                       (setq *next-id* (+ *next-id* 1))
                       (setf (unsafe-aref *if-hash-table* index)
                             (cons result
                                   (unsafe-aref *if-hash-table* index)))
                       result))))))))))

;;; Function to "reconstruct" a BDD node after "garbage collection".

(defun bdd-recache (formula)
  (cond ((or (eq formula *bdd-zero*) (eq formula *bdd-one*)) formula)
        (t (or (lookup-memo-for-recache formula)
               (cond
                ((= (length formula) 2)
                 (let ((result (bdd-negate (bdd-recache (second formula)))))
                   (memoize-recache (bdd-id formula) result)
                   result))
                (t
                 (let ((result
                        (bdd-make-if (if-test formula)
                                     (bdd-recache (if-left formula))
                                     (bdd-recache (if-right formula)))))
                   (memoize-recache (bdd-id formula) result)
                   result)))))))



;;; =========== The "merge-sorting" functions ============


;;; All boolean connectives are converted to use the "and"
;;; operation and negation (instead of "nand" or "nor").

(defsubst andop-constant (formula negated1 negated2)
  (cond ((not negated1) *bdd-zero*)
        (negated2 (bdd-negate formula))
        (t formula)))

(defsubst complementary (formula1 formula2)
  (or (and (consp formula1)
           (= (length formula1) 2)
           (eq (second formula1) formula2))
      (and (consp formula2)
           (= (length formula2) 2)
           (eq (second formula2) formula1))))

(defsubst bdd-unnegated (formula)
  (if (bdd-negated-p formula) (second formula) formula))

(defsubst bdd-compute-sense (formula negated)
  (if (bdd-negated-p formula) (not negated) negated))

(defun andop-aux (formula1 formula2 negated1 negated2)
  (cond
   ((eq formula1 *bdd-zero*)
    (andop-constant formula2 negated1 negated2))
   ((eq formula2 *bdd-zero*)
    (andop-constant formula1 negated2 negated1))
   ((eq formula1 formula2)
    (if negated1
	(if negated2 (bdd-negate formula1) *bdd-zero*)
      (if negated2 *bdd-zero* formula1)))
   (t
    (let ((expr1 (if negated1 (bdd-negate formula1) formula1))
	  (expr2 (if negated2 (bdd-negate formula2) formula2)))
      (or
       (lookup-memo-for-and (bdd-id expr1) (bdd-id expr2))
       (let ((expr1-index (push-bdd-entry expr1))
             (expr2-index (push-bdd-entry expr2)))
         (let ((result
                (cond
                 ((= (if-test formula1) (if-test formula2))
                  (let ((left1 (bdd-unnegated (if-left formula1)))
                        (left2 (bdd-unnegated (if-left formula2)))
                        (neg1 (bdd-compute-sense (if-left formula1) negated1))
                        (neg2 (bdd-compute-sense (if-left formula2) negated2)))
                    ;; Note that a right branch is never a negation
                    (let ((right1-index (push-bdd-entry (if-right formula1)))
                          (right2-index (push-bdd-entry (if-right formula2)))
                          (left-index
                           (push-bdd-entry
                            (andop-aux left1 left2 neg1 neg2))))
                      (let ((right-result
                             (andop-aux (bdd-entry right1-index)
                                        (bdd-entry right2-index)
                                        negated1 negated2)))
                        (let ((left-result (bdd-entry left-index)))
                          (dotimes (i 3) (pop-bdd-entry))
                          (bdd-make-if
                           (if-test formula1)
                           left-result right-result))))))
                 ((< (if-test formula1) (if-test formula2))
                  (let ((left1 (bdd-unnegated (if-left formula1)))
                        (neg1 (bdd-compute-sense (if-left formula1) negated1)))
                    (let ((right1-index (push-bdd-entry (if-right formula1)))
                          (formula2-index (push-bdd-entry formula2))
                          (left-index
                           (push-bdd-entry
                            (andop-aux left1 formula2 neg1 negated2))))
                      (let ((right-result
                             (andop-aux (bdd-entry right1-index)
                                        (bdd-entry formula2-index)
                                        negated1 negated2)))
                        (let ((left-result (bdd-entry left-index)))
                          (dotimes (i 3) (pop-bdd-entry))
                          (bdd-make-if
                           (if-test formula1)
                           left-result right-result))))))
                 (t
                  (let ((left2 (bdd-unnegated (if-left formula2)))
                        (neg2 (bdd-compute-sense (if-left formula2) negated2)))
                    (let ((formula1-index (push-bdd-entry formula1))
                          (right2-index (push-bdd-entry (if-right formula2)))
                          (left-index
                           (push-bdd-entry
                            (andop-aux formula1 left2 negated1 neg2))))
                      (let ((right-result
                             (andop-aux (bdd-entry formula1-index)
                                        (bdd-entry right2-index)
                                        negated1 negated2)))
                        (let ((left-result (bdd-entry left-index)))
                          (dotimes (i 3) (pop-bdd-entry))
                          (bdd-make-if
                           (if-test formula2)
                           left-result right-result)))))))))
           (memoize-and (bdd-id (bdd-entry expr1-index))
                        (bdd-id (bdd-entry expr2-index))
                        result)
           (dotimes (i 2) (pop-bdd-entry))
           result)))))))

(defun andop (formula1 formula2)
  (andop-aux (bdd-unnegated formula1)
             (bdd-unnegated formula2)
             (bdd-negated-p formula1)
             (bdd-negated-p formula2)))

(defsubst orop (formula1 formula2)
  (bdd-negate (andop (bdd-negate formula1) (bdd-negate formula2))))




;;; ================ Interface =================


(defun reset-bdd ()
  (setq *atom-list* nil)
  (setq *atom-array* (vector))
  (setq *next-id* 2)
  (setq *number-of-atoms* 0)
  (setq *if-count* 0)
  (dotimes (i bdd-hash-table-size)
    (setf (aref *if-hash-table* i) nil)
    (setf (aref *recache-table* i) nil)
    (setf (aref *not-hash-table* i) nil)
    (setf (aref *sub0-hash-table* i) nil)
    (setf (aref *sub1-hash-table* i) nil)
    (setf (aref *and-hash-table* i) nil)))


(defvar *var-scores* (vector))

(defvar *initial-order* nil)

(defun compute-input-scores (circuit &optional (unit 1.0))
  (cond ((null circuit) nil)
        ((atom circuit)
         (incf (aref *var-scores* (- circuit 2)) unit))
        (t (let ((u (/ unit (length circuit))))
             (loop for c in circuit
                   do (compute-input-scores c u))))))

(defun remove-from-circuit (element circuit)
  (cond ((null circuit) nil)
        ((atom circuit)
         (cond ((= element circuit) nil)
               (t circuit)))
        (t (loop for c in circuit
                 for result = (remove-from-circuit element c)
                 unless (null result)
                 collect result))))

(defun construct-circuit-representation (formula)
  (cond ((or (and-p formula) (or-p formula))
         (loop for arg in (cdr formula)
               for result = (construct-circuit-representation arg)
               unless (null result)
               collect result))
        ((implies-p formula)
         (let ((left-result (construct-circuit-representation
                             (implies-left formula)))
               (right-result (construct-circuit-representation
                              (implies-right formula))))
           (cond ((null left-result) right-result)
                 ((null right-result) left-result)
                 (t (list left-result right-result)))))
        ((not-p formula)
         (construct-circuit-representation (not-expr formula)))
        ((if-p formula)
         (let ((left-result
                (cond ((and-p (if-left formula))
                       (construct-circuit-representation
                        (list* 'and (if-test formula)
                               (cdr (if-left formula)))))
                      (t (construct-circuit-representation
                          (make-and (if-test formula) (if-left formula))))))
               (right-result
                (cond ((and-p (if-right formula))
                       (construct-circuit-representation
                        (list* 'and (if-test formula)
                               (cdr (if-right formula)))))
                      (t (construct-circuit-representation
                          (make-and (if-test formula) (if-right formula)))))))
           (cond ((null left-result) right-result)
                 ((null right-result) left-result)
                 (t (list left-result right-result)))))
        ((not (or (true-p formula) (false-p formula)))
         (bdd-integrate-atomic formula))))


;;; The initial order here is essentially Minato's DWA.

(defun construct-initial-order (formula)
  (setq *initial-order* nil)
  (let ((circuit (construct-circuit-representation formula)))
    (setq *number-of-atoms* (length *atom-list*))
    (setq *atom-array* (make-array *number-of-atoms*
                                   :initial-contents (reverse *atom-list*)))
    (setq *var-scores* (make-array *number-of-atoms* :initial-element 0))
    (loop while (not (null circuit))
          do (progn (compute-input-scores circuit)
                    (let ((champ 0)
                          (champ-score (aref *var-scores* 0)))
                      (loop for i from 1 to (- *number-of-atoms* 1)
                            when (> (aref *var-scores* i) champ-score)
                            do (setq champ-score
                                     (aref *var-scores* (setq champ i))))
                      (push (aref *atom-array* champ) *initial-order*)
                      (setq circuit (remove-from-circuit (+ champ 2) circuit))
                      (loop for i from 0 to (- *number-of-atoms* 1)
                            do (setf (aref *var-scores* i) 0)))))
    (let ((result (reverse *initial-order*)))
      (setq *initial-order* nil)
      (setq *atom-list* nil)
      (setq *atom-array* (vector))
      (setq *var-scores* (vector))
      result)))


(defvar *input-order* nil)

(defun construct-input-order (formula)
  (let ((*input-order* nil))
    (construct-input-order-aux formula)
    (reverse *input-order*)))

(defun construct-input-order-aux (formula)
  (cond ((or (and-p formula) (or-p formula))
         (loop for arg in (cdr formula)
               do (construct-input-order-aux arg)))
        ((implies-p formula)
         (construct-input-order-aux (implies-left formula))
         (construct-input-order-aux (implies-right formula)))
        ((not-p formula)
         (construct-input-order-aux (not-expr formula)))
        ((if-p formula)
         (construct-input-order-aux (if-test formula))
         (construct-input-order-aux (if-left formula))
         (construct-input-order-aux (if-right formula)))
        ((not (or (true-p formula) (false-p formula)
                  (member-equal formula *input-order*)))
         (push formula *input-order*))))


;;; ============== Integrating formulas into the BDD ===============


(defun set-expression (formula)
  (bdd-integrate-atoms formula)
  (setq *number-of-atoms* (length *atom-list*))
  (setq *atom-array* (make-array *number-of-atoms*
				 :initial-contents (reverse *atom-list*)))
  (setq *next-id* (+ *number-of-atoms* 2))
  ;; By now, all atoms have been integrated.
  (bdd-integrate-formula formula))


(defun set-expression-with-reorder (formula)
  (let ((initial-bdd-index (push-bdd-entry (set-expression formula))))
    (bdd-clear-and-recache)
    (let ((list-of-literals nil)
	  (initial-bdd (bdd-entry initial-bdd-index)))
      (pop-bdd-entry)
      (dolist (var (bdd-choose-order initial-bdd))
        (push (aref *atom-array* (- var 2)) list-of-literals))
      (reset-bdd)
      (dolist (l list-of-literals)
        (bdd-integrate-atomic l))
      (set-expression formula))))

         
;;; We assume that all atoms have been integrated when this is called.

(defun bdd-integrate-formula (formula)
  (cond ((true-p formula) *bdd-one*)
	((false-p formula) *bdd-zero*)
	((if-p formula)
         (let ((test-index
                (push-bdd-entry (bdd-integrate-formula (if-test formula))))
               (left-index
                (push-bdd-entry (bdd-integrate-formula (if-left formula))))
               (right-index
                (push-bdd-entry (bdd-integrate-formula (if-right formula)))))
           (let ((first-index
                  (push-bdd-entry
                   (bdd-negate
                    (andop (bdd-entry test-index) (bdd-entry left-index)))))
                 (second-result
                  (bdd-negate
                   (andop (bdd-negate (bdd-entry test-index))
                          (bdd-entry right-index)))))
             (let ((first-result (bdd-entry first-index)))
               (dotimes (i 4) (pop-bdd-entry))
               (bdd-negate (andop first-result second-result))))))
	((not-p formula)
	 (bdd-negate (bdd-integrate-formula (second formula))))
	((and-p formula)
         (let ((first-index
                (push-bdd-entry
                 (bdd-integrate-formula (second formula))))
               (second-result (bdd-integrate-formula (third formula))))
           (let ((first-result (bdd-entry first-index)))
             (pop-bdd-entry)
             (andop first-result second-result))))
	((or-p formula)
         (let ((first-index
                (push-bdd-entry
                 (bdd-integrate-formula (second formula))))
               (second-result (bdd-integrate-formula (third formula))))
           (let ((first-result (bdd-entry first-index)))
             (pop-bdd-entry)
             (orop first-result second-result))))
	((implies-p formula)
         (let ((first-index
                (push-bdd-entry
                 (bdd-integrate-formula (second formula))))
               (second-result (bdd-integrate-formula (third formula))))
           (let ((first-result (bdd-entry first-index)))
             (pop-bdd-entry)
             (bdd-negate
              (andop first-result (bdd-negate second-result))))))
	(t
         ;; Atoms have been integrated, so bdd-integrate-atomic will
         ;; not have any side effects.
         (bdd-make-if (bdd-integrate-atomic formula)
                      *bdd-one*
                      *bdd-zero*))))


(defun bdd-integrate-atomic (formula)
  (let ((tail (member-equal formula *atom-list*)))
    (cond (tail (+ (length tail) 1))
          (t (push formula *atom-list*)
             (+ (length *atom-list*) 1)))))

(defun bool-connective-p (formula)
  (or (and-p formula)
      (or-p formula)
      (implies-p formula)))

(defun bdd-integrate-atoms (formula)
  (cond ((or (true-p formula) (false-p formula)) nil)
	((if-p formula)
	 (bdd-integrate-atoms (if-test formula))
	 (bdd-integrate-atoms (if-left formula))
	 (bdd-integrate-atoms (if-right formula)))
	((not-p formula)
	 (bdd-integrate-atoms (second formula)))
	((bool-connective-p formula)
	 (bdd-integrate-atoms (second formula))
	 (bdd-integrate-atoms (third formula)))
	(t (bdd-integrate-atomic formula))))


;;; Some more BDD operations


(defun bdd-subfunction0 (var formula)
  (cond
   ((or (eq formula *bdd-zero*) (eq formula *bdd-one*))
    formula)
   ((bdd-negated-p formula)
    (bdd-negate (bdd-subfunction0 var (second formula))))
   (t (or (lookup-memo-for-sub0 var formula)
          (let* ((formula-index (push-bdd-entry formula))
		 (result
		  (cond
		   ((= (if-test formula) var) (if-right formula))
		   ((< (if-test formula) var)
		    (bdd-make-if (if-test formula)
				 (bdd-subfunction0 var (if-left formula))
				 (bdd-subfunction0
				  var (if-right (bdd-entry formula-index)))))
		   (t formula))))
            (memoize-sub0 var (bdd-entry formula-index) result)
	    (pop-bdd-entry)
            result)))))

(defun bdd-subfunction1 (var formula)
  (cond
   ((or (eq formula *bdd-zero*) (eq formula *bdd-one*))
    formula)
   ((bdd-negated-p formula)
    (bdd-negate (bdd-subfunction1 var (second formula))))
   (t (or (lookup-memo-for-sub1 var formula)
          (let* ((formula-index (push-bdd-entry formula))
		 (result
		  (cond
		   ((= (if-test formula) var) (if-left formula))
		   ((< (if-test formula) var)
		    (bdd-make-if (if-test formula)
				 (bdd-subfunction1 var (if-left formula))
				 (bdd-subfunction1
				  var (if-right (bdd-entry formula-index)))))
		   (t formula))))
            (memoize-sub1 var (bdd-entry formula-index) result)
	    (pop-bdd-entry)
            result)))))

(defsubst bdd-var (formula)
  (cond ((or (eq formula *bdd-zero*) (eq formula *bdd-one*)) 1000000)
        ((bdd-negated-p formula) (if-test (second formula)))
        (t (if-test formula))))

(defun bdd-compute-subfunctions (var set-indices)
  (let ((result-indices nil))
    (dolist (s-index set-indices)
      (let ((sub0 (bdd-unnegated (bdd-subfunction0 var (bdd-entry s-index)))))
	(unless (loop for r-index in result-indices
		      when (eq sub0 (bdd-entry r-index))
		      return t)
	  (push (push-bdd-entry sub0) result-indices)))
      (let ((sub1 (bdd-unnegated (bdd-subfunction1 var (bdd-entry s-index)))))
	(unless (loop for r-index in result-indices
		      when (eq sub1 (bdd-entry r-index))
		      return t)
	  (push (push-bdd-entry sub1) result-indices))))
    (let ((result (loop for r-index in result-indices
			collect (bdd-entry r-index))))
      (dotimes (i (length result-indices)) (pop-bdd-entry))
      result)))

(defun bdd-choose-order-aux (set-indices result)
  (let ((minvar (bdd-var (bdd-entry (car set-indices)))))
    (dolist (s-index set-indices)
      (when (< (bdd-var (bdd-entry s-index)) minvar)
	(setq minvar (bdd-var (bdd-entry s-index)))))
    (cond ((> minvar *number-of-atoms*)
	   (dotimes (i (length set-indices)) (pop-bdd-entry))
	   result)
          (t (let ((champ-indices
		    (loop for c in (bdd-compute-subfunctions
				    minvar set-indices)
			  collect (push-bdd-entry c)))
                   (champvar minvar))
               (loop for var from 2 to (+ *number-of-atoms* 1)
                     do (unless (or (eq var champvar)
				    (member-eq var result))
                          (let ((chal (bdd-compute-subfunctions
				       var set-indices)))
                            (when (< (length chal) (length champ-indices))
			      (dotimes (i (length champ-indices))
				(pop-bdd-entry))
                              (setq champ-indices
				    (loop for c in chal
					  collect (push-bdd-entry c)))
                              (setq champvar var)))))
	       (let ((champ (loop for c-index in champ-indices
				  collect (bdd-entry c-index))))
		 (dotimes (i (length champ)) (pop-bdd-entry))
		 (dotimes (i (length set-indices)) (pop-bdd-entry))
		 (setq champ-indices
		       (loop for c in champ
			     collect (push-bdd-entry c)))
		 (bdd-choose-order-aux
		  champ-indices (cons champvar result))))))))

(defun bdd-choose-order (formula)
  (unless (or (eq formula *bdd-zero*) (eq formula *bdd-one*))
    (let* ((var (bdd-var formula))
	   (formula-index (push-bdd-entry formula))
	   (subfunctions (bdd-compute-subfunctions var (list formula-index))))
      (pop-bdd-entry)
      (let ((subfunction-indices
	     (loop for s in subfunctions
		   collect (push-bdd-entry s))))
	(bdd-choose-order-aux subfunction-indices (list var))))))




;;; ================= ZBDD ==================



(defconstant zbdd-hash-table-size 65536)
(defconstant zbdd-hash-table-mask (1- zbdd-hash-table-size))

(defvar *zbdd-next-id* 0)

(defvar *zbdd-hash-table* (make-array zbdd-hash-table-size
                                    :initial-element nil))

(defun zbdd-make-if (test left right)
  (cond ((equal left 0) right)
	(t
	 (let ((test-id (bdd-id test))
	       (left-id (bdd-id left))
	       (right-id (bdd-id right)))
	   (let ((index (fixnum-op logand
			 (fixnum-op +
			   (fixnum-op * test-id hash-multiplier)
			   (fixnum-op +
			     (fixnum-op * left-id second-hash-multiplier)
			     right-id))
			 zbdd-hash-table-mask)))
	     (or (loop for x in (unsafe-aref *zbdd-hash-table* index)
		       when (let ((u (car x)))
			      (and (fixnum-rel = (first u) test-id)
				   (fixnum-rel = (second u) left-id)
				   (fixnum-rel = (third u) right-id)))
		       return (cdr x))
		 (let ((result (list *zbdd-next-id* test left right)))
		   (setq *zbdd-next-id* (fixnum-op + *zbdd-next-id* 1))
		   (setf (unsafe-aref *zbdd-hash-table* index)
			 (cons (cons (list test-id left-id right-id) result)
			       (unsafe-aref *zbdd-hash-table* index)))
		   result)))))))

;;; Returns subset of formula such that var = 1

(defun zbdd-subset1 (formula var)
  (cond ((< var (bdd-top formula)) 0)
        ((= var (bdd-top formula)) (if-left formula))
        (t (zbdd-make-if (if-test formula)
                         (zbdd-subset1 (if-left formula) var)
                         (zbdd-subset1 (if-right formula) var)))))

;;; Returns subset of formula such that var = 0

(defun zbdd-subset0 (formula var)
  (cond ((< var (bdd-top formula)) formula)
        ((= var (bdd-top formula)) (if-right formula))
        (t (zbdd-make-if (if-test formula)
                         (zbdd-subset0 (if-left formula) var)
                         (zbdd-subset0 (if-right formula) var)))))

;;; Returns formula with var inverted

(defun zbdd-change (formula var)
  (cond ((or (atom formula) (< var (bdd-top formula)))
	 (zbdd-make-if var formula 0))
        ((= var (bdd-top formula))
         (zbdd-make-if var (if-right formula) (if-left formula)))
        (t (zbdd-make-if (if-test formula)
                         (zbdd-change (if-left formula) var)
                         (zbdd-change (if-right formula) var)))))

;;; Union

(defun zbdd-union (formula1 formula2)
  (cond ((equal formula1 0) formula2)
        ((equal formula2 0) formula1)
        ((equal formula1 formula2) formula1)
        ((< (bdd-top formula1) (bdd-top formula2))
         (zbdd-make-if (if-test formula1)
                       (if-left formula1)
                       (zbdd-union (if-right formula1) formula2)))
        ((= (bdd-top formula1) (bdd-top formula2))
         (zbdd-make-if (if-test formula1)
                       (zbdd-union (if-left formula1) (if-left formula2))
                       (zbdd-union (if-right formula1) (if-right formula2))))
        (t
         (zbdd-make-if (if-test formula2)
                       (if-left formula2)
                       (zbdd-union formula1 (if-right formula2))))))


;;; Intersection

(defun zbdd-inter (formula1 formula2)
  (cond ((equal formula1 0) 0)
        ((equal formula2 0) 0)
        ((equal formula1 formula2) formula1)
        ((< (bdd-top formula1) (bdd-top formula2))
         (zbdd-inter (if-right formula1) formula2))
        ((= (bdd-top formula1) (bdd-top formula2))
         (zbdd-make-if (if-test formula1)
                       (zbdd-inter (if-left formula1) (if-left formula2))
                       (zbdd-inter (if-right formula1) (if-right formula2))))
        (t
         (zbdd-inter formula1 (if-right formula2)))))

;;; Difference

(defun zbdd-diff (formula1 formula2)
  (cond ((equal formula1 0) 0)
        ((equal formula2 0) formula1)
        ((equal formula1 formula2) 0)
        ((< (bdd-top formula1) (bdd-top formula2))
         (zbdd-make-if (if-test formula1)
                       (if-left formula1)
                       (zbdd-diff (if-right formula1) formula2)))
        ((= (bdd-top formula1) (bdd-top formula2))
         (zbdd-make-if (if-test formula1)
                       (zbdd-diff (if-left formula1) (if-left formula2))
                       (zbdd-diff (if-right formula1) (if-right formula2))))
        (t (zbdd-diff formula1 (if-right formula2)))))

(defun reset-zbdd ()
  (setq *zbdd-next-id* 0)
  (dotimes (i zbdd-hash-table-size)
    (setf (aref *zbdd-hash-table* i) nil)))

(defsubst zbdd-atom (atom)
  (- (* 2 atom) 2))

(defun zbdd-complement-atom (atom)
  (- (* 2 atom) 1))

(defun zbdd-complemented-p (atom)
  (= (mod atom 2) 1))

(defun zbdd-print-atom (atom)
  (let ((atomic-formula (aref *atom-array* (floor (- atom 2) 2))))
    (if (zbdd-complemented-p atom)
	(make-not atomic-formula)
      atomic-formula)))
  

;;; ================ New ISOP using ZBDDs ===================

;;; Uses Minato-Morreale algorithm.

(defvar *isop-hash-table* (make-array zbdd-hash-table-size
                                      :initial-element nil))

(defun reset-new-isop ()
  (setq *zbdd-next-id* 0)
  (dotimes (i zbdd-hash-table-size)
    (setf (aref *zbdd-hash-table* i) nil)
    (setf (aref *isop-hash-table* i) nil)))

(defun setup-new-isop ()
  (setq *zbdd-next-id* (+ (* 2 *number-of-atoms*) 2)))

(defun memoize-isop (floor-id ceiling-id result)
  (let ((index (fixnum-op logand
                          (fixnum-op +
                                     (fixnum-op * hash-multiplier floor-id)
                                     ceiling-id)
                          zbdd-hash-table-mask)))
    (setf (unsafe-aref *isop-hash-table* index)
          (cons (cons (cons floor-id ceiling-id) result)
                (unsafe-aref *isop-hash-table* index)))))

(defun lookup-memo-for-isop (floor ceiling)
  (let ((floor-id (bdd-id floor))
        (ceiling-id (bdd-id ceiling)))
    (loop for x in 
          (unsafe-aref *isop-hash-table*
		(fixnum-op logand
			   (fixnum-op + (fixnum-op * hash-multiplier floor-id)
				      ceiling-id)
			   zbdd-hash-table-mask))
	  when (and (fixnum-rel = floor-id (caar x))
		    (fixnum-rel = ceiling-id (cdar x)))
	  return (cdr x))))

(defun new-isop (flr ceil)
  (cond
   ((eq flr *bdd-zero*) (list *bdd-zero* 0))
   ((eq ceil *bdd-one*) (list *bdd-one* 1))
   (t (or (lookup-memo-for-isop flr ceil)
          (let ((flr-expr (if (bdd-negated-p flr) (second flr) flr))
                (neg-flr (if (bdd-negated-p flr) t nil))
                (ceil-expr (if (bdd-negated-p ceil) (second ceil) ceil))
                (neg-ceil (if (bdd-negated-p ceil) t nil))
                (flr-index (push-bdd-entry flr))
                (ceil-index (push-bdd-entry ceil)))
            (let ((result
                   (cond
                    ((= (if-test flr-expr) (if-test ceil-expr))
                     (new-isop-aux (if-test flr-expr)
                                   (if neg-flr
                                       (bdd-negate (if-left flr-expr))
                                     (if-left flr-expr))
                                   (if neg-ceil
                                       (bdd-negate (if-left ceil-expr))
                                     (if-left ceil-expr))
                                   (if neg-flr
                                       (bdd-negate (if-right flr-expr))
                                     (if-right flr-expr))
                                   (if neg-ceil
                                       (bdd-negate (if-right ceil-expr))
                                     (if-right ceil-expr))))
                    ((< (if-test flr-expr) (if-test ceil-expr))
                     (new-isop-aux (if-test flr-expr)
                                   (if neg-flr
                                       (bdd-negate (if-left flr-expr))
                                     (if-left flr-expr))
                                   ceil
                                   (if neg-flr
                                       (bdd-negate (if-right flr-expr))
                                     (if-right flr-expr))
                                   ceil))
                    (t (new-isop-aux (if-test ceil-expr)
                                     flr
                                     (if neg-ceil
                                         (bdd-negate (if-left ceil-expr))
                                       (if-left ceil-expr))
                                     flr
                                     (if neg-ceil
                                         (bdd-negate (if-right ceil-expr))
                                       (if-right ceil-expr)))))))
              (memoize-isop (bdd-id (bdd-entry flr-index))
                            (bdd-id (bdd-entry ceil-index))
                            result)
              (pop-bdd-entry)
              (pop-bdd-entry)
              result))))))

(defun new-isop-aux (test left-floor left-ceiling right-floor right-ceiling)
  (let ((left-floor-index (push-bdd-entry left-floor))
        (left-ceiling-index (push-bdd-entry left-ceiling))
        (right-floor-index (push-bdd-entry right-floor))
        (right-ceiling-index (push-bdd-entry right-ceiling))
        (first-index
         (push-bdd-entry (andop left-floor (bdd-negate right-ceiling)))))
    (let ((second-index
           (push-bdd-entry
            (andop (bdd-entry right-floor-index)
                   (bdd-negate (bdd-entry left-ceiling-index))))))
      (let* ((left (new-isop (bdd-entry first-index)
                             (bdd-entry left-ceiling-index)))
             (left-index (push-bdd-entry (first left)))
             (right (new-isop (bdd-entry second-index)
                              (bdd-entry right-ceiling-index)))
             (right-index (push-bdd-entry (first right))))
        (let ((leftdpflr-index
               (push-bdd-entry
                (andop (bdd-entry left-floor-index)
                       (bdd-negate (bdd-entry left-index)))))
              (rightdpflr
               (andop (bdd-entry right-floor-index)
                      (bdd-negate (bdd-entry right-index)))))
          (let ((leftdpflr (bdd-entry leftdpflr-index)))
            (pop-bdd-entry)
            (let ((floor-index
                   (push-bdd-entry
                    (orop (andop leftdpflr (bdd-entry right-ceiling-index))
                          (andop rightdpflr (bdd-entry left-ceiling-index)))))
                  (ceiling-index
                   (push-bdd-entry (andop (bdd-entry left-ceiling-index)
                                          (bdd-entry right-ceiling-index)))))
              (let* ((dontcare (new-isop (bdd-entry floor-index)
                                         (bdd-entry ceiling-index)))
                     (dontcare-index (push-bdd-entry (first dontcare)))
                     (res1-index
                      (push-bdd-entry
                       (andop (bdd-make-if test *bdd-one* *bdd-zero*)
                              (bdd-entry left-index))))
                     (res2
                      (andop (bdd-make-if test *bdd-zero* *bdd-one*)
                             (bdd-entry right-index)))
                     (result-bdd
                       (orop (orop (bdd-entry res1-index) res2)
                             (bdd-entry dontcare-index))))
                (dotimes (i 12) (pop-bdd-entry))
                (list result-bdd
                      (zbdd-union
                       (zbdd-union
                        (zbdd-change (second left) (zbdd-atom test))
                        (zbdd-change (second right)
                                     (zbdd-complement-atom test)))
                       (second dontcare)))))))))))

(defun new-ipos (flr ceil)
  (cond
   ((equal ceil *bdd-one*) (list *bdd-one* 0))
   ((equal flr *bdd-zero*) (list *bdd-zero* 1))
   (t (or (lookup-memo-for-isop flr ceil)
          (let ((flr-expr (if (bdd-negated-p flr) (second flr) flr))
                (neg-flr (if (bdd-negated-p flr) t nil))
                (ceil-expr (if (bdd-negated-p ceil) (second ceil) ceil))
                (neg-ceil (if (bdd-negated-p ceil) t nil))
                (flr-index (push-bdd-entry flr))
                (ceil-index (push-bdd-entry ceil)))
            (let ((result
                   (cond
                    ((= (if-test flr-expr) (if-test ceil-expr))
                     (new-ipos-aux (if-test flr-expr)
                                   (if neg-flr
                                       (bdd-negate (if-left flr-expr))
                                     (if-left flr-expr))
                                   (if neg-ceil
                                       (bdd-negate (if-left ceil-expr))
                                     (if-left ceil-expr))
                                   (if neg-flr
                                       (bdd-negate (if-right flr-expr))
                                     (if-right flr-expr))
                                   (if neg-ceil
                                       (bdd-negate (if-right ceil-expr))
                                     (if-right ceil-expr))))
                    ((< (if-test flr-expr) (if-test ceil-expr))
                     (new-ipos-aux (if-test flr-expr)
                                   (if neg-flr
                                       (bdd-negate (if-left flr-expr))
                                     (if-left flr-expr))
                                   ceil
                                   (if neg-flr
                                       (bdd-negate (if-right flr-expr))
                                     (if-right flr-expr))
                                   ceil))
                    (t (new-ipos-aux (if-test ceil-expr)
                                     flr
                                     (if neg-ceil
                                         (bdd-negate (if-left ceil-expr))
                                       (if-left ceil-expr))
                                     flr
                                     (if neg-ceil
                                         (bdd-negate (if-right ceil-expr))
                                       (if-right ceil-expr)))))))
              (memoize-isop (bdd-id (bdd-entry flr-index))
                            (bdd-id (bdd-entry ceil-index))
                            result)
              (pop-bdd-entry)
              (pop-bdd-entry)
              result))))))

(defun new-ipos-aux (test left-floor left-ceiling right-floor right-ceiling)
  (let ((left-floor-index (push-bdd-entry left-floor))
        (left-ceiling-index (push-bdd-entry left-ceiling))
        (right-floor-index (push-bdd-entry right-floor))
        (right-ceiling-index (push-bdd-entry right-ceiling))
        (first-index
         (push-bdd-entry (orop left-ceiling (bdd-negate right-floor)))))
    (let ((second-index
           (push-bdd-entry
            (orop (bdd-entry right-ceiling-index)
                  (bdd-negate (bdd-entry left-floor-index))))))
      (let* ((left (new-ipos (bdd-entry left-floor-index)
                             (bdd-entry first-index)))
             (left-index (push-bdd-entry (first left)))
             (right (new-ipos (bdd-entry right-floor-index)
                              (bdd-entry second-index)))
             (right-index (push-bdd-entry (first right))))
        (let ((leftdpceil-index
               (push-bdd-entry
                (orop (bdd-entry left-ceiling-index)
                      (bdd-negate (bdd-entry left-index)))))
              (rightdpceil
               (orop (bdd-entry right-ceiling-index)
                     (bdd-negate (bdd-entry right-index)))))
          (let ((leftdpceil (bdd-entry leftdpceil-index)))
            (pop-bdd-entry)
            (let ((floor-index
                   (push-bdd-entry (orop (bdd-entry left-floor-index)
                                         (bdd-entry right-floor-index))))
                  (ceiling-index
                   (push-bdd-entry
                    (andop (orop leftdpceil (bdd-entry right-floor-index))
                           (orop rightdpceil (bdd-entry left-floor-index))))))
              (let* ((dontcare (new-ipos (bdd-entry floor-index)
                                         (bdd-entry ceiling-index)))
                     (dontcare-index (push-bdd-entry (first dontcare)))
                     (res1-index
                      (push-bdd-entry
                       (orop (bdd-make-if test *bdd-one* *bdd-zero*)
                             (bdd-entry right-index))))
                     (res2
                      (orop (bdd-make-if test *bdd-zero* *bdd-one*)
                            (bdd-entry left-index)))
                     (result-bdd
                      (andop (andop (bdd-entry res1-index) res2)
                             (bdd-entry dontcare-index))))
                (dotimes (i 12) (pop-bdd-entry))
                (list result-bdd
                      (zbdd-union
                       (zbdd-change (second right) (zbdd-atom test))
                       (zbdd-union (zbdd-change (second left)
                                                (zbdd-complement-atom test))
                                   (second dontcare))))))))))))

(defvar *zbdd-cube-set* nil)

(defun zbdd-to-cube-set (zbdd)
  (setq *zbdd-cube-set* nil)
  (zbdd-to-cube-set-aux zbdd nil)
  *zbdd-cube-set*)

(defun zbdd-to-cube-set-aux (zbdd path)
  (cond ((equal zbdd 1) (push path *zbdd-cube-set*))
        ((equal zbdd 0))
        (t (zbdd-to-cube-set-aux (if-left zbdd) (cons (if-test zbdd) path))
           (zbdd-to-cube-set-aux (if-right zbdd) path))))

(defun prop-weight (formula order)
  (cond ((not-p formula)
         (length (member-equal (not-expr formula) order)))
        (t (length (member-equal formula order)))))

(defun insert-into-collection (pair collection)
  (cond ((or (null collection) (> (car pair) (caar collection)))
         (cons pair collection))
        (t (cons (car collection)
                 (insert-into-collection pair (cdr collection))))))

(defun prop-rearrange (formula order)
  (cond ((and-p formula)
         (let ((collected nil))
           (loop for expr in (cdr formula)
                 do (let ((r (prop-rearrange expr order)))
                      (setq collected
                            (insert-into-collection
                             (cons (prop-weight r order) r)
                             collected))))
           (cons 'and (loop for r in collected
                            collect (cdr r)))))
        ((or-p formula)
         (let ((collected nil))
           (loop for expr in (cdr formula)
                 do (let ((r (prop-rearrange expr order)))
                      (setq collected
                            (insert-into-collection
                             (cons (prop-weight r order) r)
                             collected))))
           (cons 'or (loop for r in collected
                            collect (cdr r)))))
        ((not-p formula)
         (make-not (prop-rearrange (not-expr formula) order)))
        ((implies-p formula)
         (make-implies (prop-rearrange (implies-left formula) order)
                       (prop-rearrange (implies-right formula) order)))
        ((if-p formula)
         (make-if (prop-rearrange (if-test formula) order)
                  (prop-rearrange (if-left formula) order)
                  (prop-rearrange (if-right formula) order)))
        (t formula)))



;;; ============ Top level functions for DNF and CNF ===============


(defun dnf (formula)
  (let* ((initial-order (construct-initial-order formula))
         (input-order (construct-input-order formula))
         (rearranged (prop-rearrange formula initial-order)))
    (loop for atom in initial-order
          do (bdd-integrate-atomic atom))
    (let ((internal-formula
           (set-expression
            (without-proof-logging (expand-proposition rearranged nil)))))
      (let ((internal-formula-index (push-bdd-entry internal-formula)))
        (bdd-clear-and-recache)
        (setq internal-formula (bdd-entry internal-formula-index))
        (pop-bdd-entry)
        (setup-new-isop)
        (let* ((result (new-isop internal-formula internal-formula))
               (cube-set (zbdd-to-cube-set (second result)))
               (result-formula
                (cond ((null cube-set) *false*)
                      ((= (length cube-set) 1) (dnf-aux (first cube-set)))
                      (t (let ((result nil))
                           (loop for disjunct in cube-set
                                 do (push (dnf-aux disjunct) result))
                           (cons 'or result))))))
          (reset-new-isop)
          (reset-bdd)
          (prop-rearrange result-formula input-order))))))

(defun dnf-aux (result)
  (cond ((null result) *true*)
	((= (length result) 1)
	 (zbdd-print-atom (first result)))
	(t (let ((res nil))
	     (loop for conjunct in result
		   do (push (zbdd-print-atom conjunct) res))
	     (cons 'and res)))))


(defun cnf (formula)
  (let* ((initial-order (construct-initial-order formula))
         (input-order (construct-input-order formula))
         (rearranged (prop-rearrange formula initial-order)))
    (loop for atom in initial-order
          do (bdd-integrate-atomic atom))
    (let ((internal-formula
           (set-expression
            (without-proof-logging (expand-proposition rearranged nil)))))
      (let ((internal-formula-index (push-bdd-entry internal-formula)))
        (bdd-clear-and-recache)
        (setq internal-formula (bdd-entry internal-formula-index))
        (pop-bdd-entry)
        (setup-new-isop)
        (let* ((result (new-ipos internal-formula internal-formula))
               (cube-set (zbdd-to-cube-set (second result)))
               (result-formula
                (cond ((null cube-set) *true*)
                      ((= (length cube-set) 1) (cnf-aux (first cube-set)))
                      (t (let ((result nil))
                           (loop for disjunct in cube-set
                                 do (push (cnf-aux disjunct) result))
                           (cons 'and result))))))
          (reset-new-isop)
          (reset-bdd)
          (prop-rearrange result-formula input-order))))))

(defun cnf-aux (result)
  (cond ((null result) *false*)
	((= (length result) 1)
	 (zbdd-print-atom (first result)))
	(t (let ((res nil))
	     (loop for disjunct in result
		   do (push (zbdd-print-atom disjunct) res))
	     (cons 'or res)))))
