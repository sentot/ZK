
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


;;; =====================================================================
;;; Various "utility" functions. They can be viewed as primitive
;;; functions that can be used by different "modules".
;;; =====================================================================

(in-package "ZK")


;;;
;;; Generally the functions and macros are low level routines that are
;;; used throughout the system. They do not depend on specific
;;; structures for various parts of the system.
;;; ---------------------------------------------------------------------------


;;; ----- Functions on trees

;;; Function to flatten a tree into a list.

(defun flatten (expr)
  (cond ((atom expr) (and expr (list expr)))
        (t (mapcan #'flatten expr))))

;;; Function to produce a list of symbols appearing in a tree.
;;; A symbol may appear more than once in the resulting list.
;;; The function unique, below, can be used to produce a a list
;;; with no repeated symbols.

(defun list-of-symbols (expr)
  (cond ((atom expr) (and (symbolp expr) (list expr)))
        (t (mapcan #'list-of-symbols expr))))

;;; Function to check if expr occurs anywhere in a tree.
;;; Returns non-nil if expr occurs in the tree.

(defun membertree (expr tree)
  (cond ((equal expr tree))
        ((atom tree) nil)
        ((or (membertree expr (car tree)) (membertree expr (cdr tree))))))


;;; ----- Functions on lists

;;; Function which returns length of list if proper list and nil otherwise.

(defun proper-length (list)
  (and (listp list)
       (handler-case (length list) (error () nil))))

;;; Function to remove all of the duplicate elements of a list.
;;; Order is preserved based on first occurrence.

(defun unique (list)
  (loop with (result)
        for elm in list
        unless (member-equal elm result) do (push elm result)
        finally (return (nreverse result))))

;;; Function to produce all the duplicate elements of a list.

(defun duplicates (list)
  (loop for rest on list
        when (member-equal (car rest) (cdr rest)) collect (car rest)))

;;; An efficient version of sublis which can be used if the alist keys are all
;;; symbols.

(defun sublis-symbol (alist form)
  (dolist (elt alist)
    (setf (get (car elt) :unique-symbol) (cdr elt)))
  (prog1
      (sublis-symbol-aux form)
    (dolist (elt alist)
      (remprop (car elt) :unique-symbol))))

(defun sublis-symbol-aux (form)
  (cond
   ((null form)
    nil)
   ((symbolp form)
    (or (get form :unique-symbol) form))
   ((atom form)
    form)
   (t
    (cons (sublis-symbol-aux (car form))
          (sublis-symbol-aux (cdr form))))))

;;; An efficient version of unique which can be used on lists of symbols.

(defun unique-symbol (list)
  (let ((result
         (loop for sym in list
             unless (get sym :unique-symbol)
             do (setf (get sym :unique-symbol) t)
             and collect sym)))
    (loop for sym in result
        do (remprop sym :unique-symbol))
    result))


;;; ----- Functions on lists as sets

;;; Function to check the subset relationship. Returns non-nil iff list-1
;;; is a subset of list-2.

(defun subset-p (list-1 list-2)
  (null (set-difference-equal list-1 list-2)))

;;; Function to check for the occurrence of a symbol in an expression.
;;; Note that this does not restrict the occurrence to free occurrences.

(defun occurs-in (var expr)
  (cond ((atom expr) (eq var expr))
        (t (some #'(lambda (u) (occurs-in var u)) expr))))

;;; A version for checking the occurrence of an expression rather
;;; than simply a symbol.

(defun expr-occurs (expression formula)
  (cond ((equal expression formula) t)
        ((atom formula) nil)
        (t (some #'(lambda (u) (expr-occurs expression u)) formula))))

;;; Count the number of occurences of expression within formula.

(defun count-expr-occurs (expression formula)
  (cond ((equal expression formula) 1)
        ((atom formula) 0)
        (t (loop for form in formula
                 sum (count-expr-occurs expression form)))))

;;; Count the number of atoms in a formula.

(defun size-of (formula)
  (length (flatten formula)))

;;; ----- Lists as stacks

;;; Macros for FIFO operations.

(defmacro push-fifo (element fifo)
  `(cond ((null ,fifo)
	  (push ,element ,fifo)
	  (setq ,fifo (cons ,fifo ,fifo)))
	 (t (setf (cdr (cdr ,fifo)) (cons ,element nil))
	    (setf (cdr ,fifo) (cdr (cdr ,fifo))))))

(defmacro pop-fifo (fifo)
  `(cond ((null ,fifo) nil)
	 ((null (cdr (car ,fifo)))
	  (prog1 (car (car ,fifo))
		 (setq ,fifo nil)))
	 (t (pop (car ,fifo)))))

;;; Code to convert decoded time to a string for printing.
;;; The day-of-week, savings-time and time-zone are ignored.

(defparameter *table-of-months*
	      (make-array '(12)
			  :initial-contents
			  '("January" "February" "March" "April"
			    "May" "June" "July" "August"
			    "September" "October" "November" "December")))

(defun get-decoded-date ()
  (multiple-value-bind (sec min hr dat mon yr day sav zone)
      (get-decoded-time)
    day sav zone
    (format nil "~D:~2,'0D:~2,'0D, ~D ~A, ~D"
	    hr min sec dat (aref *table-of-months* (1- mon)) yr)))
