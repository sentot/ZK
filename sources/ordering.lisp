
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


;;; The ordering defined here is similar to RRL's lrpo with the
;;; status of all function symbols being lr (left to right).


;;; Function to find out whether exp1 is greater in the ordering than
;;; exp2.  Vars is the list of variables that may be instantiated.
(defun lrpo> (exp1 exp2 vars)
  (cond ((atom exp1)
	 ;; exp1 is atom, very restricted condition for exp1
	 ;; to be greater than exp2.
	 (and (not (member-eq exp1 vars))
	      (atom exp2)
	      (not (member-eq exp2 vars))
	      (alphalessp exp2 exp1)))
	((atom exp2)
	 (if (member-eq exp2 vars)
	     (occurs-in exp2 exp1)
	     t))
	((eq (car exp1) (car exp2))
	 (lrpo>-aux exp1 exp2 vars))
	((greater-operator (car exp1) (car exp2))
	 (loop for u in (cdr exp2)
	       always (lrpo> exp1 u vars)))
	((loop for u in (cdr exp1)
	       thereis (or (equal u exp2) (lrpo> u exp2 vars)))
	 t)))

;;; Same operator, compare arguments.
(defun lrpo>-aux (exp1 exp2 vars)
  (do ((args1 (cdr exp1) (cdr args1))
       (args2 (cdr exp2) (cdr args2)))
      ((null args1) nil)
    (unless (equal (car args1) (car args2))
      (if (lrpo> (car args1) (car args2) vars)
	  (return (loop for u in (cdr args2)
			always (lrpo> exp1 u vars)))
	  (return (loop for u in (cdr args1)
			thereis (or (equal u exp2)
				    (lrpo> u exp2 vars))))))))

;;; Earlier defined operator is preferred.
(defun greater-operator (op1 op2)
  (and (get-event op1)
       (get-event op2)
       (> (event-number (get-event op1))
	  (event-number (get-event op2)))))
