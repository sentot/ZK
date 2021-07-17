
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


;;; ===== Code to handle ASSUMEs in the deductive database.

;;; Main features:
;;; - Lazy interface.
;;; - Production of chain rules for backchaining.
;;; Because dynamic caching is tied to assumes and their retractions,
;;; the caching mechanism is included here.


;;; Globals

(proclaim '(special *reduce-statistics* *true-node* *false-node*
		    *simplifier-instantiates-variables-flag*))

;;; ==================== Non-Lazy Assumes ====================

;;; Non-lazy routines to assume or deny a formula.

;;; To assume, we merge the e-graph representation of the formula
;;; with the e-graph representation (e-node) of *true*.  This may
;;; cause new facts to be deduced which are then propagated to the
;;; rest of the e-graph and tableau.  If the formula is quantified,
;;; then chain rules may be produced which are used during lookups.

(defun assume-in-egraph (formula)
  (unless *inconsistent*
    (incf (stat-assume *reduce-statistics*))
    (cond ((or (all-p formula) (some-p formula))
           (let ((node (intern-quantification formula)))
             (unless *inconsistent*
               (merge-nodes node *true-node* 'context)))
           (when (and *simplifier-instantiates-variables-flag*
                      (all-p formula)
                      (assume-produces-chain-rules-p formula))
             (produce-chain-rules-from-assume formula)))
	  (t (assume-expression formula)))))

;;; To deny, we forbid the merge instead.

(defun deny-in-egraph (formula)
  (unless *inconsistent*
    (incf (stat-deny *reduce-statistics*))
    (cond ((or (all-p formula) (some-p formula))
           (let ((node (intern-quantification formula)))
             (unless *inconsistent*
               (forbid-the-merge node *true-node* `(context ,node))))
           (when (and *simplifier-instantiates-variables-flag*
                      (some-p formula)
                      (deny-produces-chain-rules-p formula))
             (produce-chain-rules-from-deny formula)))
	  (t (deny-expression formula)))))

;;; After merging node with *true-node*, see if expression is
;;; a "conjunction".  If so, recursively assume/deny the conjuncts.

(defun assume-expression (expression)
  (let ((node (intern-expression expression)))
    (unless *inconsistent* (merge-nodes node *true-node* 'context))
    (when (and (not *inconsistent*)
               (if-p expression))
      (cond ((false-p (if-right expression))
             (assume-expression-aux (if-test expression) node 'regular)
             (unless *inconsistent*
               (assume-expression-aux (if-left expression) node 'regular)))
            ((false-p (if-left expression))
             (deny-expression-aux (if-test expression) node 'test)
             (unless *inconsistent*
               (assume-expression-aux (if-right expression) node 'right)))))))

(defun assume-expression-aux (expression if-node kind)
  (let ((node (intern-expression expression)))
    (unless *inconsistent*
      (merge-nodes node *true-node* `(assume-if ,if-node ,kind)))
    (when (and (not *inconsistent*)
               (if-p expression))
      (cond ((false-p (if-right expression))
             (assume-expression-aux (if-test expression) node 'regular)
             (unless *inconsistent*
               (assume-expression-aux (if-left expression) node 'regular)))
            ((false-p (if-left expression))
             (deny-expression-aux (if-test expression) node 'test)
             (unless *inconsistent*
               (assume-expression-aux (if-right expression) node 'right)))))))

;;; deny-expression is the counterpart of assume-expression.

;;; After forbidding the merge of node with *true-node*, see if
;;; expression is a "disjunction".  If so, recursively assume/deny
;;; the disjuncts.

(defun deny-expression (expression)
  (let ((node (intern-expression expression)))
    (unless *inconsistent*
      (forbid-the-merge node *true-node* `(context ,node)))
    (when (and (not *inconsistent*)
               (if-p expression))
      (cond ((true-p (if-left expression))
             (deny-expression-aux (if-test expression) node 'regular)
             (unless *inconsistent*
               (deny-expression-aux (if-right expression) node 'regular)))
            ((true-p (if-right expression))
             (assume-expression-aux (if-test expression) node 'test)
             (unless *inconsistent*
               (deny-expression-aux (if-left expression) node 'left)))))))

(defun deny-expression-aux (expression if-node kind)
  (let ((node (intern-expression expression)))
    (unless *inconsistent*
      (forbid-the-merge node *true-node* `(deny-if ,if-node ,kind)))
    (when (and (not *inconsistent*)
               (if-p expression))
      (cond ((true-p (if-left expression))
             (deny-expression-aux (if-test expression) node 'regular)
             (unless *inconsistent*
               (deny-expression-aux (if-right expression) node 'regular)))
            ((true-p (if-right expression))
             (assume-expression-aux (if-test expression) node 'test)
             (unless *inconsistent*
               (deny-expression-aux (if-left expression) node 'left)))))))

;;; ==================== End of Non-Lazy Assumes ====================



;;; ==================== Production of Chain Rules ====================


;;; Chain rules are mini resolution rules.

;;; Each chain rule entry consists of a triple (vars newvars expr)
;;; and a path.
;;;
;;; vars - original vars quantified
;;; newvars - renaming of vars
;;; expr - current subexpression
;;; path is a list with an integer between 0 and 5 inclusive:
;;;   0 - entire subexpression
;;;   1 - test part of subexpression
;;;   2 - left part of subexpression
;;;   3 - right part of subexpression
;;;   4 - left part of subexpression, assuming test part
;;;   5 - right part of subexpression, denying test part
;;;
;;; The chain-rules slot of an e-node is an array of two elements:
;;; (aref (e-node-chain-rules e-node) 0) stores chain rules that
;;; make an instance of (e-node-atrribute e-node) (TRUE),
;;; (aref (e-node-chain-rules e-node) 1) stores chain rules that
;;; make an instance of (e-node-atrribute e-node) not equals (TRUE).

;;; Test to determine if an ASSUME can produce chain rules.

(defun assume-produces-chain-rules-p (formula)
  (cond ((all-p formula)
         (assume-produces-chain-rules-p (all-expr formula)))
        ((not (contains-quantifier formula)) t)))

;;; Code to produce chain rules from an ASSUME.

(defun produce-chain-rules-from-assume (formula)
  (let* ((vars (list-of-leading-universals formula))
         (newvars (mapcar #'(lambda (u) (make-skolem nil u nil)) vars))
         (expr (without-proof-logging
                (strip-off-leading-universals formula nil))))
    (produce-chain-rules-from-assume-aux
     (sublis-eq (pairlis vars newvars) expr) (list vars newvars formula) nil)))

;;; Produce and add chain rules.

(defun produce-chain-rules-from-assume-aux (expr triple path)
  (cond ((if-p expr)
         (cond ((false-p (if-left expr))
		;; (AND (NOT test) right) => show test not equals (TRUE),
		;; independent of right. It us used to show an expression
		;; is (FALSE) when it is known to be in (BOOL).
		(when (consp (if-test expr))
                  (let ((node (intern-expression (if-test expr))))
                    (push-undo (list #'undo-chain-rule node 1
                                     (aref (e-node-chain-rules node) 1)))
                    (push (cons triple (reverse (cons 1 path)))
                          (aref (e-node-chain-rules node) 1))))
		;; Recursion on right independent of test.
                (produce-chain-rules-from-assume-aux
                 (if-right expr) triple (cons 3 path)))
               ((false-p (if-right expr))
		;; (AND test left) => show test is (TRUE), independent of left.
                (when (consp (if-test expr))
                  (let ((node (intern-expression (if-test expr))))
                    (push-undo (list #'undo-chain-rule node 0
                                     (aref (e-node-chain-rules node) 0)))
                    (push (cons triple (reverse (cons 1 path)))
                          (aref (e-node-chain-rules node) 0))))
		;; Recursion on left independent of test.
                (produce-chain-rules-from-assume-aux
                 (if-left expr) triple (cons 2 path)))
               (t
		;; Recursion on left, assuming test.
		(produce-chain-rules-from-assume-aux
		 (if-left expr) triple (cons 4 path))
		;; Recursion on right, denying test.
		(produce-chain-rules-from-assume-aux
		 (if-right expr) triple (cons 5 path)))))
        ((and (consp expr) (not (true-p expr)) (not (false-p expr)))
	 ;; Entire subexpression
         (let ((node (intern-expression expr)))
           (push-undo (list #'undo-chain-rule node 0
                            (aref (e-node-chain-rules node) 0)))
           (push (cons triple (reverse (cons 0 path)))
                 (aref (e-node-chain-rules node) 0))))))



;;; Test to determine if a DENY produces chain rules.

(defun deny-produces-chain-rules-p (formula)
  (cond ((some-p formula)
         (deny-produces-chain-rules-p (some-expr formula)))
        ((not (contains-quantifier formula)) t)))

;;; Code to produce chain rules from a DENY.

(defun produce-chain-rules-from-deny (formula)
  (let* ((vars (list-of-leading-existentials formula))
         (newvars (mapcar #'(lambda (u) (make-skolem nil u nil)) vars))
         (expr (without-proof-logging
                (strip-off-leading-existentials formula nil))))
    (produce-chain-rules-from-deny-aux
     (sublis-eq (pairlis vars newvars) expr) (list vars newvars formula) nil)))

(defun produce-chain-rules-from-deny-aux (expr triple path)
  (cond ((if-p expr)
         (cond ((true-p (if-left expr))
		;; (OR test right) => show test not equals (TRUE),
		;; independent of right.
                (when (consp (if-test expr))
                  (let ((node (intern-expression (if-test expr))))
                    (push-undo (list #'undo-chain-rule node 1
                                     (aref (e-node-chain-rules node) 1)))
                    (push (cons triple (reverse (cons 1 path)))
                          (aref (e-node-chain-rules node) 1))))
		;; Recursion on right, independent of test.
                (produce-chain-rules-from-deny-aux
                 (if-right expr) triple (cons 3 path)))
               ((true-p (if-right expr))
		;; (IMPLIES test left) => show test (TRUE), independent
		;; of left.
                (when (consp (if-test expr))
                  (let ((node (intern-expression (if-test expr))))
                    (push-undo (list #'undo-chain-rule node 0
                                     (aref (e-node-chain-rules node) 0)))
                    (push (cons triple (reverse (cons 1 path)))
                          (aref (e-node-chain-rules node) 0))))
		;; Recursion on left, independent of test.
                (produce-chain-rules-from-deny-aux
                 (if-left expr) triple (cons 2 path)))
               (t
		;; Recursion on left, assuming test
		(produce-chain-rules-from-deny-aux
		 (if-left expr) triple (cons 4 path))
		;; Recursion on right, denying test.
		(produce-chain-rules-from-deny-aux
		 (if-right expr) triple (cons 5 path)))))
        ((and (consp expr) (not (true-p expr)) (not (false-p expr)))
	 ;; Entire subexpression.
         (let ((node (intern-expression expr)))
           (push-undo (list #'undo-chain-rule node 1
                            (aref (e-node-chain-rules node) 1)))
           (push (cons triple (reverse (cons 0 path)))
                 (aref (e-node-chain-rules node) 1))))))

;;; ==================== End of Production of Chain Rules ====================


;;; ==================== Pending Assumes ====================

;;; Pending assumes are stacked on the *pending-assumptions-stack*.
(defvar *pending-assumptions-stack* nil)

;;; ----- Force Updates

;;; Update the deductive database with the pending assumes.
(defsubst perform-pending-assumptions ()
  (mapc #'(lambda (u) (apply (car u) (cdr u)))
        (nreverse *pending-assumptions-stack*))
  (setq *pending-assumptions-stack* nil))

;;; ==================== End of Pending Assumes ====================


;;; ==================== Retract Assumes ====================

;;; Because of the LAZY assumes, we need two levels of undo:
;;; one at the pending level via *pending-assumptions-stack* and
;;; one at a lower non-lazy level via *undo-stack* implemented elsewhere.

;;; Extra undo marker.
(defparameter *blip* 'blip)

;;; Function to push *blip* and *undo-push-mark* onto *undo-stack*.
(defun pending-blip ()
  (push-undo *blip*)
  (push-undo *undo-push-mark*))

;;; Define constant for efficiency. The constant represents the
;;; application of pending-blip with no parameters.
(defparameter *pending-blip* (list #'pending-blip))

;;; Push a pending blip onto *pending-assumptions-stack*. Only when
;;; necessary (when updates are actually performed) will this
;;; translate into a blip on *undo-stack*.
(defsubst stack-blip ()
  (push *pending-blip* *pending-assumptions-stack*))

;;; Undo back through the most recent *blip* on *undo-stack*.
;;; This undoes all of the assumptions made after the pushing of that blip.
(defun undo-stack-blip-in-egraph ()
  (loop until (or (null *undo-stack*)
		  (eq (car *undo-stack*) *blip*))
	do (pop-undo))
  (if *undo-stack*
      (progn (pop *undo-stack*)
	     (setq *merge-list* nil *tableau-list* nil))
      (error "Unable to recover egraph, missing blip.")))

;;; Define constant for efficiency.
(defparameter *pending-undo* (list #'undo-stack-blip-in-egraph))

;;; Undo back through to the most recent *pending-blip* on
;;; *pending-assumptions-stack*.
;;; If unsuccessful then it places a *pending-undo* on the stack.
(defun undo-stack-blip ()
  (loop until (or (null *pending-assumptions-stack*)
		  (eq (car *pending-assumptions-stack*) *pending-blip*)
		  (eq (car *pending-assumptions-stack*) *pending-undo*))
	do (pop *pending-assumptions-stack*))
  (if (and *pending-assumptions-stack*
	   (eq (car *pending-assumptions-stack*) *pending-blip*))
      (pop *pending-assumptions-stack*)
      (push *pending-undo* *pending-assumptions-stack*)))

;;; ==================== End of Retract Assumes ====================



;;; ==================== Caching Mechanism ====================

;;; Code for handling the caches used by reduce.

;;; The literal cache holds formulas which reduce to literals.
(defvar *reduce-literal-cache* 0)

;;; The dynamic cache holds all other reductions. It is rebound each
;;; time a new assumption is made and restored upon the removal of the
;;; new assumption.
(defvar *reduce-dynamic-cache* 0)

;;; Given a formula, return the cache index for it.
(defun cache-index (formula)
  (cond ((atom formula) formula)
	(t (cache-index (car formula)))))

;;; Given a function and key, return the associated entry in the cache.
;;; If successful, (value T index proof-log) is returned as multiple
;;; values. The T indicates success.

(defun get-cache (function key)
  (let ((cache-pair
         (or (assoc-equal key (getf (cdr *reduce-literal-cache*) function))
             (assoc-equal key (getf (cdr *reduce-dynamic-cache*) function)))))
    (cond ((null cache-pair) (values nil nil nil nil))
	  (t
	   (let ((entry (cdr cache-pair)))
	     (values (car entry) t (second entry) (third entry)))))))

;;; Put an entry in the cache.

(defun put-cache (function key value index proof-log)
  (let ((cache-pair (cons key (list value index proof-log))))
    (if (literal-p value)
	;; we have something for the literal cache
	;; unless the formula input was actually a value
	(progn (when (car *reduce-literal-cache*)	;copy?
		 (setq *reduce-literal-cache*
		       (cons nil (copy-list (cdr *reduce-literal-cache*)))))
	       (push cache-pair (getf (cdr *reduce-literal-cache*) function)))
	;; now we have something for the dynamic cache
	;; however successfull subgoals can be treated as literals
	(if (and value (second key))
	    (progn (when (car *reduce-literal-cache*)	;copy?
		     (setq *reduce-literal-cache*
			   (cons nil
                                 (copy-list (cdr *reduce-literal-cache*)))))
		   (push cache-pair
                         (getf (cdr *reduce-literal-cache*) function)))
	    (push cache-pair (getf (cdr *reduce-dynamic-cache*) function))))
    value))


;;; ==================== End of Caching Mechanism ====================




;;; ==================== The Interface ====================

;;; Initialize the caches.
(defmacro with-empty-cache (&body body)
  `(let ((*reduce-literal-cache* (list nil))
	 (*reduce-dynamic-cache* (list nil)))
     . ,body))

;;; Inherit the literal cache but use new dynamic cache.
;;; This is strongly tied to assumes and denies so only used
;;; below and nowhere else.
(defmacro with-inherited-cache (&body body)
  `(let ((*reduce-dynamic-cache* (list nil))
	 (*reduce-literal-cache* (cons t (cdr *reduce-literal-cache*))))
     . ,body))

;;; Lazy assume-true. When asserted, the formula is equated to (TRUE)
;;; in the deductive database.
(defsubst assume-true (formula)
  (push (list #'assume-in-egraph formula) *pending-assumptions-stack*))

;;; Lazy assume-false. When asserted, the formula is assumed to be
;;; not equal to (TRUE) in the deductive database.
(defsubst assume-false (formula)
  (push (list #'deny-in-egraph formula) *pending-assumptions-stack*))

;;; Lazy integration of expressions into the deductive database.
(defun intern-expressions (formula)
  (push (list #'intern-expressions-in-egraph formula)
        *pending-assumptions-stack*))

;;; Protect the deductive database by recovering its state after running
;;; some code which can modify it.
(defmacro with-egraph-protected (&body body)
  `(prog1 (progn (stack-blip) . ,body)
	  (undo-stack-blip)))

;;; *assumed-expression* is used by the reducer for its heuristics
;;; on recursive functions.
(defvar *assumed-expressions* nil)

;;; Run some code body after an assume, protecting the deductive database.
(defmacro with-assumed-true ((assumption) &body body)
  `(let ((*assumed-expressions* (cons ,assumption *assumed-expressions*)))
     (with-inherited-cache
      (with-egraph-protected (assume-true ,assumption) . ,body))))

;;; Run some code body after a denial, protecting the deductive database.
(defmacro with-assumed-false ((assumption) &body body)
  `(let ((*assumed-expressions* (cons ,assumption *assumed-expressions*)))
     (with-inherited-cache
      (with-egraph-protected (assume-false ,assumption) . ,body))))


;;; Run some code body with an assumption first assumed then denied. The
;;; result consists of the two values which are the results of the two forms.
(defmacro with-assumed-true-then-false ((assumption) true-form false-form)
  `(values (with-assumed-true (,assumption) ,true-form)
	   (with-assumed-false (,assumption) ,false-form)))

;;; ==================== End of The Interface ====================
