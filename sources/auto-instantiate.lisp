
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


;;; ========== Automatic Instantiations in the Simplifier ==========

;;; Code to do automatic instantiations of quantified variables in the
;;; simplifier. The main functionalities are:
;;; - Application of the one-point rule (called directly by the reducer).
;;; - Backchaining (mini-resolution, called through lookup).
;;; - Equivalence allowing instantiations (called through lookup).

;;; Globals

(proclaim '(special *true-node* *false-node* *zero-node* *enil* *cols* *rows*
		    *undo-stack* *instantiation-list* *inconsistent*))


;;; ==================== One-point Rule ====================


(defvar *one-point-rule-success* nil)

;;; ----- Top level function to apply one-point rule.

(defun apply-one-point-rule (formula index)
  (setq *one-point-rule-success* nil)
  (let ((result (apply-one-point-rule-aux formula index nil)))
    (when *one-point-rule-success* result)))

(defun apply-one-point-rule-aux (formula index bool-p)
  (cond
   ((all-p formula)
    (let ((var (all-var formula))
          (expr (apply-one-point-rule-aux
                 (all-expr formula) (all-expr-index)
		 (make-context-for-bool-p formula index))))
      (cond
       ((one-point-rule-applies-all-p var expr)
        (setq *one-point-rule-success* t)
        (push-proof-log 'marker index (list 'one-point 'start))
        (let* ((result (one-point-rule-phase-1-all
			var expr (all-expr-index) bool-p))
               (vars (list-of-leading-universals result)))
          (setq result (strip-off-leading-universals result (all-expr-index)))
          (when *record-proof-logs-flag*
            (log-flip-universals (length vars) index))
          (let ((inner-index (append (mapcar #'(lambda (u) u 2) vars) index))
                (replacement (one-point-instantiation-all var result)))
            ;; (all ... (all (var) expr))
            (setq result
                  (one-point-rule-phase-2-all
                   var replacement result inner-index))
            ;; (all ... (all (var) (if (= var replacement) expr (true))))
            (setq result
                  (one-point-replace-expr var replacement (if-left result)
                                          (list* 2 2 inner-index)))
            ;; (all ... (all (var) (if (= var replacement) result (true))))
            (when *record-proof-logs-flag*
	      (let ((f (make-all (list var)
				 (make-if (make-= var replacement)
					  result
					  *true*))))
		(log-all-case-analysis-2 f inner-index))
              (one-point-rule-log-instantiate var replacement inner-index)
              (push-proof-log 'marker index (list 'one-point 'end)))
            (make-series-of-quantification
             'all vars (make-if result *true* *false*)))))
       (t (make-all-single var expr)))))
   ((some-p formula)
    (let ((var (some-var formula))
          (expr (apply-one-point-rule-aux
                 (some-expr formula) (some-expr-index)
		 (make-context-for-bool-p formula index))))
      (cond
       ((one-point-rule-applies-some-p var expr)
        (setq *one-point-rule-success* t)
        (push-proof-log 'marker index (list 'one-point 'start))
        (let* ((result (one-point-rule-phase-1-some
                        var expr (some-expr-index) bool-p))
               (vars (list-of-leading-existentials result)))
          (setq result
                (strip-off-leading-existentials result (some-expr-index)))
          (when *record-proof-logs-flag*
            (repeat-log-flip-existentials (length vars) index))
          (let ((inner-index (append (mapcar #'(lambda (u) u 2) vars) index))
                (replacement (one-point-instantiation-some var result)))
            ;; (some ... (some (var) expr))
            (setq result
                  (one-point-rule-phase-2-some
                   var replacement result inner-index))
            ;; (some ... (some (var) (if (= var replacement) expr (false))))
            (setq result
                  (one-point-replace-expr var replacement (if-left result)
                                          (list* 2 2 inner-index)))
            ;; (some ... (some (var) (if (= var replacement) result (false))))
            (when *record-proof-logs-flag*
              (log-some-case-analysis-2
	       (make-some-single
		var (make-if (make-= var replacement) result *false*))
	       inner-index)
              (one-point-rule-log-instantiate var replacement inner-index)
              (push-proof-log 'marker index (list 'one-point 'end)))
            (push (cons var replacement) *instantiation-list*)
            (make-series-of-quantification
             'some vars (make-if result *true* *false*)))))
       (t (make-some-single var expr)))))
   (t formula)))

(defun one-point-rule-log-instantiate (var replacement index)
  (log-instantiate-existential `(= ,var ,replacement) (cons 1 index))
  (push-proof-log 'compute (list* 1 1 index))
  (push-proof-log 'if-true (cons 1 index))
  (push-proof-log 'if-true index))


;;; ----- Predicate to determine if one-point rule can be applied.

(defun one-point-rule-applies-all-p (var formula)
  (cond ((and (if-p formula)
              (true-p (if-right formula)))
         (or (one-point-rule-applies-some-p var (if-test formula))
             (one-point-rule-applies-all-p var (if-left formula))))
        ((and (if-p formula)
              (true-p (if-left formula)))
         (or (one-point-rule-applies-all-p var (if-test formula))
             (one-point-rule-applies-all-p var (if-right formula))))
        ((all-p formula)
         (one-point-rule-applies-all-p var (all-expr formula)))))

(defun one-point-rule-applies-some-p (var formula)
  (cond ((and (if-p formula) (false-p (if-right formula)))
         (or (one-point-rule-applies-some-p var (if-test formula))
             (one-point-rule-applies-some-p var (if-left formula))))
        ((and (if-p formula)
              (false-p (if-left formula)))
         (or (one-point-rule-applies-all-p var (if-test formula))
             (one-point-rule-applies-some-p var (if-right formula))))
        ((some-p formula)
         (one-point-rule-applies-some-p var (some-expr formula)))
        ((=-p formula)
         (or (and (eq (=-left formula) var)
                  (not (occurs-in var (=-right formula))))
             (and (eq (=-right formula) var)
                  (not (occurs-in var (=-left formula))))))))

;;; ----- Phase 1 - move blocking quantifiers out (after renaming them).

(defun one-point-rule-phase-1-all (var expr index bool-p)
  (cond ((all-p expr)
         (let ((newvar (genvar (all-var expr))))
           (push-proof-log 'rename-universal index (all-var expr) newvar)
           (make-all-single
             newvar
             (one-point-rule-phase-1-all
	      var (subst-eq newvar (all-var expr) (all-expr expr))
	      (all-expr-index)
	      (make-context-for-bool-p
	       (make-all-single newvar *true*) index)))))
        ((and (if-p expr) (true-p (if-right expr)))
         (cond ((one-point-rule-applies-some-p var (if-test expr))
                (one-point-move-somes-out-test-negate
                 (one-point-rule-phase-1-some
                  var (if-test expr) (if-test-index)
		  (make-context-for-bool-p expr index))
                 (if-left expr)
                 index bool-p))
               (t (one-point-move-alls-out-left
                   (if-test expr)
                   (one-point-rule-phase-1-all
                    var (if-left expr) (if-left-index) bool-p)
                   index bool-p))))
        (t ; (if test (true) right)
         (cond ((one-point-rule-applies-all-p var (if-test expr))
                (one-point-move-alls-out-test
                 (one-point-rule-phase-1-all
                  var (if-test expr) (if-test-index)
		  (make-context-for-bool-p expr index))
                 (if-right expr)
                 index bool-p))
               (t
                (one-point-move-alls-out-right
                 (if-test expr)
                 (one-point-rule-phase-1-all
                  var (if-right expr) (if-right-index) bool-p)
                 index bool-p))))))

(defun one-point-rule-phase-1-some (var expr index bool-p)
  (cond ((some-p expr)
         (let ((newvar (genvar (some-var expr))))
           (log-rename-existential (some-var expr) newvar index)
           (make-some-single
             newvar
             (one-point-rule-phase-1-some
               var (subst-eq newvar (some-var expr) (some-expr expr))
               (some-expr-index)
	       (make-context-for-bool-p
		(make-some-single newvar *true*) index)))))
        ((and (if-p expr) (false-p (if-left expr)))
         (cond ((one-point-rule-applies-all-p var (if-test expr))
                (one-point-move-alls-out-test-negate
                 (one-point-rule-phase-1-all
                  var (if-test expr) (if-test-index)
		  (make-context-for-bool-p expr index))
                 (if-right expr)
                 index bool-p))
               (t (one-point-move-somes-out-right
                   (if-test expr)
                   (one-point-rule-phase-1-some
                    var (if-right expr) (if-right-index) bool-p)
                   index bool-p))))
        ((and (if-p expr) (false-p (if-right expr)))
         (cond ((one-point-rule-applies-some-p var (if-test expr))
                (one-point-move-somes-out-test
                 (one-point-rule-phase-1-some
                  var (if-test expr) (if-test-index)
		  (make-context-for-bool-p expr index))
                 (if-left expr)
                 index bool-p))
               (t
                (one-point-move-somes-out-left
                 (if-test expr)
                 (one-point-rule-phase-1-some
                  var (if-left expr) (if-left-index) bool-p)
                 index bool-p))))
        (t expr))) ; (= var e) or (= e var)

(defun one-point-move-alls-out-test (test right index bool-p)
  ;; (if test (true) right)
  (cond ((all-p test)
	 (log-coerce-expr-for-boolean-or-bool-p right (if-right-index) bool-p)
         ;; (if (all () ...) (true) (if right (true) (false)))
	 (log-all-uncase-analysis-3
	  (make-if test *true* (make-if right *true* *false*)) index)
         (make-all (all-vars test)
                   (one-point-move-alls-out-test
                    (all-expr test) right (all-expr-index)
		    (make-context-for-bool-p
		     (make-all (all-vars test) *true*) index))))
        (t (make-if test *true* right))))

(defun one-point-move-alls-out-test-negate (test right index bool-p)
  ;; (if test (false) right)
  (cond ((all-p test)
	 (log-coerce-expr-for-boolean-or-bool-p right (if-right-index) bool-p)
         ;; (if (all () ...) (false) (if right (true) (false)))
	 (log-some-uncase-analysis-3
	  (make-if test *false* (make-if right *true* *false*)) index)
         (make-some (all-vars test)
                    (one-point-move-alls-out-test-negate
                     (all-expr test) right (all-expr-index)
		     (make-context-for-bool-p
		      (make-some (all-vars test) *true*) index))))
        (t (make-if test *false* right))))

(defun one-point-move-alls-out-left (test left index bool-p)
  ;; (if test left (true))
  (cond ((all-p left)
	 (push-proof-log 'is-boolean (if-right-index))
	 (push-proof-log 'remove-universal (if-right-index)
			 (all-vars left) t)
	 (log-all-uncase-analysis-1
	  (make-if test left (make-all (all-vars left) *true*)) index)
         (make-all (all-vars left)
                   (one-point-move-alls-out-left
                    test (all-expr left) (all-expr-index)
		    (make-context-for-bool-p
		     (make-all (all-vars left) *true*) index))))
        (t (make-if test left *true*))))

(defun one-point-move-alls-out-right (test right index bool-p)
  ;; (if test (true) right)
  (cond ((all-p right)
	 (push-proof-log 'is-boolean (if-left-index))
	 (push-proof-log 'remove-universal (if-left-index)
			 (all-vars right) t)
	 (log-all-uncase-analysis-1
	  (make-if test (make-all (all-vars right) *true*) right) index)
         (make-all (all-vars right)
                   (one-point-move-alls-out-right
                    test (all-expr right) (all-expr-index)
		    (make-context-for-bool-p
		     (make-all (all-vars right) *true*) index))))
        (t (make-if test *true* right))))

(defun one-point-move-somes-out-test (test left index bool-p)
  ;; (if test left (false))
  (cond ((some-p test)
	 (log-coerce-expr-for-boolean-or-bool-p left (if-left-index) bool-p)
	 (log-some-uncase-analysis-2
	  (make-if test (make-if left *true* *false*) *false*) index)
         (make-some (some-vars test)
                    (one-point-move-somes-out-test
                     (some-expr test) left (all-expr-index)
		     (make-context-for-bool-p
		      (make-some (some-vars test) *true*) index))))
        (t (make-if test left *false*))))

(defun one-point-move-somes-out-test-negate (test left index bool-p)
  ;; (if test left (true))
  (cond ((some-p test)
	 (log-coerce-expr-for-boolean-or-bool-p left (if-left-index) bool-p)
	 (log-all-uncase-analysis-2
	  (make-if test (make-if left *true* *false*) *true*) index)
         (make-all (some-vars test)
                   (one-point-move-somes-out-test-negate
                    (some-expr test) left (all-expr-index)
		    (make-context-for-bool-p
		     (make-all (some-vars test) *true*) index))))
        (t (make-if test left *true*))))

(defun one-point-move-somes-out-left (test left index bool-p)
  ;; (if test left (false))
  (cond ((some-p left)
	 (push-proof-log 'is-boolean (if-right-index))
	 (log-introduce-existential (some-vars left) (if-right-index))
	 (log-some-uncase-analysis-1
	  (make-if test left (make-some (some-vars left) *false*)) index)
         (make-some (some-vars left)
                    (one-point-move-somes-out-left
                     test (some-expr left) (all-expr-index)
		     (make-context-for-bool-p
		      (make-some (some-vars left) *true*) index))))
        (t (make-if test left *false*))))

(defun one-point-move-somes-out-right (test right index bool-p)
  ;; (if test (false) right)
  (cond ((some-p right)
	 (push-proof-log 'is-boolean (if-left-index))
	 (log-introduce-existential (some-vars right) (if-left-index))
	 (log-some-uncase-analysis-1
	  (make-if test (make-some (some-vars right) *false*) right) index)
         (make-some (some-vars right)
                    (one-point-move-somes-out-right
                     test (some-expr right) (all-expr-index)
		     (make-context-for-bool-p
		      (make-some (some-vars right) *true*) index))))
        (t (make-if test *false* right))))

;;; ----- Phase 2 - split on (= var replacement) and simplify the right
;;; branch to (true) or (false).

(defun one-point-rule-phase-2-all (var replacement expr index)
  ;; (all (var) expr)
  (push-proof-log 'if-equal (all-expr-index) `(= ,var ,replacement) t)
  ;; (all (var) (if (= var replacement) expr expr))
  (when *record-proof-logs-flag*
    (one-point-log-simplify-all
     var replacement expr (cons 3 (all-expr-index))))
  ;; (all (var) (if (= var replacement) expr (true)))
  (make-if `(= ,var ,replacement) expr *true*))

(defun one-point-rule-phase-2-some (var replacement expr index)
  ;; (some (var) expr)
  (push-proof-log 'if-equal (some-expr-index) `(= ,var ,replacement) t)
  ;; (some (var) (if (= var replacement) expr expr))
  (when *record-proof-logs-flag*
    (one-point-log-simplify-some
     var replacement expr (cons 3 (some-expr-index))))
  ;; (some (var) (if (= var replacement) expr (true)))
  (make-if `(= ,var ,replacement) expr *false*))

;;; Log conversion of expr to (true)

(defun one-point-log-simplify-all (var replacement expr index)
  (cond ((and (if-p expr) (true-p (if-right expr)))
         (cond ((one-point-rule-applies-some-p var (if-test expr))
                (one-point-log-simplify-some var replacement (if-test expr)
                                             (if-test-index))
                (push-proof-log 'if-false index))
               (t (one-point-log-simplify-all var replacement (if-left expr)
                                              (if-left-index))
                  (push-proof-log 'if-equal index))))
        ((one-point-rule-applies-all-p var (if-test expr))
         (one-point-log-simplify-all var replacement (if-test expr)
                                     (if-test-index))
         (push-proof-log 'if-true index))
        (t
         (one-point-log-simplify-all var replacement (if-right expr)
                                     (if-right-index))
         (push-proof-log 'if-equal index))))

;;; Log conversion of expr to (false)

(defun one-point-log-simplify-some (var replacement expr index)
  (cond ((=-p expr)
         (when (not (eq (=-left expr) var))
           (log-commute-= replacement var index))
         ;; (= var replacement)
         (log-convert-boolean-to-coerced `(= ,var ,replacement) index)
         ;; (if (= var replacement) (true) (false))
         (push-proof-log 'if-false (if-left-index) *false* t)
         (push-proof-log 'if-true (if-right-index) *true* t)
         ;; (if (= var replacement)
         ;;     (if (false) (false) (true))
         ;;     (if (true) (false) (true)))
         (push-proof-log 'case-analysis index 1 t)
         (push-proof-log 'look-up (if-test-index) *true*)
         (push-proof-log 'if-true index))
        ((and (if-p expr) (false-p (if-left expr)))
         ;; (if test (false) right)
         (cond ((one-point-rule-applies-all-p var (if-test expr))
                (one-point-log-simplify-all var replacement (if-test expr)
                                            (if-test-index))
                (push-proof-log 'if-true index))
               (t (one-point-log-simplify-some var replacement (if-right expr)
                                               (if-right-index))
                  (push-proof-log 'if-equal index))))
        ((one-point-rule-applies-some-p var (if-test expr))
         (one-point-log-simplify-some var replacement (if-test expr)
                                      (if-test-index))
         (push-proof-log 'if-false index))
        (t
         (one-point-log-simplify-some var replacement (if-left expr)
                                      (if-left-index))
         (push-proof-log 'if-equal index))))

;;; Functions that return the instantiation for the var for the one-point rule.

(defun one-point-instantiation-all (var formula)
  (cond ((and (if-p formula)
              (true-p (if-right formula)))
         (or (one-point-instantiation-some var (if-test formula))
             (one-point-instantiation-all var (if-left formula))))
        ((and (if-p formula)
              (true-p (if-left formula)))
         (or (one-point-instantiation-all var (if-test formula))
             (one-point-instantiation-all var (if-right formula))))))

(defun one-point-instantiation-some (var formula)
  (cond ((=-p formula)
         (or (and (eq (=-left formula) var)
                  (not (occurs-in var (=-right formula)))
                  (=-right formula))
             (and (eq (=-right formula) var)
                  (not (occurs-in var (=-left formula)))
                  (=-left formula))))
        ((and (if-p formula)
              (false-p (if-left formula)))
         (or (one-point-instantiation-all var (if-test formula))
             (one-point-instantiation-some var (if-right formula))))
        ((and (if-p formula)
              (false-p (if-right formula)))
         (or (one-point-instantiation-some var (if-test formula))
             (one-point-instantiation-some var (if-left formula))))))

;;; Replace free occurrences of var in expr by replacement and
;;; log in terms of LOOK-UP.

(defun one-point-replace-expr (var replacement expr index)
  (cond ((atom expr)
         (cond ((eq expr var)
                (push-proof-log 'look-up index replacement)
                replacement)
               (t expr)))
        ((all-p expr)
         (cond ((eq (all-var expr) var) expr)
               (t (make-all
                   (all-vars expr)
                   (one-point-replace-expr
                    var replacement (all-expr expr) (all-expr-index))))))
        ((some-p expr)
         (cond ((eq (some-var expr) var) expr)
               (t (make-some
                   (some-vars expr)
                   (one-point-replace-expr
                    var replacement (some-expr expr) (some-expr-index))))))
        (t (cons (car expr)
                 (loop for e in (cdr expr)
                       for i = 1 then (+ i 1)
                       collect (one-point-replace-expr
                                var replacement e (cons i index)))))))

;;; ==================== End of One-point Rule ====================


;;; ==================== Backchaining ====================


;;; Backchaining is a mini-resolution step performed during a lookup
;;; using chain rules produced by assumes and denys.

;;; Prevent infinite backchaining. For efficiency, keep this
;;; number very low.

(defvar *max-backchain-depth* 1)

(defmacro with-limit (&body body)
  `(let ((*max-backchain-depth* (1- *max-backchain-depth*)))
     (unless (< *max-backchain-depth* 0) . ,body)))

;;; The top level routines.

(defun true-with-backchain (e-node index)
  (backchain-true e-node `((,*true* ,(e-node-attribute e-node))) index))

;;; Note that false-with-backchain is called only if (e-node-attribute e-node)
;;; is known to be in (BOOL).
(defun false-with-backchain (e-node index)
  (backchain-false e-node `((,*false* ,(e-node-attribute e-node))) index))

;;; Backchain rules are searched in nodes that potentially match,
;;; i.e. those nodes that represent expressions that are application
;;; of the same function symbol as that of the looked up formula.

(defun backchain-true (e-node backchain-list index)
  (let ((expr (e-node-attribute e-node)))
    (with-limit
     (with-undo
      (dolist (next (make-node-list-excluding e-node-samecar e-node))
        (let ((rules (aref (e-node-chain-rules next) 0))
              (pattern (e-node-attribute next)))
          (and rules
               (multiple-value-bind (substitutions success)
                  (simple-pattern-match
                    pattern expr (unique (list-of-skolem-variables pattern)))
                 (when (and success
                            (condition-satisfied
                             e-node substitutions rules backchain-list
                             *true* index))
                   (return t))))))))))

(defun backchain-false (e-node backchain-list index)
  (let ((expr (e-node-attribute e-node)))
    (with-limit
     (with-undo
      ;; Because expr is known to be in (BOOL), not equals (TRUE)
      ;; is equal to (FALSE).
      (dolist (next (make-node-list-excluding e-node-samecar e-node))
        (let ((rules (aref (e-node-chain-rules next) 1))
              (pattern (e-node-attribute next)))
          (and rules
               (multiple-value-bind (substitutions success)
                  (simple-pattern-match
                   pattern expr (unique (list-of-skolem-variables pattern)))
                 (when (and success
                            (condition-satisfied
                             e-node substitutions rules backchain-list
                             *false* index))
                   (return t))))))))))

;;; Determine if condition is satisfied by an e-node. To satisfy the
;;; condition, node must be shown to be representing an expression that
;;; is equal to (TRUE) or not equal to (TRUE), depending on goal, using
;;; one of the chaining rules in rules.

;;; node - e-node for looked up formula
;;; substitutions - instantiation of skolem variables
;;; rules - matching backchaining rules
;;; backchain-list - a list of currently active backchains
;;;                  (for possible recursive backchaining)
;;; goal - (TRUE) or (FALSE)
;;; index - for proof logging

(defun condition-satisfied (node substitutions rules backchain-list goal index)
  (dolist (r rules)
    (let ((vars (first (car r)))     ; quantifier variables
          (newvars (second (car r))) ; skolem variables
          (formula (third (car r)))  ; quantified formula
          (path (cdr r))
          skolems sub result proof-log instantiations)
      ;; set skolem variables and constants
      (setq skolems
            (mapcar #'(lambda (n) (if (assoc-eq n substitutions)
                                      n
                                    (make-skolem nil n nil)))
                    newvars))
      (setq sub
            (loop for v in vars
                  for s in skolems
                  collect (cons v (if (member-eq s newvars)
                                      (cdr (assoc-eq s substitutions))
                                    s))))
      (let ((*proof-log* nil))
        (with-undo
         (setq result
               (subgoals-satisfied
                path
                (sublis-eq
                 sub (without-proof-logging
                      (if (all-p formula)
                          (strip-off-leading-universals formula nil)
                        (strip-off-leading-existentials formula nil))))
                (remove-if #'(lambda (v) (member-eq v newvars)) skolems)
                backchain-list (cons 1 (if-test-index))))
         (unless (null result)
           (dolist (entry (second result))
	     ;; Cycle check.
             (when (contains-skolem-p (cdr entry)) (setq result nil))))
         (unless (null result) (setq proof-log (save-proof-log)))))
      (unless (null result)
        (setq sub (second result))
        (setq instantiations
              (loop for v in vars
                    for s in skolems
                    collect (let ((entry (or (assoc-eq s sub)
                                             (assoc-eq s substitutions))))
                              (cons v (cond ((null entry) 0)
                                            (t (cdr entry)))))))
        (dolist (i instantiations) (push i *instantiation-list*)))
      (unless (or (null result) *record-proof-logs-flag*) (return t))
      (unless (null result)
        (push-proof-log 'marker index '(backchain start))
        (push-proof-log 'if-true index goal t)
        ;; (if (true) expr goal)
        (cond ((all-p formula)
	       (push-proof-log 'look-up (if-test-index) formula)
               (log-instantiations 'all nil instantiations (if-test-index))
               (push-proof-log 'look-up (cons 2 (if-test-index)) *true*))
              (t
	       (push-proof-log 'look-up (if-test-index)
			       (make-if formula *false* *true*))
	       (log-instantiations 'some nil instantiations
				   (cons 1 (if-test-index)))
	       (push-proof-log 'case-analysis (if-test-index) 1)
	       (push-proof-log 'if-true (cons 2 (if-test-index)))
	       (push-proof-log 'look-up (cons 3 (if-test-index)) *true*)))
        (setq *proof-log* (append proof-log *proof-log*))
        ;; (if res expr goal)
        ;; res is (if result (true) (false)) when formula is universal
        ;; or (if result (false) (true)) when formula is existential
        (cond ((all-p formula)
               (log-condition-satisfied-all node (first result) goal index))
              (t (log-condition-satisfied-some
                  node (first result) goal index)))
        (push-proof-log 'marker index '(backchain end))
        (return t)))))

(defun log-condition-satisfied-all (node path goal index)
  (push-proof-log 'case-analysis index 1)
  (push-proof-log 'if-true (if-left-index))
  (push-proof-log 'if-false (if-right-index))
  ;; (if result expr goal)
  (log-condition-satisfied-all-aux node path goal index))

(defun log-condition-satisfied-all-aux (node path goal index)
  (cond ((null path) ; goal must be (true)
         ;; (if expr expr (true))
         (push-proof-log 'look-up (if-left-index) *true*)
         (push-proof-log 'if-equal index))
        ((= (car path) 1)
         (cond ((true-p goal)
                ;; (if (if expr left (false)) expr (true))
                (push-proof-log 'case-analysis index 1)
                ;; (if expr (if left expr (true)) (if (false) expr (true)))
                (push-proof-log 'look-up (cons 2 (if-left-index)) *true*)
                (push-proof-log 'if-equal (if-left-index))
		(push-proof-log 'if-false (if-right-index))
                (push-proof-log 'if-equal index))
               (t
                ;; (if (if expr (false) right) expr (false))
                (push-proof-log 'case-analysis index 1)
                ;; (if expr (if (false) expr (false)) (if right expr (false)))
		(push-proof-log 'if-false (if-left-index))
                ;; (if expr (false) (if right expr (false)))
                (log-denied-boolean node (cons 2 (if-right-index)))
                (push-proof-log 'if-equal (if-right-index))
                (push-proof-log 'if-equal index))))
        ((= (car path) 2)
         ;; (if (if test left (false)) expr goal)
         (push-proof-log 'case-analysis index 1)
         ;; (if test (if left expr goal) (if (false) expr (goal)))
         (log-condition-satisfied-all-aux node (cdr path) goal (if-left-index))
	 (push-proof-log 'if-false (if-right-index))
         (push-proof-log 'if-equal index))
        ((= (car path) 3)
         ;; (if (if test (false) right) expr goal)
         (push-proof-log 'case-analysis index 1)
         ;; (if test (if (false) expr (goal)) (if right expr goal))
	 (push-proof-log 'if-false (if-left-index))
         (log-condition-satisfied-all-aux
          node (cdr path) goal (if-right-index))
         (push-proof-log 'if-equal index))))

(defun log-condition-satisfied-some (node path goal index)
  (push-proof-log 'case-analysis index 1)
  (push-proof-log 'if-false (if-left-index))
  (push-proof-log 'if-true (if-right-index))
  ;; (if result goal expr)
  (log-condition-satisfied-some-aux node path goal index))

(defun log-condition-satisfied-some-aux (node path goal index)
  (cond ((null path) ; goal must be (false)
         ;; (if expr (false) expr)
         (log-denied-boolean node (if-right-index))
         (push-proof-log 'if-equal index))
        ((= (car path) 1)
         (cond ((true-p goal)
                ;; (if (if expr left (true)) (true) expr)
                (push-proof-log 'case-analysis index 1)
                ;; (if expr (if left (true) expr) (if (true) (true) expr))
                (push-proof-log 'look-up (cons 3 (if-left-index)) *true*)
                (push-proof-log 'if-equal (if-left-index))
                (push-proof-log 'if-true (if-right-index))
                (push-proof-log 'if-equal index))
               (t
                ;; (if (if expr (true) right) (false) expr)
                (push-proof-log 'case-analysis index 1)
                ;; (if expr (if (true) (false) expr) (if right (false) expr))
                (push-proof-log 'if-true (if-left-index))
                ;; (if expr (false) (if right (false) expr))
                (log-denied-boolean node (cons 3 (if-right-index)))
                (push-proof-log 'if-equal (if-right-index))
                (push-proof-log 'if-equal index))))
        ((= (car path) 2)
         ;; (if (if test left (true)) goal expr)
         (push-proof-log 'case-analysis index 1)
         ;; (if test (if left goal expr) (if (true) goal (expr)))
         (log-condition-satisfied-some-aux
          node (cdr path) goal (if-left-index))
         (push-proof-log 'if-true (if-right-index))
         (push-proof-log 'if-equal index))
        ((= (car path) 3)
         ;; (if (if test (true) right) goal expr)
         (push-proof-log 'case-analysis index 1)
         ;; (if test (if (true) (goal) expr) (if right goal expr))
         (push-proof-log 'if-true (if-left-index))
         (log-condition-satisfied-some-aux
          node (cdr path) goal (if-right-index))
         (push-proof-log 'if-equal index))))

;;; Determine if all subgoals are satisfied within the logical
;;; structure specified. The logical structure is specified by path.
(defun subgoals-satisfied (path expr vars backchain-list index)
  (let ((i (car path)))
    (cond ((= i 0)
           (list nil nil vars expr))
          ((= i 1)
           (list '(1) nil vars expr))
          ((= i 2)
           (let ((result (subgoals-satisfied
                          (cdr path) (if-left expr) vars backchain-list
                          (if-left-index))))
             (unless (null result)
               (list (cons 2 (first result)) (second result) (third result)
                     `(if ,(sublis-eq (second result) (if-test expr))
                          ,(fourth result)
                        ,(sublis-eq (second result) (if-right expr)))))))
          ((= i 3)
           (let ((result (subgoals-satisfied
                          (cdr path) (if-right expr) vars backchain-list
                          (if-right-index))))
             (unless (null result)
               (list (cons 3 (first result)) (second result) (third result)
                     `(if ,(sublis-eq (second result) (if-test expr))
                          ,(sublis-eq (second result) (if-left expr))
                        ,(fourth result))))))
          ((= i 4)
           (let ((result (subgoals-satisfied
                          (cdr path) (if-left expr) vars backchain-list
                          (if-left-index))))
             (unless (null result)
               (let* ((test (sublis-eq (second result) (if-test expr)))
                      (node (intern-expression test)))
                 (when (or (true-with-match node (if-test-index))
                           (and (=-p test)
                                (with-undo
                                 (when
                                  (match-and-merge (arg-1-node node)
                                                   (arg-2-node node))
                                  (when *record-proof-logs-flag*
                                    (log-node-equality
                                     (arg-1-node node) (arg-2-node node)
                                     (cons 1 (if-test-index))))
                                  t))
                                (progn (push-proof-log 'compute
                                                       (if-test-index))
                                       t))
                           (backchain-true
                            node (cons `(,*true* ,test) backchain-list)
                            (if-test-index)))
                   (push-proof-log 'if-true index)
                   (modify-backchain-result result))))))
          ((= i 5)
           (let ((result (subgoals-satisfied
                          (cdr path) (if-right expr) vars backchain-list
                          (if-right-index)))
                 (test (if-test expr)))
             (unless (null result)
               (let ((node (intern-expression
                            (sublis-eq (second result) test))))
                 (unless (node-bool-p node)
                   (when *record-proof-logs-flag*
		     (push-proof-log 'if-test index))
                   (setq node (intern-expression
                               (make-= (e-node-attribute node) *true*))))
                 (when (or (false-with-match node (if-test-index))
                           (backchain-false
                            node (cons `(,*false* ,test) backchain-list)
                            (if-test-index)))
		   (push-proof-log 'if-false index)
                   (modify-backchain-result result)))))))))

;;; Modify backchain result, where result is a list (path subst vars expr).
;;; subst, vars and expr must be modified according to instantiations
;;; recorded in *instantiation-list*.
(defun modify-backchain-result (result)
  (let ((subst (second result))
        (expr (fourth result))
        (vars nil))
    (dolist (v (third result))
      (let ((entry (assoc-eq v *instantiation-list*)))
        (cond ((null entry) (push v vars))
              (t (push entry subst)
                 (setq expr (sublis-eq (list entry) expr))))))
    (list (first result) subst vars expr)))


;;; Log transformation of expr to (FALSE) where the node for expr
;;; is known to have a type of (BOOL) and expr is denied.

(defun log-denied-boolean (node index)
  (let ((expr (e-node-attribute node)))
    ;; expr
    (push-proof-log 'if-equal index `(= ,expr (true)) t)
    (push-proof-log 'look-up (if-left-index) *true*)
    (push-proof-log 'if-equal (if-left-index)
                    `(= (true) (if ,expr (false) (true))) t)
    (push-proof-log 'look-up (cons 2 (if-left-index))
                    `(if ,expr (false) (true)))
    ;; (if (= expr (true))
    ;;     (if (= (true) (if expr (false) (true)))
    ;;         (if expr (false) (true))
    ;;         (true))
    ;;     expr)
    (push-proof-log 'look-up (list* 2 1 (if-left-index)) *true*)
    (push-proof-log 'compute (cons 1 (if-left-index)))
    (push-proof-log 'if-true (if-left-index))
    ;; (if (= expr (true)) (if expr (false) (true)) expr)
    (push-proof-log 'look-up (cons 1 (if-left-index)) *true*)
    (push-proof-log 'look-up (cons 3 (if-left-index)) expr)
    ;; (if (= expr (true)) (if (true) (false) expr) expr)
    (push-proof-log 'if-equal (if-right-index) `(= ,expr (false)) t)
    (push-proof-log 'look-up (cons 2 (if-right-index)) *false*)
    ;; (if (= expr (true))
    ;;     (if (true) (false) expr)
    ;;     (if (= expr (false)) (false) expr))
    (push-proof-log 'case-analysis index 1 t)
    (log-use-bool-definition expr (if-test-index) t)
    ;; (if (= (type-of expr) (bool)) (false) expr)
    (log-node-equality (e-node-type node) *bool-node* (cons 1 (if-test-index)))
    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)))


;;; ==================== End of Backchaining ====================


;;; =============== Equivalence with Instantiations  ===============


;;; Check to see if a node is equivalent to true, allowing matching.
(defun true-with-match (e-node index)
  (or (is-inconsistent *true* index)
      ;; see if the node matches a node in
      ;; the equivalence class of true.
      (dolist (node (make-node-list-excluding e-node-eqclass *true-node*))
        (when (with-undo (match-and-merge node e-node))
          (when *record-proof-logs-flag*
            (log-node-equality e-node node index)
            (log-node-equality node *true-node* index))
          (return t)))))

;;; Check to see if a node is not equivalent to true, allowing matching.
(defun false-with-match  (e-node index)
  (or (is-inconsistent *false* index)
      ;; see if the node matches a node in
      ;; the equivalence class of false.
      (dolist (node (make-node-list-excluding e-node-eqclass *false-node*))
        (when (with-undo (match-and-merge node e-node))
          (when *record-proof-logs-flag*
            (log-node-equality e-node node index)
            (log-node-equality node *false-node* index))
          (return t)))))

;;; Try to unify two e-nodes.
(defun match-and-merge (node-1 node-2)
  (cond
   ;; Success if the nodes are already in the same equivalence class.
   ((eq (e-node-root node-1) (e-node-root node-2)) t)
   ;; If the nodes are in each other's forbidden list, then failed.
   ((check-forbid node-1 node-2) nil)
   ;; The first node is an instantiable variable node.
   ((and (e-node-variable node-1) (check-var-merge node-1 node-2))
    (push (cons (e-node-attribute node-1) (e-node-attribute node-2))
          *instantiation-list*)
    (merge-nodes node-1 node-2 'instantiate) t)
   ;; The second node is an instantiable variable node.
   ((and (e-node-variable node-2) (check-var-merge node-2 node-1))
    (push (cons (e-node-attribute node-2) (e-node-attribute node-1))
          *instantiation-list*)
    (merge-nodes node-2 node-1 'instantiate) t)
   ;; Give up if the nodes are atomic.
   ((or (is-a-leaf node-1) (is-a-leaf node-2))
    nil)
   ;; Try to unify function applications.
   ((and (match-and-merge (e-node-ecar node-1) (e-node-ecar node-2))
         (match-and-merge-aux (e-node-ecdr node-1)
                              (e-node-ecdr node-2)))
    t)))

;;; Try to unify two aux-nodes.
(defun match-and-merge-aux (node-1 node-2)
  (cond
   ;; Success if the aux-nodes are already in the same equivalence class.
   ((eq (aux-node-root node-1) (aux-node-root node-2)) t)
   ;; Give up if the aux-nodes are atomic.
   ((or (is-a-leaf-aux node-1) (is-a-leaf-aux node-2)) nil)   
   ;; Try unify the ecars and the ecdrs.
   ((and (match-and-merge-aux (aux-node-ecdr node-1) (aux-node-ecdr node-2))
         (match-and-merge (aux-node-ecar node-1) (aux-node-ecar node-2)))
    t)))


;;; See if it is ok to merge a variable node with some other node.
(defun check-var-merge (var-node instance-node)
  (and (null (e-node-forbid (e-node-root var-node)))
       (not (equivalent-to-non-var var-node))
       (substitution-terminates var-node instance-node)))

;;; See if a node is equivalent to a literal or constant node.
(defun equivalent-to-literal-or-constant (node)
  (loop-over-nodes (n node e-node-eqclass)
    (when (litconst-p (e-node-attribute n)) (return t))))

;;; Generalization of the occurs check of syntactic unification.
(defun substitution-terminates (var-node other-node)
  (multiple-value-bind (success successes fails)
      (substitution-terminates-aux
       (e-node-root var-node) (e-node-root other-node) nil nil)
    successes
    fails
    success))

(defun substitution-terminates-aux
  (root-1 root-2 successful-roots failed-roots)
  (cond ((or (eq root-2 root-1) (member-eq root-2 failed-roots))
	 (values nil successful-roots failed-roots))
	((member-eq root-2 successful-roots)
	 (values t successful-roots failed-roots))
	(t (let ((success nil)
		 (successes successful-roots)
		 (fails (cons root-2 failed-roots))
		 (node-2-equivalent-to-non-variable nil))
	     (dolist (n2 (make-node-list e-node-eqclass root-2))
	       (unless (e-node-variable n2)
		 (setq node-2-equivalent-to-non-variable t)
		 (cond ((is-a-leaf n2) (return (setq success t)))
		       (t (let ((root-3 (e-node-root (e-node-ecar n2))))
			    (multiple-value-setq (success successes fails)
			      (substitution-terminates-aux
                               root-1 root-3 successes fails))
			    (when success
			      (multiple-value-setq (success successes fails)
				(substitution-terminates-aux-aux
				  root-1 (e-node-ecdr n2) successes fails))
			      (when success (return t))))))))
	     (cond ((or success (not node-2-equivalent-to-non-variable))
		    (values t (cons root-2 successes)
                            (remove-eq root-2 fails)))
		   (t (values nil successes fails)))))))

(defun substitution-terminates-aux-aux
  (root-1 aux-node successful-roots failed-roots)
  (cond ((is-a-leaf-aux aux-node) (values t successful-roots failed-roots))
	(t (let ((root-2 (e-node-root (aux-node-ecar aux-node))))
	     (multiple-value-bind (success successes fails)
		 (substitution-terminates-aux
                  root-1 root-2 successful-roots failed-roots)
	       (if success
		   (substitution-terminates-aux-aux
		     root-1 (aux-node-ecdr aux-node) successes fails)
		   (values nil successes fails)))))))

;;; See if a node is equivalent to some other node that does not
;;; represent a variable.
(defun equivalent-to-non-var (node)
  (loop-over-nodes-excluding (u node e-node-eqclass)
    (unless (e-node-variable u) (return t))))

;;; =============== End of Equivalence with Instantiations  ===============
