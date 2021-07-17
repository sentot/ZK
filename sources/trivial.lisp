
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

;;; Main functionalities implemented:
;;; - Trivial Reduction
;;; - Expansion/Unexpansion of logical connectives and integer
;;;   operators.

;;; =============== Trivial Reduction ===============

;;;
;;; The trivial simplifier is similar to the full simplifier but
;;; but without equality reasoning, integer reasoning, quantifier
;;; reasoning, and applications of frules and grules.
;;;
;;; The trivial rewriter performs leftmost innermost unconditional
;;; rewriting with an optimization due to Gallier-Book. When only
;;; unconditional rewriting is required this can be fast.
;;; 
;;; The trivial reducer "invokes" functions that are enabled and not
;;; recursive, but otherwise does no rewriting or simplification.
;;; ---------------------------------------------------------------------------


;;; ==================== Trivial Simplifier ====================

;;; Only simple lookups of assumptions. Traversal is similar to
;;; the full simplifier.

(defun ls-simplify-formula (formula assumed denied index
                                    &optional bool-p prop-only-p)
  ;; NOTE: bool-p must be non-nil if prop-only-p is non-nil
  (cond	((literal-p formula) formula)
	((atom formula) (ls-lookup formula assumed denied index bool-p))
	((if-p formula)
	 (let ((test (ls-simplify-formula
		      (if-test formula) assumed denied (if-test-index)
		      (make-context-for-bool-p formula index)
		      prop-only-p)))
	   (ls-simplify-if-parts
	    test (if-left formula) (if-right formula) assumed denied index
	    bool-p
	    prop-only-p)))
        (prop-only-p (ls-lookup formula assumed denied index bool-p))
        ((all-p formula)
         ;; NOTE: This assumes that the formula is not a subformula
         ;; of a bigger formula where the quantified variable occurs free.
         (make-all (all-vars formula)
                   (ls-simplify-formula
                    (all-expr formula) assumed denied (all-expr-index)
		    (make-context-for-bool-p formula index)
		    nil)))
        ((some-p formula)
         ;; NOTE: This assumes that the formula is not a subformula
         ;; of a bigger formula where the quantified variable occurs free.
         (make-some (some-vars formula)
                    (ls-simplify-formula
                     (some-expr formula) assumed denied (some-expr-index)
		     (make-context-for-bool-p formula index)
		     nil)))
	(t
	 (let ((simplified
		(cons (car formula)
		      (loop for expr in (cdr formula)
			    for number = 1 then (+ 1 number)
			    collect (ls-simplify-formula
				     expr assumed denied (cons number index)
				     nil nil)))))
	   (ls-lookup simplified assumed denied index bool-p)))))


;;; The test part is already simplified but not the left and right.
(defun ls-simplify-if-parts (test left right assumed denied index
                                  &optional bool-p prop-only-p)
  (cond ((true-p test)
         (push-proof-log 'if-true index)
         (ls-simplify-formula left assumed denied index bool-p prop-only-p))
        ((false-p test)
         (push-proof-log 'if-false index)
         (ls-simplify-formula right assumed denied index bool-p prop-only-p))
        ((member-equal test denied)
	 (cond ((bool-p test)
		(log-look-up-false (if-test-index)))
	       (t
		(log-coerce-if-test-to-bool index)
		(log-look-up-false-for-coercion (if-test-index))))

         (push-proof-log 'if-false index)
	 (ls-simplify-formula right assumed denied index bool-p prop-only-p))
	;; NOTE: a slight weakness here; perhaps normalization would be
	;; "trivial" after left and right are simplified but not before.
	((and (if-p test)
	      (or *reduce-normalizes-flag*
		  (if-normalization-trivial-p test left right)))
	 (ls-simplify-normalize-if-parts
          test left right assumed denied index bool-p prop-only-p))
	(t (ls-simplify-reduce-if-parts
	     test
	     (ls-simplify-formula
	      left (cons test assumed) denied (if-left-index)
	      bool-p prop-only-p)
	     (ls-simplify-formula
	      right assumed (cons test denied) (if-right-index)
	      bool-p prop-only-p)
             index bool-p))))

;;; Perform normalization with test being an IF expression.
(defun ls-simplify-normalize-if-parts
  (test left right assumed denied index &optional bool-p prop-only-p)
  (let ((test-test (if-test test)))
    (push-proof-log 'case-analysis index 1)
    (ls-simplify-reduce-if-parts
      test-test
      (ls-simplify-if-parts (if-left test) left right
                            (cons test-test assumed) denied
                            (if-left-index) bool-p prop-only-p)
      (ls-simplify-if-parts (if-right test) left right
                            assumed (cons test-test denied)
                             (if-right-index) bool-p prop-only-p)
      index bool-p)))

;;; With test, left and right all reduced, do final reduction based
;;; on two simple rules.
(defun ls-simplify-reduce-if-parts (test left right index &optional bool-p)
  (cond ((and (true-p left) (false-p right) (or bool-p (bool-p test)))
	 (log-remove-coercion-for-boolean-or-bool-p test index bool-p)
         test)
	((equal left right)
         (push-proof-log 'if-equal index)
         left)
	(t (make-if test left right))))

;;; The simple lookup of a formula.
(defun ls-lookup (formula assumed denied index &optional bool-p)
  (cond	((member-equal formula assumed)
         (push-proof-log 'look-up index *true*)
         *true*)
	((and (or bool-p (bool-p formula)) (member-equal formula denied))
	 (cond ((bool-p formula)
		(log-look-up-false index))
	       (t
		(log-look-up-false-in-boolean-context bool-p index)
		))
         *false*)
	(t formula)))


;;; ==================== Trivial Rewriter ====================

;;; List of rules applied by uc-rewrite-formula.
(defvar *list-of-rules* nil)

;;; Perform unconditional rewrite with the list of substitutions using
;;; the Gallier-Book technique. The function returns two values: 
;;; the result of the rewrite and the list of rules applied.
(defun uc-rewrite-formula (formula substitutions index)
  (let ((*list-of-rules* nil))
    (values (uc-rewrite-formula-aux formula substitutions index)
            *list-of-rules*)))

(defun uc-rewrite-formula-aux (formula substitutions index)
  (loop with (apply-success)
	if (literal-p formula) do (return formula)
	if (atom formula) do (return (binding-of formula substitutions))
	do (multiple-value-setq (formula substitutions apply-success)
	     (uc-apply-rules-formula
              (loop for expr in formula
                  for number = 0 then (+ 1 number)
                  collect (uc-rewrite-formula-aux
                           expr substitutions (cons number index)))
              index))
	when (not apply-success) do (return formula)))

;;; Single level rewriting of formula. Does not "dive" into formula
;;; to apply rewrite rules.
(defun uc-apply-rules-formula (formula index)
  (loop	for rule in (get-rules formula)
	when (and (rule-enabled rule)
		  (not (rule-conditional rule))
		  (not (event-inaccessible-p rule)))
	  do ;; ignore rules which are disabled or are conditional
	    (multiple-value-bind (substitutions match-success)
		(match-pattern-formula (rule-pattern rule) formula)
	      (when (and match-success
			 (or (not (rule-permutative rule))
			     ;; permutative rules have to produce lrpo<
			     (lrpo> formula
				    (sublis-eq substitutions (rule-value rule))
				    nil)))
		(log-use-axiom index (internal-name (rule-name rule)))
                (let* ((right-index (cons 2 (repeat-all-expr-index
                                             (length (rule-args rule))
                                             (if-test-index))))
                       (renamed (conditionally-rename-quantified-variables
                                 (rule-valbound rule)
                                 (rule-value rule)
                                 right-index))
                       (unrenames (mapcar #'(lambda (x)
                                              (cons (cdr x) (car x)))
                                          (rule-renames rule)))
                       (unrenamed-substitutions
                        (mapcar #'(lambda (x)
                                    (make-= (binding-of (car x) unrenames)
                                            (cdr x)))
                                (reorder-substitutions
                                 substitutions
                                 ;;(sublis-eq (rule-renames rule)
                                 ;;           (rule-args rule))
				 (mapcar #'cdr (rule-renames rule))
				 ))))
		  (log-rewrite
		   (make-if (make-series-of-quantification
			     'all
			     (mapcar #'=-left unrenamed-substitutions)
			     (sublis-eq unrenames
					(make-= (rule-pattern rule) renamed)))
			    formula
			    *true*)
		   unrenamed-substitutions
		   index)
		  (log-unrenames (rule-value rule) renamed right-index)
		  (push-proof-log 'use-axiom (if-test-index)
				  (internal-name (rule-name rule)) t)
		  (push-proof-log 'if-true index)
                  (or (member-eq rule *list-of-rules*)
                      (push rule *list-of-rules*))
                  (return (values renamed substitutions rule)))))
	finally (return (values formula nil nil))))	;failure


;;; ==================== Trivial Reducer ====================

;;; Replaces applications of non-recursive functions with
;;; appropriate instances of their definitions.

;;; Memo of already reduced subexpressions.
(defvar *tr-reduced-formulas* nil)

;;; List of function names invoked.
(defvar *list-of-names* nil)

(defun tr-reduce-formula (formula index)
  (let ((*list-of-names* nil))
    (values (tr-reduce-formula-aux formula index) *list-of-names*)))

;;; The reduction is performed innermost-first.
(defun tr-reduce-formula-aux (formula index)
  (cond ((atom formula) formula)
	((member-eq formula *tr-reduced-formulas*) formula)
  	(t (let* ((reduced-args
                  (loop for expr in (cdr formula)
                      for number = 1 then (+ 1 number)
                      collect (tr-reduce-formula-aux
                               expr (cons number index))))
		  (name (car formula))
		  (name-event (and (symbolp name)
				   (get-event name))))
	     (if (and (ufunction-p name-event)
		      (not (event-inaccessible-p name-event))
		      (ufunction-internal-body name-event)
		      (ufunction-enabled name-event)
		      (not (ufunction-recursive name-event)))
		 (let ((*tr-reduced-formulas* reduced-args))
                   (or (member-eq name-event *list-of-names*)
                       (push name-event *list-of-names*))
		   (tr-reduce-formula-aux
		    (invoke-single-name name-event
					(cons name reduced-args)
					index)
		    index))
	         (cons name reduced-args))))))


;;; ==================== Expansion/Unexpansion  ====================

;;; Expansions here are right-associated.
;;; Unexpansions are flattening.

;;; -------------------- ANDs

(defun expand-ands (formula index)
  ;; Expansions are performed in the body of expand-ands
  (cond
   ((and-p formula)
    (cond
     ((= (length formula) 3)
      (expand-ands-aux (expand-ands (and-left formula) (and-left-index))
		       (expand-ands (and-right formula) (and-right-index))
		       index))
     ((> (length formula) 3) ; Expansion
      ;; (and a b c ...)
      (push-proof-log 'syntax index)
      ;; (and a (and b c ...))
      (expand-ands-aux (expand-ands (second formula) (and-left-index))
		       (expand-ands (cons 'and (cddr formula))
				    (and-right-index))
		       index))
     ((= (length formula) 2)
      ;; (and a)
      (push-proof-log 'syntax index)
      ;; (and a (true))
      (expand-ands-aux (expand-ands (second formula) (and-left-index))
		       *true*
		       index))
     (t
      ;; (and)
      (log-and-0 index)
      ;; (true)
      *true*)))
   (t formula)))

(defun expand-ands-aux (left right index)
  ;; (and left right)
  ;; Note that left and right are assumed to already be expanded,
  ;; right associated, with no unnecessary (TRUE)s and Boolean
  ;; coercions.
  (cond
   ((and-p left) ; (and (and left1 left2) right)
    (log-associate-and-right (make-and left right) index)
    (make-and
     (and-left left)
     (expand-ands-aux (and-right left) right (and-right-index))))
   ((true-p left) ; (and (true) right)
    (push-proof-log 'syntax index)
    (push-proof-log 'if-true index)
    ;; (if right (true) (false))
    ;; right is known to be an AND, (TRUE), or Boolean coercion.
    (push-proof-log 'is-boolean index t)
    ;; right
    right
    )
   ((and (if-p left) (true-p (if-left left)) (false-p (if-right left)))
    ;; (and (if lefttest (true) (false)) right)
    (push-proof-log 'syntax index)
    ;; (if (if lefttest (true) (false)) (if right (true) (false)) (false))
    (log-remove-bool-coercion-from-if-test index)
    ;; (if lefttest (if right (true) (false)) (false))
    (cond
     ((true-p right)
      (push-proof-log 'if-true (if-left-index))
      ;; (if lefttest (true) (false))
      (cond ((bool-p (if-test left))
	     (push-proof-log 'is-boolean index t)
	     (if-test left))
	    (t left)))
     ((and (if-p right) (true-p (if-left right)) (false-p (if-right right)))
      ;; (if lefttest (if (if righttest (true) (false)) (true) (false)) (false))
      (push-proof-log 'is-boolean (if-left-index) t)
      (push-proof-log 'syntax index t)
      ;; (and lefttest righttest)
      (make-and (if-test left) (if-test right)))
     (t
      (push-proof-log 'syntax index t)
      ;; (and lefttest right)
      (make-and (if-test left) right))))
   ;; *** At this point left is not an AND, (TRUE), or Boolean coercion.
   ((true-p right)
    ;; (and left (true))
    (push-proof-log 'syntax index)
    (push-proof-log 'if-true (if-left-index))
    ;; (if left (true) (false))
    (cond ((bool-p left)
	   (push-proof-log 'is-boolean index t)
	   left)
	  (t (make-if left *true* *false*))))
   ((and (if-p right) (true-p (if-left right)) (false-p (if-right right)))
    ;; (and left (if righttest (true) (false)))
    (push-proof-log 'syntax index)
    ;; (if left (if (if righttest (true) (false)) (true) (false)) (false))
    (push-proof-log 'is-boolean (if-left-index) t)
    (push-proof-log 'syntax index t)
    ;; (and left righttest)
    (make-and left (if-test right)))
   (t (make-and left right))))

(defun flatten-ands (formula index)
  (cond ((and-p formula)
	 (let ((right (flatten-ands (and-right formula) (and-right-index))))
	   (cond ((and-p right)
		  ;; (and left (and ...)
		  (push-proof-log 'syntax index t)
		  (list* 'and (and-left formula) (cdr right)))
		 (t formula))))
	(t formula)))

(defun really-flatten-ands (formula index)
  (flatten-ands (expand-ands formula index) index))


;;; -------------------- ORs

(defun expand-ors (formula index)
  ;; Expansions are performed in the body of expand-ors
  (cond
   ((or-p formula)
    (cond
     ((= (length formula) 3)
      (expand-ors-aux (expand-ors (or-left formula) (or-left-index))
		      (expand-ors (or-right formula) (or-right-index))
		      index))
     ((> (length formula) 3) ; Expansion
      ;; (or a b c ...)
      (push-proof-log 'syntax index)
      ;; (or a (or b c ...))
      (expand-ors-aux (expand-ors (second formula) (or-left-index))
		      (expand-ors (cons 'or (cddr formula))
				  (or-right-index))
		      index))
     ((= (length formula) 2)
      ;; (or a)
      (push-proof-log 'syntax index)
      ;; (or a (false))
      (expand-ors-aux (expand-ors (second formula) (or-left-index))
		      *false*
		      index))
     (t
      ;; (or)
      (log-or-0 index)
      ;; (false)
      *false*)))
   (t formula)))

(defun expand-ors-aux (left right index)
  ;; (or left right)
  ;; Note that left and right are assumed to already be expanded,
  ;; right associated, with no unnecessary (FALSE)s and Boolean
  ;; coercions.
  (cond
   ((or-p left) ; (or (or left1 left2) right)
    (log-associate-or-right (make-or left right) index)
    (make-or
     (or-left left)
     (expand-ors-aux (or-right left) right (or-right-index))))
   ((false-p left) ; (or (false) right)
    (push-proof-log 'syntax index)
    (push-proof-log 'if-false index)
    ;; (if right (true) (false))
    ;; right is known to be an OR, (FALSE), or Boolean coercion.
    (push-proof-log 'is-boolean index t)
    ;; right
    right
    )
   ((and (if-p left) (true-p (if-left left)) (false-p (if-right left)))
    ;; (or (if lefttest (true) (false)) right)
    (push-proof-log 'syntax index)
    ;; (if (if lefttest (true) (false)) (true) (if right (true) (false)))
    (log-remove-bool-coercion-from-if-test index)
    ;; (if lefttest (true) (if right (true) (false)))
    (cond
     ((false-p right)
      (push-proof-log 'if-false (if-right-index))
      ;; (if lefttest (true) (false))
      left)
     ((and (if-p right) (true-p (if-left right)) (false-p (if-right right)))
      ;; (if lefttest (true) (if (if righttest (true) (false)) (true) (false)))
      (push-proof-log 'is-boolean (if-right-index) t)
      (push-proof-log 'syntax index t)
      ;; (or lefttest righttest)
      (make-or (if-test left) (if-test right)))
     (t
      (push-proof-log 'syntax index t)
      ;; (and lefttest right)
      (make-or (if-test left) right))))
   ;; *** At this point left is not an OR, (FALSE), or Boolean coercion.
   ((false-p right)
    ;; (or left (false))
    (push-proof-log 'syntax index)
    (push-proof-log 'if-false (if-right-index))
    ;; (if left (true) (false))
    (make-if left *true* *false*))
   ((and (if-p right) (true-p (if-left right)) (false-p (if-right right)))
    ;; (or left (if righttest (true) (false)))
    (push-proof-log 'syntax index)
    ;; (if left (true) (if (if righttest (true) (false)) (true) (false)))
    (push-proof-log 'is-boolean (if-right-index) t)
    (push-proof-log 'syntax index t)
    ;; (or left righttest)
    (make-or left (if-test right)))
   (t (make-or left right))))

(defun flatten-ors (formula index)
  (cond ((or-p formula)
	 (let ((right (flatten-ors (or-right formula) (or-right-index))))
	   (cond ((or-p right)
		  ;; (or left (or ...)
		  (push-proof-log 'syntax index t)
		  (list* 'or (or-left formula) (cdr right)))
		 (t formula))))
	(t formula)))

(defun really-flatten-ors (formula index)
  (flatten-ors (expand-ors formula index) index))


;;; -------------------- +s

(defun expand-+s (formula index)
  ;; Expansions are performed in the body of expand-+s
  (cond
   ((+-p formula)
    (cond
     ((= (length formula) 3)
      (expand-+s-aux (expand-+s (+-left formula) (cons 1 index))
		     (expand-+s (+-right formula) (cons 2 index))
		     index))
     ((> (length formula) 3) ; Expansion
      ;; (+ a b c ...)
      (push-proof-log 'syntax index)
      ;; (+ a (+ b c ...))
      (expand-+s-aux (expand-+s (second formula) (cons 1 index))
		     (expand-+s (cons '+ (cddr formula)) (cons 2 index))
		     index))
     ((= (length formula) 2)
      ;; (+ a)
      (push-proof-log 'syntax index)
      ;; (+ a 0)
      (log-use-axiom-as-rewrite
       (make-+ (second formula) 0) '+.commutes
       `((= |)X| ,(second formula)) (= |)Y| 0)) index)
      (expand-+s-aux 0 (expand-+s (second formula) (cons 2 index)) index))
     (t
      ;; (+)
      (push-proof-log 'syntax index)
      (push-proof-log 'compute index)
      ;; 0
      0)))
   (t formula)))

(defun expand-+s-aux (left right index)
  ;; (+ left right)
  ;; Note that left and right are assumed to already be expanded,
  ;; right associated, with no unnecessary 0s.
  (cond
   ((+-p left) ; (+ (+ left1 left2) right)
    (log-associate-+-right (make-+ left right) index)
    ;; (+ left1 (+ left2 right))
    (let ((right (expand-+s-aux (+-right left) right (cons 2 index))))
      (cond
       ((equal right 0)
	(cond ((equal (+-left left) 0)
	       (push-proof-log 'compute index)
	       0)
	      (t (log-use-axiom-as-rewrite
		  (make-+ (+-left left) 0) '+.commutes
		  `((= |)X| ,(+-left left)) (= |)Y| 0))
		  index)
		 (make-+ 0 (+-left left)))))
       ((and (+-p right) (equal (+-left right) 0))
	;; (+ left1 (+ 0 rightright))
	(log-use-axiom-as-rewrite
	 (make-+ (+-left left) right) '+.associate.left
	 `((= |)X| ,(+-left left)) (= |)Y| 0) (= |)Z| ,(+-right right))) index)
	(cond ((equal (+-left left) 0)
	       ;; (+ (+ 0 0) rightright)
	       (push-proof-log 'compute (cons 1 index))
	       (make-+ 0 (+-right right)))
	      (t ; (+ (+ left1 0) rightright)
	       (log-use-axiom-as-rewrite
		(make-+ (+-left left) 0) '+.commutes
		`((= |)X| ,(+-left left)) (= |)Y| 0))
		(cons 1 index))
	       ;; (+ (+ 0 left1) rightright)
	       (log-associate-+-right
		(make-+ (make-+ 0 (+-left left)) (+-right right)) index)
	       (make-+ 0 (make-+ (+-left left) (+-right right))))))
       (t (make-+ (+-left left) right)))))
   ((equal left 0) ; (+ 0 right)
    (cond
     ((equal right 0)
      ;; (+ 0 0)
      (push-proof-log 'compute index)
      0)
     ((and (+-p right) (equal (+-left right) 0))
      ;; (+ 0 (+ 0 rightright))
      (log-use-axiom-as-rewrite
       (make-+ left right) '+.associate.left
       `((= |)X| 0) (= |)Y| 0) (= |)Z| ,(+-right right))) index)
      ;; (+ (+ 0 0) rightright)
      (push-proof-log 'compute (cons 1 index))
      ;; (+ 0 rightright)
      right)
     (t (make-+ 0 right))))
   ;; At this point left is neither 0 nor (+ ...).
   ((equal right 0)
    ;; (+ left 0)
    (log-use-axiom-as-rewrite (make-+ left 0) '+.commutes
			      `((= |)X| ,left) (= |)Y| 0)) index)
    ;; (+ 0 left)
    (make-+ 0 left))
   ((and (+-p right) (equal (+-left right) 0))
    ;; (+ left (+ 0 rightright))
    (log-use-axiom-as-rewrite
     (make-+ left right) '+.associate.left
     `((= |)X| ,left) (= |)Y| 0) (= |)Z| ,(+-right right))) index)
    ;; (+ (+ left 0) rightright)
    (log-use-axiom-as-rewrite
     (make-+ left 0) '+.commutes `((= |)X| ,left) (= |)Y| 0)) (cons 1 index))
    ;; (+ (+ 0 left) rightright)
    (log-associate-+-right (make-+ (make-+ 0 left) (+-right right)) index)
    ;; (+ 0 (+ left rightright))
    (make-+ 0 (make-+ left (+-right right))))
   (t (make-+ left right))))

(defun flatten-+s (formula index)
  (cond ((+-p formula)
	 (let ((right (flatten-+s (+-right formula) (cons 2 index))))
	   (cond ((+-p right)
		  ;; (+ left (+ ...)
		  (push-proof-log 'syntax index t)
		  (list* '+ (second formula) (cdr right)))
		 (t formula))))
	(t formula)))

(defun really-flatten-+s (formula index)
  (let ((result (flatten-+s (expand-+s formula index) index)))
    (cond ((and (+-p result) (equal (second result) 0))
	   (cond ((> (length result) 3)
		  (push-proof-log 'syntax index)
		  ;; (+ 0 (+ ....))
		  (let ((rest (cons '+ (cddr result))))
		    (log-use-axiom-as-rewrite
		     `(+ 0 ,rest) '+.zero.left `((= |)X| ,rest)) index)
		    ;; (if (= (type-of (+ ...)) (int)) (+ ...) (+ 0 (+ ...)))
		    (push-proof-log 'compute (cons 1 (if-test-index)))
		    ;; (if (= (int) (int)) (+ ...) (+ 0 (+ ...)))
		    (push-proof-log 'compute (if-test-index))
		    (push-proof-log 'if-true index)
		    ;; (+ ...)
		    rest))
		 ((int-p (third result))
		  (let ((rest (third result)))
		    (log-use-axiom-as-rewrite
		     `(+ 0 ,rest) '+.zero.left `((= |)X| ,rest)) index)
		    ;; (if (= (type-of rest) (int)) rest (+ 0 rest))
		    (push-proof-log 'compute (cons 1 (if-test-index)))
		    ;; (if (= (int) (int)) rest (+ 0 rest))
		    (push-proof-log 'compute (if-test-index))
		    (push-proof-log 'if-true index)
		    ;; rest
		    rest))
		 (t result)))
	  (t result))))


;;; -------------------- *s

(defun expand-*s (formula index)
  ;; Expansions are performed in the body of expand-*s
  (cond
   ((*-p formula)
    (cond
     ((= (length formula) 3)
      (expand-*s-aux (expand-*s (*-left formula) (cons 1 index))
		     (expand-*s (*-right formula) (cons 2 index))
		     index))
     ((> (length formula) 3) ; Expansion
      ;; (* a b c ...)
      (push-proof-log 'syntax index)
      ;; (* a (* b c ...))
      (expand-*s-aux (expand-*s (second formula) (cons 1 index))
		     (expand-*s (cons '* (cddr formula)) (cons 2 index))
		     index))
     ((= (length formula) 2)
      ;; (* a)
      (push-proof-log 'syntax index)
      ;; (* a 1)
      (log-use-axiom-as-rewrite
       (make-* (second formula) 1) '*.commutes
       `((= |)X| ,(second formula)) (= |)Y| 1)) index)
      (expand-*s-aux 1 (expand-*s (second formula) (cons 2 index)) index))
     (t
      ;; (*)
      (push-proof-log 'syntax index)
      (push-proof-log 'compute index)
      ;; 1
      1)))
   (t formula)))

(defun expand-*s-aux (left right index)
  ;; (* left right)
  ;; Note that left and right are assumed to already be expanded,
  ;; right associated, with no unnecessary 1s.
  (cond
   ((*-p left) ; (* (* left1 left2) right)
    (log-associate-*-right (make-* left right) index)
    ;; (* left1 (* left2 right))
    (let ((right (expand-*s-aux (*-right left) right (cons 2 index))))
      (cond
       ((equal right 1)
	(cond ((equal (*-left left) 1)
	       (push-proof-log 'compute index)
	       1)
	      (t (log-use-axiom-as-rewrite
		  (make-* (*-left left) 1) '*.commutes
		  `((= |)X| ,(*-left left)) (= |)Y| 1))
		  index)
		 (make-* 1 (*-left left)))))
       ((and (*-p right) (equal (*-left right) 1))
	;; (* left1 (* 1 rightright))
	(log-use-axiom-as-rewrite
	 (make-* (*-left left) right) '*.associate.left
	 `((= |)X| ,(*-left left)) (= |)Y| 1) (= |)Z| ,(*-right right))) index)
	(cond ((equal (*-left left) 1)
	       ;; (* (* 1 1) rightright)
	       (push-proof-log 'compute (cons 1 index))
	       (make-* 1 (*-right right)))
	      (t ; (* (* left1 1) rightright)
	       (log-use-axiom-as-rewrite
		(make-* (*-left left) 1) '*.commutes
		`((= |)X| ,(*-left left)) (= |)Y| 1))
		(cons 1 index))
	       ;; (* (* 1 left1) rightright)
	       (log-associate-*-right
		(make-* (make-* 1 (*-left left)) (*-right right)) index)
	       (make-* 1 (make-* (*-left left) (*-right right))))))
       (t (make-* (*-left left) right)))))
   ((equal left 1) ; (* 1 right)
    (cond
     ((equal right 1)
      ;; (* 1 1)
      (push-proof-log 'compute index)
      1)
     ((and (*-p right) (equal (*-left right) 1))
      ;; (* 1 (* 1 rightright))
      (log-use-axiom-as-rewrite
       (make-* left right) '*.associate.left
       `((= |)X| 1) (= |)Y| 1) (= |)Z| ,(*-right right))) index)
      ;; (* (* 1 1) rightright)
      (push-proof-log 'compute (cons 1 index))
      ;; (* 1 rightright)
      right)
     (t (make-* 1 right))))
   ;; At this point left is neither 1 nor (* ...).
   ((equal right 1)
    ;; (* left 1)
    (log-use-axiom-as-rewrite (make-* left 1) '*.commutes
			      `((= |)X| ,left) (= |)Y| 1)) index)
    ;; (* 1 left)
    (make-* 1 left))
   ((and (*-p right) (equal (*-left right) 1))
    ;; (* left (* 1 rightright))
    (log-use-axiom-as-rewrite
     (make-* left right) '*.associate.left
     `((= |)X| ,left) (= |)Y| 1) (= |)Z| ,(*-right right))) index)
    ;; (* (* left 1) rightright)
    (log-use-axiom-as-rewrite
     (make-* left 1) '*.commutes `((= |)X| ,left) (= |)Y| 1)) (cons 1 index))
    ;; (* (* 1 left) rightright)
    (log-associate-*-right (make-* (make-* 1 left) (*-right right)) index)
    ;; (* 1 (* left rightright))
    (make-* 1 (make-* left (*-right right))))
   (t (make-* left right))))

(defun flatten-*s (formula index)
  (cond ((*-p formula)
	 (let ((right (flatten-*s (*-right formula) (cons 2 index))))
	   (cond ((*-p right)
		  ;; (* left (* ...)
		  (push-proof-log 'syntax index t)
		  (list* '* (second formula) (cdr right)))
		 (t formula))))
	(t formula)))

(defun really-flatten-*s (formula index)
  (let ((result (flatten-*s (expand-*s formula index) index)))
    (cond ((and (*-p result) (equal (second result) 1))
	   (cond ((> (length result) 3)
		  (push-proof-log 'syntax index)
		  ;; (* 1 (* ....))
		  (let ((rest (cons '* (cddr result))))
		    (log-use-axiom-as-rewrite
		     `(* 1 ,rest) '*.one.left `((= |)X| ,rest)) index)
		    ;; (if (= (type-of (* ...)) (int)) (* ...) (* 1 (* ...)))
		    (push-proof-log 'compute (cons 1 (if-test-index)))
		    ;; (if (= (int) (int)) (* ...) (* 1 (* ...)))
		    (push-proof-log 'compute (if-test-index))
		    (push-proof-log 'if-true index)
		    ;; (* ...)
		    rest))
		 ((int-p (third result))
		  (let ((rest (third result)))
		    (log-use-axiom-as-rewrite
		     `(* 1 ,rest) '*.one.left `((= |)X| ,rest)) index)
		    ;; (if (= (type-of rest) (int)) rest (* 1 rest))
		    (push-proof-log 'compute (cons 1 (if-test-index)))
		    ;; (if (= (int) (int)) rest (* 1 rest))
		    (push-proof-log 'compute (if-test-index))
		    (push-proof-log 'if-true index)
		    ;; rest
		    rest))
		 (t result)))
	  (t result))))
