
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


;;; ========== Proof Logging of Frequently Used Transformations ========

;;; Some transformation patterns occur frequently in the proof logging
;;; process. Most of the functions here implement the proof logging
;;; associated with these transformations. It is mostly mundane
;;; book-keeping.

;;; A couple of utility functions tightly coupled to proof logging at
;;; the end.



;;; Most uses of use-axiom converts expr to (if axiom expr (true)).

(defun log-use-axiom (index axiom)
  (push-proof-log 'if-true index *true* t)
  (push-proof-log 'use-axiom (if-test-index) axiom))

;;; ================= Rewriting ======================

(defun log-rewrite (formula substitutions index)
  (when *record-proof-logs-flag*
    (let ((renames (mapcar #'(lambda (u) (cons (=-left u) (genvar (=-left u))))
			   substitutions)))
      ;; formula is an "if":
      ;; (if axiom expr (true))
      (log-renames renames (if-test-index))
      (log-rewrite-aux
       (make-if (sublis-eq renames (if-test formula))
		(if-left formula)
		(if-right formula))
       (mapcar #'(lambda (u) (make-= (binding-of (=-left u) renames)
				     (=-right u)))
	       substitutions)
       index
       (if-left-index)
       (length substitutions))
      (log-renames (mapcar #'(lambda (u) (cons (cdr u) (car u))) renames)
		   (if-test-index)))))

;;; (if partially-instantiated fully-instantiated (true))
;;; substitutions

(defun log-rewrite-aux (formula substitutions index left-index n)
  (cond ((null substitutions)
         (push-proof-log 'look-up left-index (=-right (if-test formula)))
         (make-if (if-test formula)
                  (log-rewrite-aux-aux (if-left formula)
                                       (=-right (if-test formula))
                                       n)
                  (if-right formula)))
        (t
         (push-proof-log 'instantiate-universal (if-test-index)
                         (car substitutions))
         (push-proof-log 'case-analysis index 1)
         (push-proof-log 'if-false (if-right-index))
         (let ((result
                (log-rewrite-aux
                 (make-if (subst-eq (=-right (car substitutions))
                                    (=-left (car substitutions))
                                    (all-expr (if-test formula)))
                          formula
                          (if-right formula))
                 (cdr substitutions) index (cons 2 left-index) n)))
           (push-proof-log 'if-false (if-right-index)
			   (if-left (if-left result)) t)
           (push-proof-log 'case-analysis index 1 t)
           (push-proof-log 'instantiate-universal
                           (if-test-index)
                           (car substitutions)
			   t)
	   (if-left result)
	   ))))

(defun log-rewrite-aux-aux (formula replacement n)
  (cond ((zerop n) replacement)
        (t (make-if (if-test formula)
                    (log-rewrite-aux-aux (if-left formula) replacement (- n 1))
                    (if-right formula)))))

;;; Log the transformation of expr using an axiom as a rewrite rule.
;;; The instances must be given because they might not be in the pattern.
;;; axiom here is the name of the axiom

(defun log-use-axiom-as-rewrite (expr axiom substitutions index)
  (when *record-proof-logs-flag*
    (let ((formula (get-axiom axiom)))
      (push-proof-log 'marker index (list 'start 'axiom-as-rewrite axiom))
      (log-use-axiom index axiom)
      (log-rewrite (make-if formula expr *true*) substitutions index)
      (push-proof-log 'use-axiom (if-test-index) axiom t)
      (push-proof-log 'if-true index)
      (push-proof-log 'marker index (list 'end 'axiom-as-rewrite axiom))
      )))


(defun log-use-axiom-as-inverse-rewrite (axiom left right substitutions index)
  ;; right
  (push-proof-log 'if-equal index (make-= left right) t)
  ;; (if (= left right) right right)
  (push-proof-log 'look-up (if-left-index) left)
  ;; (if (= left right) left right)
  (log-use-axiom-as-rewrite left axiom substitutions (cons 1 (if-test-index)))
  ;; (if (= right right) left right)
  (push-proof-log 'compute (if-test-index))
  (push-proof-log 'if-true index)
  ;; left
  )


;;; ========== Associative and commutative transformations ======

;;; (and a (and b c)) => (and (and a b) c)

(defun log-associate-and-left (formula index)
  (let ((a (and-left formula))
	(b (and-left (and-right formula)))
	(c (and-right (and-right formula))))
    (log-use-axiom-as-rewrite
     formula 'and.associative
     `((= |)X| ,a) (= |)Y| ,b) (= |)Z| ,c)) index)))

;;; (and (and a b) c) => (and a (and b c))

(defun log-associate-and-right (formula index)
  (let ((a (and-left (and-left formula)))
	(b (and-right (and-left formula)))
	(c (and-right formula)))
    (let ((result (make-and a (make-and b c))))
      (log-use-axiom-as-inverse-rewrite
       'and.associative result formula
       `((= |)X| ,a) (= |)Y| ,b) (= |)Z| ,c)) index))))

;;; (or a (or b c)) => (or (or a b) c)

(defun log-associate-or-left (formula index)
  (let ((a (or-left formula))
	(b (or-left (or-right formula)))
	(c (or-right (or-right formula))))
    (log-use-axiom-as-rewrite
     formula 'or.associative
     `((= |)X| ,a) (= |)Y| ,b) (= |)Z| ,c)) index)))

;;; (or (or a b) c) => (or a (or b c))

(defun log-associate-or-right (formula index)
  (let ((a (or-left (or-left formula)))
	(b (or-right (or-left formula)))
	(c (or-right formula)))
    (let ((result (make-or a (make-or b c))))
      (log-use-axiom-as-inverse-rewrite
       'or.associative result formula
       `((= |)X| ,a) (= |)Y| ,b) (= |)Z| ,c)) index))))

;;; (+ a (+ b c)) => (+ (+ a b) c)

(defun log-associate-+-left (formula index)
  (let ((a (+-left formula))
	(b (+-left (+-right formula)))
	(c (+-right (+-right formula))))
    (log-use-axiom-as-rewrite
     formula '+.associate.left
     `((= |)X| ,a) (= |)Y| ,b) (= |)Z| ,c)) index)))

;;; (+ (+ a b) c) => (+ a (+ b c))

(defun log-associate-+-right (formula index)
  (let ((a (+-left (+-left formula)))
	(b (+-right (+-left formula)))
	(c (+-right formula)))
    (log-use-axiom-as-rewrite
     formula '+.associate.right
     `((= |)X| ,a) (= |)Y| ,b) (= |)Z| ,c)) index)))

;;; (* a (* b c)) => (* (* a b) c)

(defun log-associate-*-left (formula index)
  (let ((a (*-left formula))
	(b (*-left (*-right formula)))
	(c (*-right (*-right formula))))
    (log-use-axiom-as-rewrite
     formula '*.associate.left
     `((= |)X| ,a) (= |)Y| ,b) (= |)Z| ,c)) index)))

;;; (* (* a b) c) => (* a (* b c))

(defun log-associate-*-right (formula index)
  (let ((a (*-left (*-left formula)))
	(b (*-right (*-left formula)))
	(c (*-right formula)))
    (log-use-axiom-as-rewrite
     formula '*.associate.right
     `((= |)X| ,a) (= |)Y| ,b) (= |)Z| ,c)) index)))

;;; (op a b) => (op b a)

(defun log-commute (expr index)
  (let ((a (second expr))
	(b (third expr))
	(axiom (cond ((eq (car expr) 'and) 'and.commutative)
		     ((eq (car expr) 'or) 'or.commutative)
		     ((eq (car expr) '+) '+.commutes)
		     ((eq (car expr) '*) '*.commutes)
		     ((eq (car expr) '=) '=.commutes))))
    (unless (null axiom)
      (log-use-axiom-as-rewrite
       expr axiom `((= |)X| ,a) (= |)Y| ,b)) index))))

;;; (op x (op y z)) => (op y (op x z))

(defun log-permute (expr index)
  (let ((x (second expr))
	(y (second (third expr)))
	(z (third (third expr))))
    (cond ((and-p expr)
	   (log-associate-and-left expr index)
	   (log-commute (make-and x y) (cons 1 index))
	   (log-associate-and-right (make-and (make-and y x) z) index))
	  ((or-p expr)
	   (log-associate-or-left expr index)
	   (log-commute (make-or x y) (cons 1 index))
	   (log-associate-or-right (make-or (make-or y x) z) index))
	  ((+-p expr)
	   (log-associate-+-left expr index)
	   (log-commute (make-+ x y) (cons 1 index))
	   (log-associate-+-right (make-+ (make-+ y x) z) index))
	  ((*-p expr)
	   (log-associate-*-left expr index)
	   (log-commute (make-* x y) (cons 1 index))
	   (log-associate-*-right (make-* (make-* y x) z) index)))))

;;; ============= Renaming quantified variables ================


;;; function to log a sequence of renamings
;;; This assumes that index points to (all (x) (all (y) ...))
;;; where ((x . a) (y . b) ....) is the list renames.

(defun log-renames (renames index)
  (when *record-proof-logs-flag*
    (unless (null renames)
      (push-proof-log 'rename-universal index (caar renames) (cdar renames))
      (log-renames (cdr renames) (all-expr-index)))))


;;; This seems to only be used in induction.lisp
;;; Note that source and target must match exactly.

(defun log-renames-unexpanded (source target index)
  (cond ((all-p source)
         (cond ((> (length (all-vars source)) 1)
                (push-proof-log 'syntax index)
                (push-proof-log
                 'rename-universal index
		 (car (all-vars source)) (car (all-vars target)))
                (log-renames-unexpanded
                 (make-all (cdr (all-vars source)) (all-expr source))
		 (make-all (cdr (all-vars target)) (all-expr target))
                 (all-expr-index))
                (push-proof-log 'syntax index t))
               (t
                (push-proof-log
                 'rename-universal index (all-var source) (all-var target)))))
        ((some-p source)
         (cond ((> (length (some-vars source)) 1)
		(log-expand-some index)
                (log-rename-existential
		 (car (some-vars source)) (car (some-vars target)) index)
                (log-renames-unexpanded
                 (make-some (cdr (some-vars source)) (some-expr source))
		 (make-some (cdr (some-vars target)) (some-expr target))
                 (some-expr-index))
                (log-unexpand-some index))
               (t
                (log-rename-existential
		 (all-var source) (all-var target) index))))
        ((consp source)
	 (loop for src in source
               for tgt in target
               for number = 0 then (+ 1 number)
	       do (log-renames-unexpanded src tgt (cons number index))))))

;;; this assumes that both original and renamed are expanded in
;;; terms of quantification.

(defun log-unrenames (original renamed index)
  (cond ((all-p original)
         (when (neq (all-var original) (all-var renamed))
           (push-proof-log 'rename-universal index (all-var renamed)
                           (all-var original)))
         (log-unrenames (all-expr original) (all-expr renamed)
                        (all-expr-index)))
        ((some-p original)
         (when (neq (some-var original) (some-var renamed))
           (log-rename-existential (some-var renamed) (some-var original)
				   index))
         (log-unrenames (some-expr original) (some-expr renamed)
                        (some-expr-index)))
        ((consp original)
	 (loop for orig in original
               for ren in renamed
               for number = 0 then (+ 1 number)
	       do (log-unrenames orig ren (cons number index))))))

;;; ==================== Expansion/Unexpansion ======================

;;; Probably only used in interface.lisp
;;; Move back to interface.lisp and FIX! ***

(defun log-unexpands (original index)
  (unless (atom original)
    (let ((function (car original)))
      ;; must treat quantifiers specially
      (cond ((and (all-p original) (> (length (all-vars original)) 1))
             (dolist (i (cdr (all-vars original)))
               i (push-proof-log 'syntax index t))
             (log-unexpands (all-expr original) (all-expr-index)))
            ((and (some-p original) (> (length (some-vars original)) 1))
             (dolist (i (cdr (some-vars original)))
               i (log-unexpand-some index))
             (log-unexpands (some-expr original) (all-expr-index)))
            ((and (symbolp function)
                  (function-stub-p (get-event function))
                  (expand-p function)
                  (> (length (cdr original))
                     (length (function-stub-args (get-event function)))))
	     (log-unexpands (second original) (cons 1 index))
	     (log-unexpands
	      (cons (car original) (cddr original))
	      (cons 2 index))
	     (push-proof-log 'syntax index t))
            (t (loop for orig in original
                   for number = 0 then (+ 1 number)
                   do (log-unexpands orig (cons number index))))))))

(defun log-expand-some (index)
  ;; (some (x1 x1 ...) expr)
  (push-proof-log 'syntax index)
  ;; (not (all (x1 x2 ...) (not expr)))
  (push-proof-log 'syntax (not-expr-index))
  ;; (not (all (x1) (all (x2 ...) (not expr))))
  (push-proof-log 'is-boolean (cons 2 (not-expr-index)))
  ;; (not (all (x1) (if (all (x2 ...) (not expr)) (true) (false)))
  (log-bool-coercion-is-double-negation (cons 2 (not-expr-index)))
  ;; (not (all (x1) (if (if (all (x2 ...) (not expr)) (false) (true))
  ;;                    (false)
  ;;                    (true))))
  (push-proof-log 'syntax (cons 2 (not-expr-index)) t)
  ;; (not (all (x1) (not (if (all (x2 ...) (not expr)) (false) (true)))))
  (push-proof-log 'syntax index t)
  ;; (some (x1) (if (all (x2 ...) (not expr)) (false) (true)))
  (push-proof-log 'syntax (some-expr-index) t)
  ;; (some (x1) (not (all (x2 ...) (not expr))))
  (push-proof-log 'syntax (some-expr-index) t)
  ;; (some (x1) (some (x2 ...) expr))
  )

(defun log-unexpand-some (index)
  ;; (some (x1) (some (x2 ...) expr))
  (push-proof-log 'syntax (some-expr-index))
  ;; (some (x1) (not (all (x2 ...) (not expr))))
  (push-proof-log 'syntax (some-expr-index))
  ;; (some (x1) (if (all (x2 ...) (not expr)) (false) (true)))
  (push-proof-log 'syntax index)
  ;; (not (all (x1) (not (if (all (x2 ...) (not expr)) (false) (true)))))
  (push-proof-log 'syntax (cons 2 (not-expr-index)))
  ;; (not (all (x1) (if (if (all (x2 ...) (not expr)) (false) (true))
  ;;                    (false)
  ;;                    (true))))
  (log-double-negation-is-coercion (cons 2 (not-expr-index)))
  ;; (not (all (x1) (if (all (x2 ...) (not expr)) (true) (false)))
  (push-proof-log 'is-boolean (cons 2 (not-expr-index)) t)
  ;; (not (all (x1) (all (x2 ...) (not expr))))
  (push-proof-log 'syntax (not-expr-index) t)
  ;; (not (all (x1 x2 ...) (not expr)))
  (push-proof-log 'syntax index t)
  ;; (some (x1 x1 ...) expr)
  )


;;; (implies a (implies b c)) => (implies (and a b) c)

(defun log-unnest-implies (c index)
  (let ((coerced-c (make-if c *true* *false*)))
    ;; (implies a (implies b c))
    (push-proof-log 'syntax (implies-right-index))
    (push-proof-log 'syntax index)
    ;; (if a (if (if b coerced-c (true)) (true) (false)) (true))
    (log-coerce-if-test-to-bool (cons 1 (if-left-index)))
    ;; (if a (if (if coerced-b coerced-c (true)) (true) (false)) (true))
    (push-proof-log 'is-boolean (if-left-index) t)
    ;; (if a (if coerced-b coerced-c (true)) (true))
    (push-proof-log 'if-false (if-right-index) coerced-c t)
    ;; (if a
    ;;     (if coerced-b coerced-c (true))
    ;;     (if (false) coerced-c (true)))
    (push-proof-log 'case-analysis index 1 t)
    ;; (if (if a coerced-b (false)) coerced-c (true))
    (push-proof-log 'syntax (if-test-index) t)
    ;; (if (and a b) coerced-c (true))
    (push-proof-log 'syntax index t)
    ;; (implies (and a b) c)
    ))

;;; ================== Equality =================

(defun log-equality-substitute (formula old new index)
  (when *record-proof-logs-flag*
    (cond ((equal formula old)
	   (push-proof-log 'look-up index new))
	  ((or (all-p formula) (some-p formula))
	   (log-equality-substitute
	    (car (last formula)) old new (all-expr-index)))
	  ((consp formula)
	   (loop for expr in (cdr formula)
		 for i = 1 then (+ i 1)
		 do (log-equality-substitute expr old new (cons i index)))))))

(defun log-true-to-= (expr index)
  ;; (true)
  (push-proof-log 'if-equal index (make-= expr expr) t)
  ;; (if (= expr expr) (true) (true))
  (push-proof-log 'look-up (if-left-index) (make-= expr expr))
  (push-proof-log 'compute (if-test-index))
  ;; (if (true) (= expr expr) (true))
  (push-proof-log 'if-true index)
  ;; (= expr expr)
  )

;;; ================== Special IF Conversions =================

(defun log-convert-if-test-left-true (left index)
  ;; (if test left (true))
  (push-proof-log 'if-false (if-left-index) *true* t)
  (push-proof-log 'if-true (if-right-index) left t)
  ;; (if test (if (false) (true) left) (if (true) (true) left)
  (push-proof-log 'case-analysis index 1 t)
  ;; (if (if test (false) (true)) (true) left)
  )

(defun log-convert-if-test-true-right (right index)
  ;; (if test (true) right)
  (push-proof-log 'if-false (if-left-index) right t)
  (push-proof-log 'if-true (if-right-index) *true* t)
  ;; (if test (if (false) right (true)) (if (true) right (true))
  (push-proof-log 'case-analysis index 1 t)
  ;; (if (if test (false) (true)) right (true))
  )

(defun log-convert-if-test-left-false (left index)
  ;; (if test left (false))
  (push-proof-log 'if-false (if-left-index) *false* t)
  (push-proof-log 'if-true (if-right-index) left t)
  ;; (if test (if (false) (false) left) (if (true) (false) left)
  (push-proof-log 'case-analysis index 1 t)
  ;; (if (if test (false) (true)) (false) left)
  )

(defun log-convert-if-test-false-right (right index)
  ;; (if test (false) right)
  (push-proof-log 'if-false (if-left-index) right t)
  (push-proof-log 'if-true (if-right-index) *false* t)
  ;; (if test (if (false) right (false)) (if (true) right (false))
  (push-proof-log 'case-analysis index 1 t)
  ;; (if (if test (false) (true)) right (false))
  )

(defun log-if-to-and-not (formula index)
  ;; (if a (false) (if b (true) (false)))
  (push-proof-log 'if-false (if-left-index) (if-right formula) t)
  (push-proof-log 'if-true (if-right-index) *false* t)
  ;; (if a
  ;;     (if (false) (if b (true) (false)) (false))
  ;;     (if (true) (if b (true) (false)) (false)))
  (push-proof-log 'case-analysis index 1 t)
  ;; (if (if a (false) (true)) (if b (true) (false)) (false))
  (push-proof-log 'syntax index t)
  (push-proof-log 'syntax (and-left-index) t)
  ;; (and (not a) b)
  )

;;; =================== Quantifiers =================


;;; instantiate-existential (= x a)

(defun log-instantiate-existential (instantiation index)
  ;; (some (x) P[x])
  (push-proof-log 'syntax index)
  ;; (not (all (x) (not P[x])))
  (push-proof-log 'instantiate-universal (not-expr-index) instantiation)
  ;; (not (if (not P[a]) (all (x) (not P[x])) (false)))
  (push-proof-log 'syntax index)
  ;; (if (if (not P[a]) (all (x) (not P[x])) (false)) (false) (true))
  (push-proof-log 'case-analysis index 1)
  ;; (if (not P[a])
  ;;     (if (all (x) (not P[x])) (false) (true))
  ;;     (if (false) (false) (true)))
  (push-proof-log 'syntax (if-test-index))
  ;; (if (if P[a] (false) (true))
  ;;     (if (all (x) (not P[x])) (false) (true))
  ;;     (if (false) (false) (true)))
  (push-proof-log 'case-analysis index 1)
  ;; (if P[a]
  ;;     (if (false)
  ;;         (if (all (x) (not P[x])) (false) (true))
  ;;         (if (false) (false) (true)))
  ;;     (if (true)
  ;;         (if (all (x) (not P[x])) (false) (true))
  ;;         (if (false) (false) (true))))
  (push-proof-log 'if-false (if-left-index))
  (push-proof-log 'if-true (if-right-index))
  ;; (if P[a}
  ;;     (if (false) (false) (true))
  ;;     (if (all (x) (not P[x])) (false) (true)))
  (push-proof-log 'if-false (if-left-index))
  (push-proof-log 'syntax (if-right-index) t)
  ;; (if P[a] (true) (not (all (x) (not P[x]))))
  (push-proof-log 'syntax (if-right-index) t)
  ;; (if P[a] (true) (some (x) P[x]))
  )

(defun log-uninstantiate-existential (instantiation index)
  ;; (if P[a] (true) (some (x) P[x]))
  (push-proof-log 'syntax (if-right-index))
  (push-proof-log 'syntax (if-right-index))
  ;; (if P[a] (true) (if (all (x) (not P[x])) (false) (true)))
  (push-proof-log 'if-false (if-left-index) *false* t)
  ;; (if P[a]
  ;;     (if (false) (false) (true))
  ;;     (if (all (x) (not P[x])) (false) (true)))
  (push-proof-log 'case-analysis index 1 t)
  ;; (if (if P[a] (false) (all (x) (not P[x])))
  ;;     (false)
  ;;     (true))
  (log-coerce-if-test-to-bool (if-test-index))
  ;; (if (if (if P[a] (true) (false)) (false) (all (x) (not P[x])))
  ;;     (false)
  ;;     (true))
  (log-bool-coercion-is-double-negation (cons 1 (if-test-index)))
  ;; (if (if (if (if P[a] (false) (true)) (false) (true))
  ;;         (false)
  ;;         (all (x) (not P[x])))
  ;;     (false)
  ;;     (true))
  (push-proof-log 'case-analysis (if-test-index) 1)
  (push-proof-log 'syntax index t)
  ;; (not (if (if P[a] (false) (true))
  ;;          (if (false) (false) (all (x) (not P[x])))
  ;;          (if (true) (false) (all (x) (not P[x])))))
  (push-proof-log 'syntax (cons 1 (not-expr-index)) t)
  (push-proof-log 'if-false (cons 2 (not-expr-index)))
  (push-proof-log 'if-true (cons 3 (not-expr-index)))
  ;; (not (if (not P[a]) (all (x) (not P[x])) (false)))
  (push-proof-log 'instantiate-universal (not-expr-index) instantiation t)
  ;; (not (all (x) (not P[x])))
  (push-proof-log 'syntax index t)
  ;; (some (x) P[x])
  )


(defun log-flip-existentials (index)
  ;; (some (x) (some (y) P))
  (push-proof-log 'syntax index)
  ;; (not (all (x) (not (some (y) P))))
  (push-proof-log 'syntax (list* 1 2 (not-expr-index)))
  ;; (not (all (x) (not (not (all (y) (not P))))))
  (log-not-not (cons 2 (not-expr-index)))
  ;; (not (all (x) (if (all (y) (not P)) (true) (false))))
  (push-proof-log 'is-boolean (cons 2 (not-expr-index)) t)
  ;; (not (all (x) (all (y) (not P))))
  (push-proof-log 'flip-universals (not-expr-index))
  ;; (not (all (y) (all (x) (not P))))
  (push-proof-log 'is-boolean (cons 2 (not-expr-index)))
  ;; (not (all (y) (if (all (x) (not P)) (true) (false))))
  (log-bool-coercion-is-double-negation (cons 2 (not-expr-index)))
  ;; (not (all (y) (if (if (all (x) (not P)) (false) (true)) (false) (true))))
  (push-proof-log 'syntax (list* 1 2 (not-expr-index)) t)
  (push-proof-log 'syntax (cons 2 (not-expr-index)) t)
  ;; (not (all (y) (not (not (all (x) (not P))))))
  (push-proof-log 'syntax (list* 1 2 (not-expr-index)) t)
  ;; (not (all (y) (not (some (x) P))))
  (push-proof-log 'syntax index t)
  ;; (some (y) (some (x) P))
  )


(defun log-some-to-if-form (index)
  ;; (some vars expr)
  (push-proof-log 'syntax index)
  ;; (not (all vars (not expr)))
  (push-proof-log 'syntax index)
  ;; (if (all vars (not expr)) (false) (true))
  (push-proof-log 'syntax (cons 2 (if-test-index)))
  ;; (if (all vars (if expr (false) (true))) (false) (true))
  )

(defun log-if-form-to-some (index)
  ;; (if (all vars (if expr (false) (true))) (false) (true))
  (push-proof-log 'syntax (cons 2 (if-test-index)) t)
  ;; (if (all vars (not expr)) (false) (true))
  (push-proof-log 'syntax index t)
  ;; (not (all vars (not expr)))
  (push-proof-log 'syntax index t)
  ;; (some vars expr)
  )

;;; function to log universal subsumption
;;; e.g. (if (P a b) (all (x) (all (y) (P x y))) (false)) =>
;;;         (all (x) (all (y) (P x y)))
;;; with the instantiations ((= x a) (= y b))

(defun log-universal-subsumption (formula instantiations index)
  (when *record-proof-logs-flag*
  (unless (null instantiations)
    (unless (null (cdr instantiations))
      (push-proof-log 'if-false (if-right-index) (if-left formula) t)
      (push-proof-log 'instantiate-universal (if-left-index)
                      (car instantiations))
      (push-proof-log 'case-analysis index 1 t))
    (log-universal-subsumption
     (make-if (if-test formula)
              (sublis-eq (list (cons (=-left (car instantiations))
                                     (=-right (car instantiations))))
                         (all-expr (if-left formula)))
              *false*)
     (cdr instantiations)
     (if-test-index))
    (push-proof-log 'instantiate-universal index (car instantiations) t))))


(defun log-existential-subsumption (formula instantiations index)
  (when *record-proof-logs-flag*
    (unless (null instantiations)
      (unless (null (cdr instantiations))
	(push-proof-log 'if-true (if-left-index) (if-right formula) t)
	(log-instantiate-existential (car instantiations) (if-right-index))
	(push-proof-log 'case-analysis index 1 t))
      (log-existential-subsumption
       (make-if (if-test formula)
		*true*
		(sublis-eq (list (cons (=-left (car instantiations))
				       (=-right (car instantiations))))
			   (if-right formula)))
       (cdr instantiations)
       (if-test-index))
      (log-uninstantiate-existential (car instantiations) index))))

(defun log-rename-existential (old new index)
  ;; (some (old) P[old])
  (push-proof-log 'syntax index)
  ;; (not (all (old) (not P[old])))
  (push-proof-log 'rename-universal (not-expr-index) old new)
  (push-proof-log 'syntax index t)
  ;; (some (new) P[new])
  )

(defun log-remove-existential (index)
  (when *record-proof-logs-flag*
    ;; (some vars expr)
    (log-some-to-if-form index)
    ;; (if (all vars (if expr (false) (true))) (false) (true))
    (push-proof-log 'remove-universal (if-test-index))
    ;; (if (if (if expr (false) (true)) (true) (false))
    ;;     (false)
    ;;     (true))
    (push-proof-log 'case-analysis (if-test-index) 1)
    ;; (if (if expr
    ;;         (if (false) (true) (false))
    ;;         (if (true) (true) (false)))
    ;;     (false)
    ;;     (true))
    (push-proof-log 'if-false (cons 2 (if-test-index)))
    ;; (if (if expr (false) (if (true) (true) (false)))
    ;;     (false)
    ;;     (true))
    (push-proof-log 'if-true (cons 3 (if-test-index)))
    ;; (if (if expr (false) (true)) (false) (true))
    (push-proof-log 'case-analysis index 1)
    ;; (if expr (if (false) (false) (true)) (if (true) (false) (true)))
    (push-proof-log 'if-false (if-left-index))
    ;; (if expr (true) (if (true) (false) (true)))
    (push-proof-log 'if-true (if-right-index))
    ;; (if expr (true) (false))
    ))

(defun log-introduce-existential (vars index)
  ;; (if expr (true) (false))  => (some vars expr)
  ;; where vars do not occur free in expr
  (push-proof-log 'if-true (if-right-index) *true* t)
  ;; (if expr (true) (if (true) (false) (true)))
  (push-proof-log 'if-false (if-left-index) *false* t)
  ;; (if expr (if (false) (false) (true)) (if (true) (false) (true)))
  (push-proof-log 'case-analysis index 1 t)
  ;; (if (if expr (false) (true)) (false) (true))
  (push-proof-log 'if-true (cons 3 (if-test-index)) *false* t)
  (push-proof-log 'if-false (cons 2 (if-test-index)) *true* t)
  (push-proof-log 'case-analysis (if-test-index) 1 t)
  ;; (if (if (if expr (false) (true)) (true) (false)) (false) (true))
  (push-proof-log 'remove-universal (if-test-index) vars t)
  (log-if-form-to-some index)
  ;; (some vars expr)

  )


;;; (all vars (if a b c)) => (if a (all vars b) (all vars c))
;;; vars do not occur free in a

(defun log-all-case-analysis-1 (formula index)
  ;; formula is of the form (all vars (if a b c))
  ;; where the variables in vars do not occur free in a.

  ;; (all vars (if a b c))

  (push-proof-log 'if-equal index (if-test (all-expr formula)) t)
  ;; (if a (all vars (if a b c)) (all vars (if a b c)))
  (push-proof-log 'look-up (list* 1 2 (if-left-index)) *true*)
  (push-proof-log 'if-true (cons 2 (if-left-index)))
  ;; (if a (all vars b) (all vars (if a b c)))
  (log-coerce-if-test-to-bool (cons 2 (if-right-index)))
  ;; (if a (all vars b) (all vars (if (if a (true) (false)) b c)))
  (log-bool-coercion-is-double-negation (list* 1 2 (if-right-index)))
  ;; (if a
  ;;     (all vars b)
  ;;     (all vars (if (if (if a (false) (true)) (false) (true)) b c)))
  (push-proof-log 'look-up (list* 1 1 2 (if-right-index)) *true*)
  ;; (if a
  ;;     (all vars b)
  ;;     (all vars (if (if (true) (false) (true)) b c)))
  (push-proof-log 'if-true (list* 1 2 (if-right-index)))
  ;; (if a
  ;;     (all vars b)
  ;;     (all vars (if (false) b c)))
  (push-proof-log 'if-false (cons 2 (if-right-index)))
  ;; (if a (all vars b) (all vars c))
  )


;;; (all vars (if a b (true)))
;;;    => (if (some vars a) (if b (true) (false)) (true))
;;; vars do not occur free in b

(defun log-all-case-analysis-2 (formula index)
  ;; (all vars (if a b (true)))
  (let ((test (if-test (all-expr formula))) ; a
	(left (if-left (all-expr formula)))) ; b
    (push-proof-log 'if-equal index left t)
    ;; (if b (all vars (if a b (true))) (all vars (if a b (true))))
    (push-proof-log 'look-up (list* 2 2 (if-left-index)) *true*)
    (push-proof-log 'if-equal (cons 2 (if-left-index)))
    ;; (if b (all vars (true)) (all vars (if a b (true))))
    (push-proof-log 'remove-universal (if-left-index))
    (push-proof-log 'if-true (if-left-index))
    (log-coerce-all-expr-to-bool (all-vars formula) (if-right-index))
    ;; (if b (true) (all vars (if (if a b (true)) (true) (false))))
    (push-proof-log 'case-analysis (cons 2 (if-right-index)) 1)
    ;; (if b
    ;;     (true)
    ;;     (all vars (if a (if b (true) (false)) (if (true) (true) (false)))))
    (push-proof-log 'if-true (list* 3 2 (if-right-index)))
    ;; (if b (true) (all vars (if a (if b (true) (false)) (true))))
    (log-look-up-false-for-coercion (list* 2 2 (if-right-index)))
    ;; (if b (true) (all vars (if a (false) (true))))
    (push-proof-log 'is-boolean (if-right-index))
    ;; (if b (true) (if (all vars (if a (false) (true))) (true) (false)))
    (log-bool-coercion-is-double-negation (if-right-index))
    ;; (if b
    ;;     (true)
    ;;     (if (if (all vars (if a (false) (true))) (false) (true))
    ;;         (false)
    ;;         (true)))
    (log-if-form-to-some (cons 1 (if-right-index)))
    ;; (if b (true) (if (some vars a) (false) (true)))
    (push-proof-log 'if-equal index (make-some (all-vars formula) test) t)
    ;; (if (some vars a)
    ;;     (if b (true) (if (some vars a) (false) (true)))
    ;;     (if b (true) (if (some vars a) (false) (true))))
    (push-proof-log 'look-up (list* 1 3 (if-left-index)) *true*)
    (push-proof-log 'if-true (cons 3 (if-left-index)))
    ;; (if (some vars a)
    ;;     (if b (true) (false))
    ;;     (if b (true) (if (some vars a) (false) (true))))
    (log-look-up-false (list* 1 3 (if-right-index)))
    (push-proof-log 'if-false (cons 3 (if-right-index)))
    ;; (if (some vars a) (if b (true) (false)) (if b (true) (true)))
    (push-proof-log 'if-equal (if-right-index))
    ;; (if (some vars a) (if b (true) (false)) (true))
    )
  )

;;; (all vars (if a (true) b)) => (if (all vars a) (true) (if b (true) (false)))
;;; vars do not occur free in b

(defun log-all-case-analysis-3 (formula index)
  ;; (all vars (if a (true) b))
  (let ((vars (all-vars formula))
	(test (if-test (all-expr formula))) ; a
	(right (if-right (all-expr formula)))) ; b
    (push-proof-log 'if-equal index right t)
    ;; (if b (all vars (if a (true) b)) (all vars (if a (true) b)))
    (push-proof-log 'look-up (list* 3 2 (if-left-index)) *true*)
    (push-proof-log 'if-equal (cons 2 (if-left-index)))
    ;; (if b (all vars (true)) (all vars (if a (true) b)))
    (push-proof-log 'remove-universal (if-left-index))
    (push-proof-log 'if-true (if-left-index))
    ;; (if b (true) (all vars (if a (true) b)))
    (log-coerce-all-expr-to-bool vars (if-right-index))
    ;; (if b (true) (all vars (if (if a (true) b) (true) (false))))
    (push-proof-log 'case-analysis (cons 2 (if-right-index)) 1)
    ;; (if b
    ;;     (true)
    ;;     (all vars (if a (if (true) (true) (false)) (if b (true) (false)))))
    (push-proof-log 'if-true (list* 2 2 (if-right-index)))
    ;; (if b (true) (all vars (if a (true) (if b (true) (false)))))
    (log-look-up-false-for-coercion (list* 3 2 (if-right-index)))
    ;; (if b (true) (all vars (if a (true) (false))))
    (log-remove-bool-coercion-from-all-expr (if-right-index))
    ;; (if b (true) (all vars a))
    (push-proof-log 'if-equal index (make-all vars test) t)
    ;; (if (all vars a) (if b (true) (all vars a)) (if b (true) (all vars b)))
    (push-proof-log 'look-up (cons 3 (if-left-index)) *true*)
    (push-proof-log 'if-equal (if-left-index))
    ;; (if (all vars a) (true) (if b (true) (all vars a)))
    (log-look-up-false (cons 3 (if-right-index)))
    ;; (if (all vars a) (true) (if b (true) (false)))
    )
  )

;;; (all vars (if a (false) b)) => (if (some vars a) (false) (all vars b))

(defun log-all-case-analysis-5 (formula index)
  ;; (all vars (if a (false) b))
  (let ((vars (all-vars formula))
	(test (if-test (all-expr formula))) ; a
	(right (if-right (all-expr formula)))) ; b
    (push-proof-log 'if-false (cons 2 (all-expr-index)) right t)
    (push-proof-log 'if-true (cons 3 (all-expr-index)) *false* t)
    ;; (all vars (if a (if (false) b (false)) (if (true) b (false))))
    (push-proof-log 'case-analysis (all-expr-index) 1 t)
    ;; (all vars (if (if a (false) (true)) b (false)))
    (push-proof-log 'all-case-analysis index)
    ;; (if (all vars (if a (false) (true))) (all vars b) (false))
    (log-coerce-if-test-to-bool index)
    ;; (if (if (all vars (if a (false) (true))) (true) (false))
    ;;     (all vars b)
    ;;     (false))
    (log-bool-coercion-is-double-negation (if-test-index))
    ;; (if (if (if (all vars (if a (false) (true))) (false) (true))
    ;;         (false)
    ;;         (true))
    ;;     (all vars b)
    ;;     (false))
    (log-if-form-to-some (cons 1 (if-test-index)))
    ;; (if (if (some vars a) (false) (true)) (all vars b) (false))
    (push-proof-log 'case-analysis index 1)
    ;; (if (some vars a)
    ;;     (if (false) (all vars b) (false))
    ;;     (if (true) (all vars b) (false)))
    (push-proof-log 'if-false (if-left-index))
    (push-proof-log 'if-true (if-right-index))
    ;; (if (some vars a) (false) (all vars b))
    )
  )

;;; (some vars (if a b c)) => (if a (some vars b) (some vars c))
;;; vars do not occur free in a

(defun log-some-case-analysis-1 (formula index)
  ;; formula is of the form (some vars (if a b c))
  ;; where the variables in vars do not occur free in a.

  ;; (some vars (if a b c))
  (push-proof-log 'if-equal index (if-test (some-expr formula)) t)
  ;; (if a (some vars (if a b c)) (some vars (if a b c)))
  (push-proof-log 'look-up (list* 1 2 (if-left-index)) *true*)
  (push-proof-log 'if-true (cons 2 (if-left-index)))
  ;; (if a (some vars b) (some vars (if a b c)))
  (log-coerce-if-test-to-bool (cons 2 (if-right-index)))
  ;; (if a (some vars b) (some vars (if (if a (true) (false)) b c)))
  (log-bool-coercion-is-double-negation (list* 1 2 (if-right-index)))
  ;; (if a
  ;;     (some vars b)
  ;;     (some vars (if (if (if a (false) (true)) (false) (true)) b c)))
  (push-proof-log 'look-up (list* 1 1 2 (if-right-index)) *true*)
  ;; (if a
  ;;     (some vars b)
  ;;     (some vars (if (if (true) (false) (true)) b c)))
  (push-proof-log 'if-true (list* 1 2 (if-right-index)))
  ;; (if a
  ;;     (some vars b)
  ;;     (some vars (if (false) b c)))
  (push-proof-log 'if-false (cons 2 (if-right-index)))
  ;; (if a (some vars b) (some vars c))
  )

;;; (some vars (if a b (false))) =>
;;;     (if (some vars a) (if b (true) (false)) (false))
;;; vars do not occur free in b

(defun log-some-case-analysis-2 (formula index)
  ;; formula is of the form (some vars (if a b (false)))
  ;; where the variables in vars do not occur free in b

  ;; (some vars (if a b (false)))
  (let ((test (if-test (all-expr formula))) ; a
	(left (if-left (all-expr formula)))) ; b
    (push-proof-log 'if-equal index left t)
    ;; (if b (some vars (if a b (false))) (some vars (if a b (false))))
    (push-proof-log 'look-up (list* 2 2 (if-left-index)) *true*)
    ;; (if b (some vars (if a (true) (false))) (some vars (if a b (false))))
    (log-coerce-some-expr-to-bool (if-right-index))
    ;; (if b
    ;;     (some vars (if a (true) (false)))
    ;;     (some vars (if (if a b (false)) (true) (false))))
    (push-proof-log 'case-analysis (cons 2 (if-right-index)) 1)
    ;; (if b
    ;;     (some vars (if a (true) (false)))
    ;;     (some vars (if a (if b (true) (false)) (if (false) (true) (false)))))
    (log-look-up-false-for-coercion (list* 2 2 (if-right-index)))
    ;; (if b
    ;;     (some vars (if a (true) (false)))
    ;;     (some vars (if a (false) (if (false) (true) (false)))))
    (push-proof-log 'if-false (list* 3 2 (if-right-index)))
    ;; (if b
    ;;     (some vars (if a (true) (false)))
    ;;     (some vars (if a (false) (false))))
    (push-proof-log 'if-equal (cons 2 (if-right-index)))
    (log-remove-existential (if-right-index))
    (log-remove-bool-coercion-from-some-expr (if-left-index))
    ;; (if b (some vars a) (if (false) (true) (false)))
    (push-proof-log 'if-false (if-right-index))
    ;; (if b (some vars a) (false))
    (push-proof-log 'if-equal index (make-some (all-vars formula) test) t)
    ;; (if (some vars a)
    ;;     (if b (some vars a) (false))
    ;;     (if b (some vars a) (false)))
    (push-proof-log 'look-up (cons 2 (if-left-index)) *true*)
    (log-look-up-false (cons 2 (if-right-index)))
    (push-proof-log 'if-equal (if-right-index))
    ;; (if (some vars a) (if b (true) (false)) (false))
    ))

;;; (some vars (if a (false) b)) =>
;;;     (if (all vars a) (false) (if b (true) (false)))
;;; vars do not occur free in b

(defun log-some-case-analysis-3 (formula index)
  ;; formula is of the form (some vars (if a b (false)))
  ;; where vars do not occur free in b

  ;; (some vars (if a (false) b))
  (let ((test (if-test (all-expr formula))) ; a
	(right (if-right (all-expr formula)))) ; b
    (push-proof-log 'if-equal index right t)
    ;; (if b (some vars (if a (false) b)) (some vars (if a (false) b)))
    (push-proof-log 'look-up (list* 3 2 (if-left-index)) *true*)
    ;; (if b (some vars (if a (false) (true))) (some vars (if a (false) b)))
    (log-coerce-some-expr-to-bool (if-right-index))
    ;; (if b
    ;;     (some vars (if a (false) (true)))
    ;;     (some vars (if (if a (false) b) (true) (false))))
    (push-proof-log 'case-analysis (cons 2 (if-right-index)) 1)
    ;; (if b
    ;;     (some vars (if a (false) (true)))
    ;;     (some vars (if a (if (false) (true) (false)) (if b (true) (false)))))
    (log-look-up-false-for-coercion (list* 3 2 (if-right-index)))
    ;; (if b
    ;;     (some vars (if a (false) (true)))
    ;;     (some vars (if a (if (false) (true) (false)) (false))))
    (push-proof-log 'if-false (list* 2 2 (if-right-index)))
    ;; (if b
    ;;     (some vars (if a (false) (true)))
    ;;     (some vars (if a (false) (false))))
    (push-proof-log 'if-equal (cons 2 (if-right-index)))
    (log-remove-existential (if-right-index))
    ;; (if b (some vars (if a (false) (true))) (if (false) (true) (false)))
    (push-proof-log 'if-false (if-right-index))
    ;; (if b (some vars (if a (false) (true))) (false))
    (log-some-to-if-form (if-left-index))
    ;; (if b
    ;;     (if (all vars (if (if a (false) (true)) (false) (true)))
    ;;         (false)
    ;;         (true))
    ;;     (false))
    (push-proof-log 'case-analysis (list* 2 1 (if-left-index)) 1)
    ;; (if b
    ;;     (if (all vars (if a
    ;;                     (if (false) (false) (true))
    ;;                     (if (true) (true) (false))))
    ;;         (false)
    ;;         (true))
    ;;     (false))
    (push-proof-log 'if-false (list* 2 2 1 (if-left-index)))
    (push-proof-log 'if-true (list* 3 2 1 (if-left-index)))
    ;; (if b
    ;;     (if (all vars (if a (true) (false))) (false) (true))
    ;;     (false))
    (log-remove-bool-coercion-from-all-expr (cons 1 (if-left-index)))
    ;; (if b (if (all vars a) (false) (true)) (false))
    (push-proof-log 'if-equal index (make-all (all-vars formula) test) t)
    ;; (if (all vars a)
    ;;     (if b (if (all vars a) (false) (true)) (false))
    ;;     (if b (if (all vars a) (false) (true)) (false)))
    (push-proof-log 'look-up (list* 1 2 (if-left-index)) *true*)
    (push-proof-log 'if-true (cons 2 (if-left-index)))
    (push-proof-log 'if-equal (if-left-index))
    ;; (if (all vars a) (false) (if b (if (all vars a) (false) (true)) (false)))
    (log-look-up-false (list* 1 2 (if-right-index)))
    (push-proof-log 'if-false (cons 2 (if-right-index)))
    ;; (if (all vars a) (false) (if b (true) (false)))
    
    ))


;;; (some vars (if a b (true))) => (if (all vars a) (some vars b) (true))

(defun log-some-case-analysis-4 (index)
  ;; (some vars (if a b (true)))
  (log-some-to-if-form index)
  ;; (if (all vars (if (if a b (true)) (false) (true))) (false) (true))
  (push-proof-log 'case-analysis (cons 2 (if-test-index)) 1)
  ;; (if (all vars (if a (if b (false) (true)) (if (true) (false) (true))))
  ;;     (false)
  ;;     (true))
  (push-proof-log 'if-true (list* 3 2 (if-test-index)))
  (push-proof-log 'all-case-analysis (if-test-index))
  ;; (if (if (all vars a) (all vars (if b (false) (true))) (false))
  ;;     (false)
  ;;     (true))
  (push-proof-log 'case-analysis index 1)
  ;; (if (all vars a)
  ;;     (if (all vars (if b (false) (true))) (false) (true))
  ;;     (if (false) (false) (true)))
  (log-if-form-to-some (if-left-index))
  (push-proof-log 'if-false (if-right-index))
  ;; (if (all vars a) (some vars b) (true))
  )

;;; (some vars (if a (true) b)) => (if (some vars a) (true) (some vars b))

(defun log-some-case-analysis-5 (formula index)
  ;; (some vars (if a b (true)))
  (let ((vars (some-vars formula))
	(test (if-test (some-expr formula))) ; a
	(right (if-right (some-expr formula)))) ; b
    (log-some-to-if-form index)
    ;; (if (all vars (if (if a (true) b) (false) (true))) (false) (true))
    (push-proof-log 'case-analysis (cons 2 (if-test-index)) 1)
    ;; (if (all vars (if a (if (true) (false) (true)) (if b (false) (true))))
    ;;     (false)
    ;;     (true))
    (push-proof-log 'if-true (list* 2 2 (if-test-index)))
    ;; (if (all vars (if a (false) (if b (false) (true))))
    ;;     (false)
    ;;     (true))
    (push-proof-log 'if-false (list* 2 2 (if-test-index))
		    (make-if right *false* *true*) t)
    (push-proof-log 'if-true (list* 3 2 (if-test-index)) *false* t)
    ;; (if (all vars (if a
    ;;                  (if (false) (if b (false) (true)) (false))
    ;;                  (if (true) (if b (false) (true)) (false))))
    ;;     (false)
    ;;     (true))
    (push-proof-log 'case-analysis (cons 2 (if-test-index)) 1 t)
    ;; (if (all vars (if (if a (false) (true)) (if b (false) (true)) (false)))
    ;;     (false)
    ;;     (true))
    (push-proof-log 'all-case-analysis (if-test-index))
    ;; (if (if (all vars (if a (false) (true)))
    ;;         (all vars (if b (false) (true)))
    ;;         (false))
    ;;     (false)
    ;;     (true))
    (push-proof-log 'if-false (cons 2 (if-test-index)) *false* t)
    (push-proof-log 'if-true (cons 3 (if-test-index))
		    (make-all vars (make-if right *false* *true*))
		    t)
    ;; (if (if (all vars (if a (false) (true)))
    ;;         (if (false) (false) (all vars (if b (false) (true))))
    ;;         (if (true) (false) (all vars (if b (false) (true)))))
    ;;     (false)
    ;;     (true))
    (push-proof-log 'case-analysis (if-test-index) 1 t)
    ;; (if (if (if (all vars (if a (false) (true))) (false) (true))
    ;;         (false)
    ;;         (all vars (if b (false) (true))))
    ;;     (false))
    ;;     (true))
    (log-if-form-to-some (cons 1 (if-test-index)))
    ;; (if (if (some vars a) (false) (all vars (if b (false) (true))))
    ;;     (false)
    ;;     (true))
    (push-proof-log 'case-analysis index 1)
    (push-proof-log 'if-false (if-left-index))
    (log-if-form-to-some (if-right-index))
    ;; (if (some vars a) (true) (some vars b))

    ))

;;; (if a (all vars b) (all vars c)) => (all vars if a b c)
;;; vars do not occur free in a.

(defun log-all-uncase-analysis-1 (formula index)
  ;; (if a (all vars b) (all vars c))
  (let ((a (if-test formula))
	(b (all-expr (if-left formula)))
	(c (all-expr (if-right formula)))
	(vars (all-vars (if-left formula))))
    (push-proof-log 'if-false (cons 2 (if-right-index)) b t)
    (push-proof-log 'if-true (list* 1 2 (if-right-index)) *true* t)
    ;; (if a
    ;;     (all vars b)
    ;;     (all vars (if (if (true) (false) (true)) b c)))
    (push-proof-log 'look-up (list* 1 1 2 (if-right-index))
		    (make-if a *false* *true*))
    ;; (if a
    ;;     (all vars b)
    ;;     (all vars (if (if (if a (false) (true)) (false) (true)) b c)))
    (log-double-negation-is-coercion (list* 1 2 (if-right-index)))
    ;; (if a
    ;;     (all vars b)
    ;;     (all vars (if (if a (true) (false)) b c)))
    (log-remove-bool-coercion-from-if-test (cons 2 (if-right-index)))
    ;; (if a (all vars b) (all vars (if a b c)))
    (push-proof-log 'if-true (cons 2 (if-left-index)) c t)
    (push-proof-log 'look-up (list* 1 2 (if-left-index)) a)
    ;; (if a (all vars (if a b c)) (all vars (if a b c)))
    (push-proof-log 'if-equal index)
    ;; (all vars (if a b c))

    ))

;;; (if (some vars a) (if b (true) (false)) (true))
;;      => (all vars (if a b (true)))
;;; vars do not occur free in b

(defun log-all-uncase-analysis-2 (formula index)
  ;; (if (some vars a) (if b (true) (false)) (true))
  (let ((a (some-expr (if-test formula)))
	(b (if-test (if-left formula)))
	(vars (some-vars (if-test formula))))
    (push-proof-log 'if-equal (if-right-index) b t)
    ;; (if (some vars a) (if b (true) (false)) (if b (true) (true)))
    (push-proof-log 'if-false (cons 3 (if-right-index)) *false* t)
    ;; (if (some vars a)
    ;;     (if b (true) (false))
    ;;     (if b (true) (if (false) (false) (true))))
    (log-inverse-look-up-false (make-some vars a) (list* 1 3 (if-right-index)))
    ;; (if (some vars a)
    ;;     (if b (true) (false))
    ;;     (if b (true) (if (some vars a) (false) (true))))
    (push-proof-log 'if-true (cons 3 (if-left-index)) *true* t)
    (push-proof-log 'look-up (list* 1 3 (if-left-index)) (make-some vars a))
    ;; (if (some vars a )
    ;;     (if b (true) (if (some vars a) (false) (true)))
    ;;     (if b (true) (if (some vars a) (false) (true))))
    (push-proof-log 'if-equal index)
    ;; (if b (true) (if (some vars a) (false) (true)))
    (log-some-to-if-form (cons 1 (if-right-index)))
    ;; (if b (true) (if (if (all vars (if a (false) (true))) (false) (true))
    ;;                  (false)
    ;;                  (true)))
    (log-double-negation-is-coercion (if-right-index))
    ;; (if b (true) (if (all vars (if a (false) (true))) (true) (false)))
    (push-proof-log 'is-boolean (if-right-index) t)
    ;; (if b (true) (all vars (if a (false) (true))))
    (log-inverse-look-up-false-for-coercion
     (make-if b *true* *false*) (list* 2 2 (if-right-index)))
    ;; (if b (true) (all vars (if a (if b (true) (false)) (true))))
    (push-proof-log 'if-true (list* 3 2 (if-right-index)) *false* t)
    ;; (if b
    ;;     (true)
    ;;     (all vars (if a (if b (true) (false)) (if (true) (true) (false)))))
    (push-proof-log 'case-analysis (cons 2 (if-right-index)) 1 t)
    ;; (if b (true) (all vars (if (if a b (true)) (true) (false))))
    (log-remove-bool-coercion-from-all-expr (if-right-index))
    (push-proof-log 'if-true (if-left-index) *false* t)
    (push-proof-log 'remove-universal (if-left-index) vars t)
    ;; (if b (all vars (true)) (all vars (if a b (true))))
    (push-proof-log 'if-equal (cons 2 (if-left-index)) a t)
    (push-proof-log 'look-up (list* 2 2 (if-left-index)) b)
    ;; (if b (all vars (if a b (true))) (all vars (if a b (true))))
    (push-proof-log 'if-equal index)
    ;; (all vars (if a b (true)))
    
    ))

(defun log-all-uncase-analysis-2a (formula index)
  ;; (if a (all vars b) (true))
  ;; vars do not occur free in a
  (let ((test (if-test formula))
	(left (if-left formula)))
    (push-proof-log 'if-true (cons 2 (if-left-index)) *true* t)
    ;; (if a (all vars (if (true) b (true))) (true))
    (push-proof-log 'look-up (list* 1 2 (if-left-index)) test)
    ;; (if a (all vars (if a b (true))) (true))
    (push-proof-log 'is-boolean (if-right-index))
    (push-proof-log 'remove-universal (if-right-index) (all-vars left) t)
    ;; (if a (all vars (if a b (true))) (all vars (true)))
    (push-proof-log 'if-true (cons 2 (if-right-index)) (all-expr left) t)
    ;; (if a (all vars (if a b (true))) (all vars (if (true) (true) b)))
    (push-proof-log 'look-up (list* 1 2 (if-right-index))
		    (make-if test *false* *true*))
    ;; (if a
    ;;     (all vars (if a b (true)))
    ;;     (all vars (if (if a (false) (true)) (true) b)))
    (push-proof-log 'case-analysis (cons 2 (if-right-index)) 1)
    ;; (if a
    ;;     (all vars (if a b (true)))
    ;;     (all vars (if a (if (false) (true) b) (if (true) (true) b))))
    (push-proof-log 'if-true (list* 3 2 (if-right-index)))
    (push-proof-log 'if-false (list* 2 2 (if-right-index)))
    ;; (if a (all vars (if a b (true))) (all vars (if a b (true))))
    (push-proof-log 'if-equal index)
    ;; (all vars (if a b (true)))
    ))
    

;;; (if (all vars a) (true) (if b (true) (false)))
;;;   => (all vars (if a (true) b))
;;; vars do not occur free in b

(defun log-all-uncase-analysis-3 (formula index)
  ;; (if (all vars a) (true) (if b (true) (false)))
  ;; vars do not occur free in b
  (let ((vars (all-vars (if-test formula)))
	(a (all-expr (if-test formula)))
	(b (if-test (if-right formula))))
    (log-inverse-look-up-false (if-test formula) (cons 3 (if-right-index)))
    ;; (if (all vars a) (true) (if b (true) (all vars a)))
    (push-proof-log 'if-equal (if-left-index) b t)
    (push-proof-log 'look-up (cons 3 (if-left-index)) (make-all vars a))
    ;; (if (all vars a) (if b (true) (all vars a)) (if b (true (all-vars a))))
    (push-proof-log 'if-equal index)
    ;; (if b (true) (all vars a))
    (log-coerce-all-expr-to-bool vars (if-right-index))
    ;; (if b (true) (all vars (if a (true) (false))))
    (log-inverse-look-up-false-for-coercion
     (make-if b *true* *false*) (list* 3 2 (if-right-index)))
    ;; (if b (true) (all vars (if a (true) (if b (true) (false)))))
    (push-proof-log 'if-true (list* 2 2 (if-right-index)) *false* t)
    ;; (if b
    ;;     (true)
    ;;     (all vars (if a (if (true) (true) (false)) (if b (true) (false)))))
    (push-proof-log 'case-analysis (cons 2 (if-right-index)) 1 t)
    ;; (if b (true) (all vars (if (if a (true) b) (true) (false))))
    (log-remove-bool-coercion-from-all-expr (if-right-index))
    ;; (if b (true) (all vars (if a (true) b)))
    (push-proof-log 'if-true (if-left-index) *false* t)
    ;; (if b (if (true) (true) (false)) (all vars (if a (true) b)))
    (push-proof-log 'remove-universal (if-left-index) vars t)
    ;; (if b (all vars (true)) (all vars (if a (true) b)))
    (push-proof-log 'if-equal (cons 2 (if-left-index)) a t)
    (push-proof-log 'look-up (list* 3 2 (if-left-index)) b)
    ;; (if b (all vars (if a (true) b)) (all vars (if a (true) b)))
    (push-proof-log 'if-equal index)
    ;; (all vars (if a (true) b))
    
    ))


;;; (if a (true) (all vars b)) => (all vars (if a (true) b))
;;; vars do not occur free in a.

(defun log-all-uncase-analysis-3a (formula index)
  ;; (if a (true) (all vars b))
  (let ((vars (all-vars (if-right formula))))
    (push-proof-log 'is-boolean (if-left-index))
    (push-proof-log 'remove-universal (if-left-index) vars t)
    ;; (if a (all vars (true)) (all vars b))
    (log-all-uncase-analysis-1
     (make-if (if-test formula) (make-all vars *true*) (if-right formula))
     index)))

;;; (if (some vars a) (false) (all vars b)) => (all vars (if a (false) b))

(defun log-all-uncase-analysis-5 (formula index)
  ;; (if (some vars a) (false) (all vars b))
  (let ((a (some-expr (if-test formula)))
	(b (all-expr (if-right formula)))
	(vars (some-vars (if-test formula))))
    (push-proof-log 'if-true (if-right-index) *false* t)
    (push-proof-log 'if-false (if-left-index) (if-right formula) t)
    ;; (if (some vars a)
    ;;     (if (false) (all vars b) (false))
    ;;     (if (true) (all vars b) (false))
    (push-proof-log 'case-analysis index 1 t)
    ;; (if (if (some vars a) (false) (true)) (all vars b) (false))
    (log-some-to-if-form (cons 1 (if-test-index)))
    ;; (if (if (if (all vars (if a (false) (true))) (false) (true))
    ;;         (false)
    ;;         (true))
    ;;     (all vars b)
    ;;     (false))
    (log-double-negation-is-coercion (if-test-index))
    ;; (if (if (all vars (if a (false) (true))) (true) (false))
    ;;     (all vars b)
    ;;     (false))
    (log-remove-bool-coercion-from-if-test index)
    ;; (if (all vars (if a (false) (true))) (all vars b) (false))
    (push-proof-log 'all-case-analysis index t)
    ;; (all vars (if (if a (false) (true)) b (false)))
    (push-proof-log 'case-analysis (all-expr-index) 1)
    ;; (all vars (if a (if (false) b (false)) (if (true) b (false))))
    (push-proof-log 'if-true (cons 3 (all-expr-index)))
    (push-proof-log 'if-false (cons 2 (all-expr-index)))
    ;; (all vars (if a (false) b))

    ))

;;; (if a (some vars b) (some vars c)) => (some vars (if a b c))
;;; vars do not occur free in a

(defun log-some-uncase-analysis-1 (formula index)
  (let ((a (if-test formula))
	(b (some-expr (if-left formula)))
	(c (some-expr (if-right formula)))
	(vars (some-vars (if-left formula))))
    ;; (if a (some vars b) (some vars c))
    (push-proof-log 'if-false (cons 2 (if-right-index)) b t)
    ;; (if a (some vars b) (some vars (if (false) b c)))
    (push-proof-log 'if-true (list* 1 2 (if-right-index)) *true* t)
    ;; (if a (some vars b) (some vars (if (if (true) (false) (true)) b c)))
    (push-proof-log 'look-up (list* 1 1 2 (if-right-index))
		    (make-if a *false* *true*))
    ;; (if a
    ;;     (some vars b)
    ;;     (some-vars (if (if (if a (false) (true)) (false) (true)) b c)))
    (log-double-negation-is-coercion (list* 1 2 (if-right-index)))
    ;; (if a (some vars b) (some vars (if (if a (true) (false)) b c)))
    (log-remove-bool-coercion-from-if-test (cons 2 (if-right-index)))
    ;; (if a (some vars b) (some vars (if a b c)))
    (push-proof-log 'if-true (cons 2 (if-left-index)) c t)
    (push-proof-log 'look-up (list* 1 2 (if-left-index)) a)
    ;; (if a (some vars (if a b c)) (some vars (if a b c)))
    (push-proof-log 'if-equal index)
    ;; (some vars (if a b c))

    ))


;;; (if (some vars a) (if b (true) (false)) (false))
;;;  =>  (some vars (if a b (false)))
;;; vars do not occur free in b

(defun log-some-uncase-analysis-2 (formula index)
  (let ((a (all-expr (if-test formula)))
	(b (if-test (if-left formula)))
	(vars (all-vars (if-test formula))))
    ;; (if (some vars a) (if b (true) (false)) (false))
    (push-proof-log 'if-equal (if-right-index) b t)
    (log-inverse-look-up-false (if-test formula) (cons 2 (if-right-index)))
    (push-proof-log 'look-up (cons 2 (if-left-index)) (if-test formula))
    ;; (if (some vars a)
    ;;     (if b (some vars a) (false))
    ;;     (if b (some vars a) (false)))
    (push-proof-log 'if-equal index)
    ;; (if b (some vars a) (false))
    (push-proof-log 'is-boolean (if-right-index))
    ;; (if b (some vars a) (if (false) (true) (false)))
    (log-coerce-some-expr-to-bool (if-left-index))
    (log-introduce-existential vars (if-right-index))
    (push-proof-log 'if-equal (cons 2 (if-right-index)) a t)
    ;; (if b
    ;;     (some vars (if a (true) (false)))
    ;;     (some vars (if a (false) (false))))
    (push-proof-log 'if-false (list* 3 2 (if-right-index)) *true* t)
    ;; (if b
    ;;     (some vars (if a (true) (false)))
    ;;     (some vars (if a (false) (if (false) (true) (false)))))
    (log-inverse-look-up-false-for-coercion
     (make-if b *true* *false*) (list* 2 2 (if-right-index)))
    ;; (if b
    ;;     (some vars (if a (true) (false)))
    ;;     (some vars (if a (if b (true) (false)) (if (false) (true) (false)))))
    (push-proof-log 'case-analysis (cons 2 (if-right-index)) 1 t)
    ;; (if b
    ;;     (some vars (if a (true) (false)))
    ;;     (some vars (if (if a b (false)) (true) (false))))
    (log-remove-bool-coercion-from-some-expr (if-right-index))
    ;; (if b
    ;;     (some vars (if a (true) (false)))
    ;;     (some vars (if a b (false))))
    (push-proof-log 'look-up (list* 2 2 (if-left-index)) b)
    (push-proof-log 'if-equal index)
    ;; (some vars (if a b (false)))

    ))


;;; (if a (some vars b) (false))
;;;  =>  (some vars (if a b (false)))
;;; vars do not occur free in a

(defun log-some-uncase-analysis-2a (formula index)
  ;; (if a (some vars b) (false))
  (let ((vars (some-vars (if-left formula))))
    (push-proof-log 'is-boolean (if-right-index))
    (log-introduce-existential vars (if-right-index))
    ;; (if a (some vars b) (some vars (false)))
    (log-some-uncase-analysis-1
     (make-if (if-test formula) (if-left formula) (make-some vars *false*))
     index)))

;;; (if (all vars a) (false) (if b (true) (false)))
;;;   => (some vars (if a (false) b))
;;; vars do no occur free in b

(defun log-some-uncase-analysis-3 (formula index)
  (let ((a (all-expr (if-test formula)))
	(b (if-test (if-right formula)))
	(vars (all-vars (if-test formula))))
    ;; (if (all vars a) (false) (if b (true) (false)))
    (push-proof-log 'if-false (cons 2 (if-right-index)) *false* t)
    (log-inverse-look-up-false (if-test formula) (list* 1 2 (if-right-index)))
    ;; (if (all vars a) (false) (if b (if (all vars a) (false) (true)) (false)))
    (push-proof-log 'if-equal (if-left-index) b t)
    (push-proof-log 'if-true (cons 2 (if-left-index)) *true* t)
    (push-proof-log 'look-up (list* 1 2 (if-left-index)) (if-test formula))
    ;; (if (all vars a)
    ;;     (if b (if (all vars a) (false) (true)) (false))
    ;;     (if b (if (all vars a) (false) (true)) (false)))
    (push-proof-log 'if-equal index)
    ;; (if b (if (all vars a) (false) (true)) (false))
    (log-coerce-all-expr-to-bool vars (cons 1 (if-left-index)))
    ;; (if b (if (all vars (if a (true) (false))) (false) (true)) (false))
    (push-proof-log 'if-true (list* 3 2 1 (if-left-index)) *true* t)
    (push-proof-log 'if-false (list* 2 2 1 (if-left-index)) *false* t)
    (push-proof-log 'case-analysis (list* 2 1 (if-left-index)) 1 t)
    (log-if-form-to-some (if-left-index))
    ;; (if b (some vars (if a (false) (true))) (false))
    (push-proof-log 'is-boolean (if-right-index))
    (log-introduce-existential vars (if-right-index))
    (push-proof-log 'if-equal (cons 2 (if-right-index)) a t)
    (push-proof-log 'is-boolean (list* 2 2 (if-right-index)))
    ;; (if b
    ;;     (some vars (if a (false) (true)))
    ;;     (some vars (if a (if (false) (true) (false)) (false))))
    (log-inverse-look-up-false-for-coercion
     (make-if b *true* *false*) (list* 3 2 (if-right-index)))
    (push-proof-log 'case-analysis (cons 2 (if-right-index)) 1 t)
    ;; (if b
    ;;     (some vars (if a (false) (true)))
    ;;     (some vars (if (if a (false) b) (true) (false))))
    (log-remove-bool-coercion-from-some-expr (if-right-index))
    (push-proof-log 'look-up (list* 3 2 (if-left-index)) b)
    (push-proof-log 'if-equal index)
    ;; (some vars (if a (false) b))

    ))


;;; (if a (false) (some vars b)
;;;   => (some vars (if a (false) b))
;;; vars do no occur free in a

(defun log-some-uncase-analysis-3a (formula index)
  (let ((vars (all-vars (if-right formula))))
    ;; (if a (false) (some vars b)
    (push-proof-log 'is-boolean (if-left-index))
    (log-introduce-existential vars (if-left-index))
    ;; (if a (some vars false) (some vars b))
    (log-some-uncase-analysis-1
     (make-if (if-test formula) (make-some vars *false*) (if-right formula))
     index)))

;;; (if (all vars a) (some vars b) (true)) => (some vars (if a b (true)))

(defun log-some-uncase-analysis-4 (index)
  ;; (if (all vars a) (some vars b) (true))
  (push-proof-log 'if-false (if-right-index) *false* t)
  (log-some-to-if-form (if-left-index))
  ;; (if (all vars a)
  ;;     (if (all vars (if b (false) (true))) (false) (true))
  ;;     (if (false) (false) (true)))
  (push-proof-log 'case-analysis index 1 t)
  ;; if (if (all vars a) (all vars (if b (false) (true))) (false))
  ;;     (false)
  ;;     (true))
  (push-proof-log 'all-case-analysis (if-test-index) t)
  (push-proof-log 'if-true (list* 3 2 (if-test-index)) *true* t)
  ;; (if (all vars (if a (if b (false) (true)) (if (true) (false) (true))))
  ;;     (false)
  ;;     (true))
  (push-proof-log 'case-analysis (cons 2 (if-test-index)) 1 t)
  ;; (if (all vars (if (if a b (true)) (false) (true))) (false) (true))
  (log-if-form-to-some index)
  ;; (some vars (if a b (true)))

  )

;;; (if (some vars a) (true) (some vars b))
;;;    =>  (some vars (if a (true) b))

(defun log-some-uncase-analysis-5 (formula index)
  (let ((a (some-expr (if-test formula)))
	(b (some-expr (if-right formula)))
	(vars (some-vars (if-test formula))))
    ;; (if (some vars a) (true) (some vars b))
    (log-some-to-if-form (if-right-index))
    (push-proof-log 'if-false (if-left-index) *false* t)
    (push-proof-log 'case-analysis index 1 t)
    ;; (if (if (some vars a) (false) (all vars (if b (false) (true))))
    ;;     (false)
    ;;     (true))
    (log-some-to-if-form (cons 1 (if-test-index)))
    (push-proof-log 'case-analysis (if-test-index) 1)
    ;; (if (if (all vars (if a (false) (true)))
    ;;         (if (false) (false) (all vars (if b (false) (true))))
    ;;         (if (true) (false) (all vars (if b (false) (true)))))
    ;;     (false)
    ;;     (true))
    (push-proof-log 'if-true (cons 3 (if-test-index)))
    (push-proof-log 'if-false (cons 2 (if-test-index)))
    ;; (if (if (all vars (if a (false) (true)))
    ;;         (all vars (if b (false) (true)))
    ;;         (false))
    ;;     (false)
    ;;     (true))
    (push-proof-log 'all-case-analysis (if-test-index) t)
    ;; (if (all vars (if (if a (false) (true)) (if b (false) (true)) (false)))
    ;;     (false)
    ;;     (true)
    (push-proof-log 'case-analysis (cons 2 (if-test-index)) 1)
    (push-proof-log 'if-true (list* 3 2 (if-test-index)))
    (push-proof-log 'if-false (list* 2 2 (if-test-index)))
    ;; (if (all vars (if a (false) (if b (false) (true))))
    ;;     (false)
    ;;     (true))
    (push-proof-log 'if-true (list* 2 2 (if-test-index)) *true* t)
    ;; (if (all vars (if a (if (true) (false) (true)) (if b (false) (true))))
    ;;     (false)
    ;;     (true))
    (push-proof-log 'case-analysis (cons 2 (if-test-index)) 1 t)
    ;; (if (all vars (if (if a (true) b) (false) (true))) (false) (true))
    (log-if-form-to-some index)
    ;; (some vars (if a (true) b))
    
    ))

(defun log-all-out-left (formula bool-p index)
  ;; (if test (all (x) lexpr) right)
  (log-coerce-expr-for-boolean-or-bool-p
   (if-right formula) (if-right-index) bool-p)
  ;; (if test (all (x) lexpr) (if right (true) (false)))
  (push-proof-log 'remove-universal
		  (if-right-index) (all-vars (if-left formula)) t)
  ;; (if test (all (x) lexpr) (all (x) right))
  (log-all-uncase-analysis-1
   (make-if (if-test formula)
	    (if-left formula)
	    (make-all (all-vars (if-left formula)) (if-right formula)))
   index)
  ;; (all (x) (if test lexpr right))
  )

(defun log-some-out-left (formula bool-p index)
  ;; (if test (some (x) lexpr) right)
  (log-coerce-expr-for-boolean-or-bool-p
   (if-right formula) (if-right-index) bool-p)
  ;; (if test (some (x) lexpr) (if right (true) (false)))
  (log-introduce-existential (some-vars (if-left formula)) (if-right-index))
  ;; (if test (some (x) lexpr) (some (x) right))
  (log-some-uncase-analysis-1
   (make-if (if-test formula)
	    (if-left formula)
	    (make-some (some-vars (if-left formula)) (if-right formula)))
   index)
  ;; (some (x) (if test lexpr right))
  )

(defun log-all-out-right (formula bool-p index)
  ;; (if test left (all (x) rexpr)
  (log-coerce-expr-for-boolean-or-bool-p
   (if-left formula) (if-left-index) bool-p)
  ;; (if test (if left (true) (false)) (all (x) rexpr))
  (push-proof-log 'remove-universal
		  (if-left-index) (all-vars (if-right formula)) t)
  ;; (if test (all (x) left) (all (x) rexpr))
  (log-all-uncase-analysis-1
   (make-if (if-test formula)
	    (make-all (all-vars (if-right formula)) (if-left formula))
	    (if-right formula))
   index)
  ;; (all (x) (if test left rexpr))
  )

(defun log-some-out-right (formula bool-p index)
  ;; (if test left (some (x) rexpr)
  (log-coerce-expr-for-boolean-or-bool-p
   (if-left formula) (if-left-index) bool-p)
  ;; (if test (if left (true) (false)) (some (x) rexpr))
  (log-introduce-existential (some-vars (if-right formula)) (if-left-index))
  ;; (if test (some (x) left) (some (x) rexpr))
  (log-some-uncase-analysis-1
   (make-if (if-test formula)
	    (make-some (some-vars (if-right formula)) (if-left formula))
	    (if-right formula))
   index)
  ;; (some (x) (if test left rexpr))
  )

;;; Assumes quantifications are expanded, instantiations agree with
;;; quantifications. Result is as though the instantiations are
;;; simultaneous, i.e., fully instantiated formule conjuncted with original
;;; formula (in IF form).
(defun linearize-and-log-universal-instantiations (instantiations index)
  (unless (null instantiations)
    (push-proof-log 'instantiate-universal index (car instantiations))
    (linearize-and-log-universal-instantiations (cdr instantiations)
                                                (if-test-index))
    (unless (null (cdr instantiations))
      (push-proof-log 'case-analysis index 1)
      (push-proof-log 'instantiate-universal
		      (if-left-index) (car instantiations) t)
      (push-proof-log 'if-false (if-right-index)))))

;;; Existential version of above.
(defun linearize-and-log-existential-instantiations (instantiations index)
  (unless (null instantiations)
    (log-instantiate-existential (car instantiations) index)
    (linearize-and-log-existential-instantiations (cdr instantiations)
                                                  (if-test-index))
    (unless (null (cdr instantiations))
      (push-proof-log 'case-analysis index 1)
      (push-proof-log 'if-true (if-left-index))
      (log-uninstantiate-existential (car instantiations) (if-right-index)))))

;;; Assumes expanded quantification, vars are outermost quantifications,
;;; subst-list agrees with inner quantifications.
(defun log-instantiations (kind vars subst-list index)
  (cond ((null vars)
         (let ((instantiations
                (mapcar #'(lambda (u) (make-= (car u) (cdr u))) subst-list)))
           (if (eq kind 'all)
               (linearize-and-log-universal-instantiations
                instantiations index)
             (linearize-and-log-existential-instantiations
              instantiations index))))
	(t (log-instantiations
	    kind (cdr vars) subst-list
	    (if (eq kind 'all) (all-expr-index) (some-expr-index))))))

(defun log-flip-universals (number-of-vars index)
  (unless (zerop number-of-vars)
    (push-proof-log 'flip-universals index)
    (log-flip-universals (- number-of-vars 1) (all-expr-index))))

(defun repeat-log-flip-existentials (number-of-vars index)
  (unless (zerop number-of-vars)
    (log-flip-existentials index)
    (repeat-log-flip-existentials (- number-of-vars 1) (some-expr-index))))

(defun log-label (index var expr)
  (when *record-proof-logs-flag*
    ;; precondition:
    ;; (not (member-eq var (list-of-free-variables-unexpanded expr)))
    ;; ---
    ;; formula
    (push-proof-log 'if-true index *true* t)
    ;; (if (true) formula (true))
    (push-proof-log 'if-false (if-test-index) *false* t)
    ;; (if (if (false) (false) (true)) formula (true))
    (push-proof-log 'if-false
     (cons 1 (if-test-index))
     (make-all (list var) (make-if (make-= var expr) *false* *true*))
     t)
    ;; (if (if (if (false) (all (var) (if (= var expr) (false) (true))) (false))
    ;;         (false)
    ;;         (true))
    ;;     formula
    ;;     (true))
    (push-proof-log 'if-true (list* 1 1 (if-test-index)) *true* t)
    ;; (if (if (if (if (true) (false) (true))
    ;;             (all (var) (if (= var expr) (false) (true)))
    ;;             (false))
    ;;         (false)
    ;;         (true))
    ;;     formula
    ;;     (true))
    (push-proof-log 'compute (list* 1 1 1 (if-test-index)) (make-= expr expr) t)
    ;; (if (if (if (if (= expr expr) (false) (true))
    ;;             (all (var) (if (= var expr) (false) (true)))
    ;;             (false))
    ;;         (false)
    ;;         (true))
    ;;     formula
    ;;     (true))
    (push-proof-log 'instantiate-universal (cons 1 (if-test-index))
		    (make-= var expr) t)
    ;; (if (if (all (var) (if (= var expr) (false) (true)))
    ;;         (false)
    ;;         (true))
    ;;     formula
    ;;     (true))
    (log-if-form-to-some (if-test-index))
    ;; (if (some (var) (= var expr)) formula (true))
    ))

;;; =============== Boolean Coercion ===============


;;; Expression part of a quantification and test part of
;;; an if expression can be coerced to Boolean and each
;;; is a Boolean context.

(defun log-coerce-all-expr-to-bool (vars index)
  (when *record-proof-logs-flag*
    ;; (all vars P)
    (push-proof-log 'is-boolean index)
    ;; (if (all vars P) (true) (false))
    (push-proof-log 'is-boolean (if-left-index))
    ;; (if (all vars P) (if (true) (true) (false)) (false))
    (push-proof-log 'remove-universal (if-left-index) vars t)
    ;; (if (all vars P) (all vars (true)) (false))
    (push-proof-log 'all-case-analysis index t)
    ;; (all vars (if P (true) (false)))
    ))

(defun log-remove-bool-coercion-from-all-expr (index)
  (when *record-proof-logs-flag*
    ;; (all vars (if P (true) (false)))
    (push-proof-log 'all-case-analysis index)
    ;; (if (all vars P) (all vars (true)) (false))
    (push-proof-log 'remove-universal (if-left-index))
    ;; (if (all vars P) (if (true) (true) (false)) (false))
    (push-proof-log 'is-boolean (if-left-index) t)
    ;; (if (all vars P) (true) (false))
    (push-proof-log 'is-boolean index t)
    ;; (all vars P)
    ))

(defun log-coerce-some-expr-to-bool (index)
  (when *record-proof-logs-flag*
    ;; (some vars P)
    (log-some-to-if-form index)
    ;; (if (all vars (if P (false) (true))) (false) (true))
    (push-proof-log 'if-true (list* 2 2 (if-test-index)) *true* t)
    (push-proof-log 'if-false (list* 3 2 (if-test-index)) *false* t)
    ;; (if (all vars
    ;;       (if P (if (true) (false) (true)) (if (false) (false) (true))))
    ;;     (false)
    ;;     (true))
    (push-proof-log 'case-analysis (cons 2 (if-test-index)) 1 t)
    ;; (if (all vars (if (if P (true) (false)) (false) (true)))
    ;;     (false)
    ;;     (true))
    (log-if-form-to-some index)
    ;; (some vars (if P (true) (false)))
    ))

(defun log-remove-bool-coercion-from-some-expr (index)
  (when *record-proof-logs-flag*
    ;; (some vars (if P (true) (false)))
    (log-some-to-if-form index)
    ;; (if (all vars (if (if P (true) (false)) (false) (true)))
    ;;     (false)
    ;;     (true))
    (push-proof-log 'case-analysis (cons 2 (if-test-index)) 1)
    ;; (if (all vars
    ;;       (if P (if (true) (false) (true)) (if (false) (false) (true))))
    ;;     (false)
    ;;     (true))
    (push-proof-log 'if-true (list* 2 2 (if-test-index)))
    (push-proof-log 'if-false (list* 3 2 (if-test-index)))
    ;; (if (all vars (if P (false) (true))) (false) (true))
    (log-if-form-to-some index)
    ;; (some vars P)
    ))

(defun log-coerce-if-test-to-bool (index)
  ;; (if test L R)
  (push-proof-log 'if-test index)
  ;; (if (= test (true)) L R)
  (push-proof-log 'is-boolean (if-test-index))
  ;; (if (if (= test (true)) (true) (false)) L R)
  (push-proof-log 'if-test (if-test-index) t)
  ;; (if (if test (true) (false)) L R)
  )

(defun log-remove-bool-coercion-from-if-test (index)
  ;; (if (if test (true) (false)) L R)
  (push-proof-log 'case-analysis index 1)
  ;; (if test
  ;;     (if (true) L R)
  ;;     (if (false) L R))
  (push-proof-log 'if-true (if-left-index))
  (push-proof-log 'if-false (if-right-index))
  ;; (if test L R)
  )

;;; Some Boolean coercion conversions.
  
(defun log-double-negation-is-coercion (index)
  ;; (if (if expr (false) (true)) (false) (true))
  (push-proof-log 'case-analysis index 1)
  ;; (if expr (if (false) (false) (true)) (if (true) (false) (true)))
  (push-proof-log 'if-false (if-left-index))
  (push-proof-log 'if-true (if-right-index))
  ;; (if expr (true) (false))
  )

(defun log-bool-coercion-is-double-negation (index)
  ;; (if expr (true) (false))
  (push-proof-log 'if-true (if-right-index) *true* t)
  ;; (if expr (true) (if (true) (false) (true)))
  (push-proof-log 'if-false (if-left-index) *false* t)
  ;; (if expr (if (false) (false) (true)) (if (true) (false) (true)))
  (push-proof-log 'case-analysis index 1 t)
  ;; (if (if expr (false) (true)) (false) (true))
  )


;;; Argument positions of connectives are also Boolean contexts.
;;; The proof logs for these are inefficient.
;;; Luckily, it is used sparingly and only in the CASES and INDUCT commands.

(defun log-coerce-to-bool-inside-connective (formula n index)
  (when *record-proof-logs-flag*
    (when (and (or (and-p formula)
		   (or-p formula)
		   (and (implies-p formula) (= (length formula) 3))
		   (and (not-p formula) (= (length formula) 2)))
	       (<= 1 n)
	       (< n (length formula)))
      (cond ((not-p formula)
	     (log-coerce-to-bool-inside-connective-strict formula n index)
	     )
	    ((= (length formula) 2)
	     (push-proof-log 'syntax index)
	     ;; (and expr (true)) or (or expr (false))
	     (log-coerce-to-bool-inside-connective-strict
	      (list (car formula) (second formula)
		    (if (and-p formula) *true* *false*))
	      n index)
	     (push-proof-log 'syntax index t)
	     ;; (and (if expr (true) (false))) or (or (if expr (true) (false)))
	     )
	    ((= (length formula) 3)
	     (log-coerce-to-bool-inside-connective-strict formula n index))
	    (t ; unexpanded and or or
	     (push-proof-log 'syntax index)
	     (cond ((= n 1)
		    (log-coerce-to-bool-inside-connective-strict
		     formula n index))
		   (t
		    (log-coerce-to-bool-inside-connective
		     (cons (car formula) (cddr formula)) (- n 1)
		     (cons 2 index))))
	     (push-proof-log 'syntax index t)
	     )))))

;;; must only be called from log-coerce-to-bool-inside-connective
(defun log-coerce-to-bool-inside-connective-strict (formula n index)
  ;; Formula must be one of the forms:
  ;;   (and expr1 expr2)
  ;;   (or expr1 expr2)
  ;;   (implies expr1 expr2)
  ;; 1 <= n <= 2
  (let ((op (car formula))
	(expr2 (third formula)))
    (let ((coerced-expr-2 (make-if expr2 *true* *false*)))
      (when *record-proof-logs-flag*
	(cond ((and-p formula)
	       ;; (and expr1 expr2)
	       (push-proof-log 'syntax index)
	       ;; (if expr1 (if expr2 (true) (false)) (false))
	       (cond ((= n 1)
		      (log-coerce-if-test-to-bool index)
		      ;; (if (if expr1 (true) (false))
		      ;;     (if expr2 (true) (false))
		      ;;     (false))
		      (push-proof-log 'syntax index t)
		      ;; (and (if expr1 (true) (false)) expr2)
		      )
		     (t ; (= n 2)
		      (push-proof-log 'is-boolean (if-left-index))
		      ;; (if expr1
		      ;;     (if (if expr2 (true) (false)) (true) (false))
		      ;;     (false))
		      (push-proof-log 'syntax index t)
		      ;; (and expr1 (if expr2 (true) (false)))
		      )))
	      ((or-p formula)
	       ;; (or expr1 expr2)
	       (push-proof-log 'syntax index)
	       ;; (if expr1 (true) (if expr2 (true) (false)))
	       (cond ((= n 1)
		      (log-coerce-if-test-to-bool index)
		      ;; (if (if expr1 (true) (false))
		      ;;     (true)
		      ;;     (if expr2 (true) (false)))
		      (push-proof-log 'syntax index t)
		      ;; (and (if expr1 (true) (false)) expr2)
		      )
		     (t ; (= n 2)
		      (push-proof-log 'is-boolean (if-right-index))
		      ;; (if expr1
		      ;;     (true)
		      ;;     (if (if expr2 (true) (false)) (true) (false)))
		      (push-proof-log 'syntax index t)
		      ;; (or expr1 (if expr2 (true) (false)))
		      )))
	      ((implies-p formula)
	       ;; (implies expr1 expr2)
	       (push-proof-log 'syntax index)
	       ;; (if expr1 (if expr2 (true) (false)) (true))
	       (cond ((= n 1)
		      (log-coerce-if-test-to-bool index)
		      ;; (if (if expr1 (true) (false))
		      ;;     (if expr2 (true) (false))
		      ;;     (true))
		      (push-proof-log 'syntax index t)
		      ;; (implies (if expr1 (true) (false)) expr2)
		      )
		     (t ; (= n 2)
		      (push-proof-log 'is-boolean (if-left-index))
		      ;; (if expr1
		      ;;     (if (if expr2 (true) (false)) (true) (false))
		      ;;     (true))
		      (push-proof-log 'syntax index t)
		      ;; (implies expr1 (if expr2 (true) (false)))
		      )))
	      ((not-p formula)
	       (push-proof-log 'syntax index)
	       ;; (if expr (false) (true))
	       (log-coerce-if-test-to-bool index)
	       ;; (if (if expr (true) (false)) (false) (true))
	       (push-proof-log 'syntax index t)
	       ;; (not (if expr (true) (false)))
	       )
	      )))))

(defun log-remove-bool-coercion-from-inside-connective (formula n index)
  ;; (op expr1 expr2 ... (if expri (true) (false)) ... exprn)
  (when *record-proof-logs-flag*
    (when (and (or (and-p formula)
		   (or-p formula)
		   (and (implies-p formula) (= (length formula) 3))
		   (and (not-p formula) (= (length formula) 2)))
	       (<= 1 n)
	       (< n (length formula)))
      (cond ((not-p formula)
	     (log-remove-bool-coercion-from-inside-connective-strict
	      formula n index))
	    ((= (length formula) 2)
	     (push-proof-log 'syntax index)
	     ;; (and (if expr (true) (false)) (true))
	     ;;   or (or (if expr (true) (false)) (false))
	     (log-remove-bool-coercion-from-inside-connective-strict
	      (list (car formula) (second formula)
		    (if (and-p formula) *true* *false*))
	      1 index)
	     (push-proof-log 'syntax index t)
	     ;; (and (if expr (true) (false))) or (or (if expr (true) (false)))
	     )
	    ((= (length formula) 3)
	     (log-remove-bool-coercion-from-inside-connective-strict
	      formula n index))
	    (t ; unexpanded and or or
	     (push-proof-log 'syntax index)
	     (cond ((= n 1)
		    (log-remove-bool-coercion-from-inside-connective-strict
		     formula n index))
		   (t
		    (log-remove-bool-coercion-from-inside-connective
		     (cons (car formula) (cddr formula)) (- n 1)
		     (cons 2 index))))
	     (push-proof-log 'syntax index t)
	     )))))

;;; must only be called from log-remove-bool-coercion-from-inside-connective
(defun log-remove-bool-coercion-from-inside-connective-strict (formula n index)
  ;; Formula must be one of the forms:
  ;;   (and (if expr1 (true) (false)) expr2)
  ;;   (and expr1 (if expr2 (true) (false)))
  ;;   (or (if expr1 (true) (false)) expr2)
  ;;   (or expr1 (if expr2 (true) (false)))
  ;;   (implies (if expr1 (true) (false)) expr2)
  ;;   (implies expr1 (if expr2 (true) (false)))
  ;; n is 1 or 2, depending on which form above is to be transformed.
  (when *record-proof-logs-flag*
    (cond ((and-p formula)
	   ;; (and left right)
	   (push-proof-log 'syntax index)
	   ;; (if left (if expr2 (true) (false)) (false))
	   (cond ((= n 1)
		  ;; left is (if expr1 (true) (false))
		  ;; right is expr2
		  (push-proof-log 'case-analysis index 1)
		  ;; (if expr1
		  ;;     (if (true) (if expr2 (true) (false)) (false))
		  ;;     (if (false) (if expr2 (true) (false)) (false)))
		  (push-proof-log 'if-true (if-left-index))
		  (push-proof-log 'if-false (if-right-index));
		  ;; (if expr1 (if expr2 (true) (false) (false)))
		  (push-proof-log 'syntax index t)
		  ;; (and expr1 expr2)
		  )
		 (t ; (= n 2)
		  ;; left is expr1
		  ;; right is (if expr2 (true) (false))
		  ;; (if expr1
		  ;;     (if (if expr2 (true) (false)) (true) (false))
		  ;;     (false))
		  (push-proof-log 'is-boolean (if-left-index) t)
		  ;; (if expr1 (if expr2 (true) (false)) (false))
		  (push-proof-log 'syntax index t)
		  ;; (and expr1 expr2)
		  )))
	  ((or-p formula)
	   ;; (or left right)
	   (push-proof-log 'syntax index)
	   ;; (if left (true) (if right (true) (false)))
	   (cond ((= n 1)
		  ;; left is (if expr1 (true) (false))
		  ;; right is expr2
		  (push-proof-log 'case-analysis index 1)
		  ;; (if expr1
		  ;;     (if (true) (true) (if expr2 (true) (false)))
		  ;;     (if (false) (true) (if expr2 (true) (false))))
		  (push-proof-log 'if-true (if-left-index))
		  (push-proof-log 'if-false (if-right-index))
		  ;; (if expr1 (true) (if expr2 (true) (false)))
		  (push-proof-log 'syntax index t)
		  ;; (or expr1 expr2)
		  )
		 (t ; (= n 2)
		  ;; left is expr1
		  ;; right is (if expr2 (true) (false))
		  (push-proof-log 'is-boolean (if-right-index) t)
		  ;; (if expr1 (true) (if expr2 (true) (false)))
		  (push-proof-log 'syntax index t)
		  ;; (or expr1 expr2)
		  )))
	  ((implies-p formula)
	   ;; (implies left right)
	   (push-proof-log 'syntax index)
	   ;; (if left (if right (true) (false)) (true))
	   (cond ((= n 1)
		  ;; left is (if expr1 (true) (false))
		  ;; right is expr2
		  (push-proof-log 'case-analysis index 1)
		  ;; (if expr1
		  ;;     (if (true) (if expr2 (true) (false)) (true))'
		  ;;     (if (false) (if expr2 (true) (false)) (true)))
		  (push-proof-log 'if-true (if-left-index))
		  (push-proof-log 'if-false (if-right-index))
		  ;; (if expr1 (if expr2 (true) (false)) (true))
		  (push-proof-log 'syntax index t)
		  ;; (implies expr1 expr2)
		  )
		 (t ; (= n 2)
		  ;; left is expr1
		  ;; right is (if expr2 (true) (false))
		  (push-proof-log 'is-boolean (if-left-index) t)
		  ;; (if expr1 (if expr2 (true) (false)) (true))
		  (push-proof-log 'syntax index t)
		  ;; (implies expr1 expr2)
		  )))
	  ((not-p formula)
	   (push-proof-log 'syntax index)
	   ;; (if (if expr (true) (false)) (false) (true))
	   (push-proof-log 'case-analysis index 1)
	   ;; (if expr (if (true) (false) (true)) (if (false) (false) (true)))
	   (push-proof-log 'if-true (if-left-index))
	   (push-proof-log 'if-false (if-right-index))
	   ;; (if expr (false) (true))
	   (push-proof-log 'syntax index t)
	   )
	  )))

;;; ==================== Propositional Reasoning =====================


(defun log-if-negate-test (index)
  (when *record-proof-logs-flag*
    ;; (if (if a (false) (true)) b c)
    (push-proof-log 'case-analysis index 1)
    ;; (if a (if (false) b c) (if (true) b c))
    (push-proof-log 'if-false (if-left-index))
    ;; (if a c (if (true) b c))
    (push-proof-log 'if-true (if-right-index))
    ;; (if a c b)
    ))

(defun log-and-false (n args index)
  (cond ((> args 2)
	 (push-proof-log 'syntax index)
	 (cond ((= n 1)
		;; (and (false) (and ...))
		(push-proof-log 'syntax index)
		(push-proof-log 'if-false index)
		;; (false)
		)
	       (t
		(log-and-false (- n 1) (- args 1) (and-right-index))
		;; (and ? (false))
		(push-proof-log 'syntax index)
		(push-proof-log 'if-false (if-left-index))
		(push-proof-log 'if-equal index)
		;; (false)
		)))
	((= args 2)
	 (cond ((= n 1)
		;; (and (false) ?)
		(push-proof-log 'syntax index)
		(push-proof-log 'if-false index)
		;; (false)
		)
	       (t
		;; (and ? (false))
		(push-proof-log 'syntax index)
		(push-proof-log 'if-false (if-left-index))
		(push-proof-log 'if-equal index)
		;; (false)
		)))
	((= args 1)
	 ;; (and (false))
	 (push-proof-log 'syntax index)
	 (push-proof-log 'syntax index)
	 ;; (if (false) (if (true) (true) (false)) (false))
	 (push-proof-log 'if-false index)
	 ;; (false)
	 )))

(defun log-and-true (n args index)
  (cond ((> args 2)
	 (push-proof-log 'syntax index)
	 (cond ((= n 1)
		;; (and (true) (and ...))
		(push-proof-log 'syntax index)
		(push-proof-log 'if-true index)
		(push-proof-log 'is-boolean index t)
		;; (and ...)
		)
	       (t
		;; (and expr1 (and ...))
		(log-and-true (- n 1) (- args 1) (and-right-index))
		(cond ((> args 3)
		       (push-proof-log 'syntax index t)
		       ;; (and expr1 expr2 ...)
		       )
		      (t
		       ;; (and expr1 (and expr2))
		       (push-proof-log 'syntax (and-right-index))
		       (push-proof-log 'syntax (and-right-index))
		       (push-proof-log 'if-true (cons 2 (and-right-index)))
		       ;; (and expr (if expr2 (true) (false)))
		       (push-proof-log 'syntax index)
		       (push-proof-log 'is-boolean (if-left-index) t)
		       (push-proof-log 'syntax index t)
		       ;; (and expr1 expr2)
		       )))))
	((= args 2)
	 (cond ((= n 1)
		(push-proof-log 'syntax index)
		(push-proof-log 'if-true index)
		;; (if expr (true) (false))
		(push-proof-log 'is-boolean (if-left-index))
		(push-proof-log 'syntax index t)
		(push-proof-log 'syntax index t)
		;; (and expr)
		)
	       (t
		(push-proof-log 'syntax index t)
		;; (and expr)
		)))
	(t
	 (push-proof-log 'syntax index)
	 (push-proof-log 'syntax index t)
	 ;; (and)
	 )))
		       

(defun log-or-true (n args index)
  (cond ((> args 2)
	 (push-proof-log 'syntax index)
	 (cond ((= n 1)
		;; (or (true) (or ...))
		(push-proof-log 'syntax index)
		(push-proof-log 'if-true index)
		;; (true)
		)
	       (t
		(log-or-true (- n 1) (- args 1) (or-right-index))
		;; (or ? (true))
		(push-proof-log 'syntax index)
		(push-proof-log 'if-true (if-right-index))
		(push-proof-log 'if-equal index)
		;; (true)
		)))
	((= args 2)
	 (cond ((= n 1)
		;; (or (true) ?)
		(push-proof-log 'syntax index)
		(push-proof-log 'if-true index)
		;; (true)
		)
	       (t
		;; (or ? (true))
		(push-proof-log 'syntax index)
		(push-proof-log 'if-true (if-right-index))
		(push-proof-log 'if-equal index)
		;; (true)
		)))
	((= args 1)
	 ;; (or (true))
	 (push-proof-log 'syntax index)
	 (push-proof-log 'syntax index)
	 ;; (if (true) (true) (if (true) (true) (false)))
	 (push-proof-log 'if-true index)
	 ;; (true)
	 )))


(defun log-or-false (n args index)
  (cond ((> args 2)
	 (push-proof-log 'syntax index)
	 (cond ((= n 1)
		;; (or (false) (or ...))
		(push-proof-log 'syntax index)
		(push-proof-log 'if-false index)
		(push-proof-log 'is-boolean index t)
		;; (or ...)
		)
	       (t
		;; (or expr1 (or ...))
		(log-or-false (- n 1) (- args 1) (or-right-index))
		(cond ((> args 3)
		       (push-proof-log 'syntax index t)
		       ;; (or expr1 expr2 ...)
		       )
		      (t
		       ;; (or expr1 (or expr2))
		       (push-proof-log 'syntax (or-right-index))
		       (push-proof-log 'syntax (or-right-index))
		       (push-proof-log 'if-false (cons 3 (or-right-index)))
		       ;; (or expr (if expr2 (true) (false)))
		       (push-proof-log 'syntax index)
		       (push-proof-log 'is-boolean (if-right-index) t)
		       (push-proof-log 'syntax index t)
		       ;; (or expr1 expr2)
		       )))))
	((= args 2)
	 (cond ((= n 1)
		(push-proof-log 'syntax index)
		(push-proof-log 'if-false index)
		;; (if expr (true) (false))
		(push-proof-log 'is-boolean (if-right-index))
		(push-proof-log 'syntax index t)
		(push-proof-log 'syntax index t)
		;; (or expr)
		)
	       (t
		(push-proof-log 'syntax index t)
		;; (or expr)
		)))
	(t
	 (push-proof-log 'syntax index)
	 (push-proof-log 'syntax index t)
	 ;; (or)
	 )))


(defun log-and-0 (index)    
  (when *record-proof-logs-flag*
    ;; (and)
    (push-proof-log 'syntax index)
    ;; (and (true) (true))
    (push-proof-log 'syntax index)
    ;; (if (true) (if (true) (true) (false)) (false))
    (push-proof-log 'if-true index)
    (push-proof-log 'if-true index)
    ;; (true)
    ))

(defun log-or-0 (index)    
  (when *record-proof-logs-flag*
    ;; (or)
    (push-proof-log 'syntax index)
    ;; (or (false) (false))
    (push-proof-log 'syntax index)
    ;; (if (false) (true) (if (false) (true) (false)))
    (push-proof-log 'if-false index)
    (push-proof-log 'if-false index)
    ;; (false)
    ))

(defun log-and-1 (index)    
  (when *record-proof-logs-flag*
    ;; (and expr)
    (push-proof-log 'syntax index)
    ;; (and expr (true))
    (push-proof-log 'syntax index)
    ;; (if expr (if (true) (true) (false)) (false))
    (push-proof-log 'if-true (if-left-index))
    ;; (if expr (true) (false))
    ))

(defun log-or-1 (index)    
  (when *record-proof-logs-flag*
    ;; (or expr)
    (push-proof-log 'syntax index)
    ;; (or expr (false))
    (push-proof-log 'syntax index)
    ;; (if expr (true) (if (false) (true) (false)))
    (push-proof-log 'if-false (if-right-index))
    ;; (if expr (true) (false))
    ))

(defun log-not-not (index)
  ;; (not (not expr))
  (push-proof-log 'syntax (not-expr-index))
  (push-proof-log 'syntax index)
  ;; (if (if expr (false) (true)) (false) (true))
  (push-proof-log 'case-analysis index 1)
  ;; (if expr (if (false) (false) (true)) (if (true) (false) (true)))
  (push-proof-log 'if-false (if-left-index))
  (push-proof-log 'if-true (if-right-index))
  ;; (if expr (true) (false))
  )

(defun log-if-to-and-or (formula index)
  ;; (if a b c)
  (push-proof-log 'if-false (if-right-index) *true* t)
  ;; (if a b (if (false) (true) c))
  (push-proof-log 'if-true (cons 1 (if-right-index)) *true* t)
  ;; (if a b (if (if (true) (false) (true)) (true) c))
  (push-proof-log 'look-up (list* 1 1 (if-right-index))
		  (make-if (if-test formula) *false* *true*))
  ;; (if a b (if (if (if a (false) (true)) (false) (true)) (true) c))
  (push-proof-log 'case-analysis (cons 1 (if-right-index)) 1)
  (push-proof-log 'if-false (list* 2 1 (if-right-index)))
  (push-proof-log 'if-true (list* 3 1 (if-right-index)))
  ;; (if a b (if (if a (true) (false)) (true) c))
  (log-remove-bool-coercion-from-if-test (if-right-index))
  ;; (if a b (if a (true) c))
  (push-proof-log 'if-true (if-right-index) *false* t)
  ;; (if a b (if (true) (if a (true) c) (false)))
  (push-proof-log 'is-boolean (if-left-index))
  ;; (if a (if b (true) (false)) (if (true) (if a (true) c) (false)))
  (push-proof-log 'if-true (cons 2 (if-left-index)) (if-right formula) t)
  ;; (if a
  ;;     (if b (if (true) (true) c) (false))
  ;;     (if (true) (if a (true) c) (false)))
  (push-proof-log 'look-up (list* 1 2 (if-left-index)) (if-test formula))
  (push-proof-log 'case-analysis index 1 t)
  ;; (if (if a b (true)) (if a (true) c) (false))
  (log-coerce-if-test-to-bool (if-test-index))
  (log-bool-coercion-is-double-negation (cons 1 (if-test-index)))
  ;; (if (if (if (if a (false) (true)) (false) (true)) b (true))
  ;;     (if a (true) c)
  ;;     (false))
  (push-proof-log 'case-analysis (if-test-index) 1)
  (push-proof-log 'if-false (cons 2 (if-test-index)))
  (push-proof-log 'if-true (cons 3 (if-test-index)))
  ;; (if (if (if a (false) (true)) (true) b) (if a (true) c) (false))
  (push-proof-log 'syntax (cons 1 (if-test-index)) t)
  (push-proof-log 'is-boolean (cons 3 (if-test-index)))
  (push-proof-log 'syntax (if-test-index) t)
  ;; (if (or (not a) b) (if a (true) c) (false))
  (push-proof-log 'is-boolean (cons 3 (if-left-index)))
  (push-proof-log 'syntax (if-left-index) t)
  (push-proof-log 'is-boolean (if-left-index))
  (push-proof-log 'syntax index t)
  ;; (and (or (not a) b) (or a c))
  )
  

;;; Should only be called if bool-p or both b and c are boolean.

(defun log-cases-if (formula bool-p index)
  ;; (if a b c)
  (push-proof-log 'if-false (if-right-index) *true* t)
  ;; (if a b (if (false) (true) c))
  (log-inverse-look-up-false-for-coercion
   (make-if (if-test formula) *true* *false*) (cons 1 (if-right-index)))
  ;; (if a b (if (if a (true) (false)) (true) c))
  (log-remove-bool-coercion-from-if-test (if-right-index))
  ;; (if a b (if a (true) c)
  (if (bool-p (if-left formula))
      (push-proof-log 'is-boolean (if-left-index))
    (log-coerce-expr-in-boolean-context bool-p (if-left-index)))
  ;; (if a (if b (true) (false)) (if a (true) c))
  (push-proof-log 'if-true (if-right-index) *false* t)
  ;; (if a
  ;;     (if b (true) (false))
  ;;     (if (true) (if a (true) c) (false)))
  (push-proof-log 'if-true (cons 2 (if-left-index)) (if-right formula) t)
  ;; (if a
  ;;     (if b (if (true) (true) c) (false))
  ;;     (if (true) (if a (true) c) (false)))
  (push-proof-log 'look-up (list* 1 2 (if-left-index)) (if-test formula))
  ;; (if a
  ;;     (if b (if a (true) c) (false))
  ;;     (if (true) (if a (true) c) (false)))
  (push-proof-log 'case-analysis index 1 t)
  ;; (if (if a b (true)) (if a (true) c) (false))
  (if (bool-p (if-left formula))
      (push-proof-log 'is-boolean (cons 2 (if-test-index)))
    (log-coerce-expr-in-boolean-context
     (make-context-for-bool-p
      (make-if (make-if (if-test formula) (if-left formula) *true*)
	       (make-if (if-test formula) *true* (if-right formula))
	       *false*)
      index)
     (cons 2 (if-test-index))))
  ;; (if (if a (if b (true) (false)) (true)) (if a (true) c) (false))
  (push-proof-log 'syntax (if-test-index) t)
  ;; (if (implies a b) (if a (true) c) (false))
  (push-proof-log 'if-false (cons 2 (if-left-index)) (if-right formula) t)
  (push-proof-log 'if-true (cons 3 (if-left-index)) *true* t)
  ;; (if (implies a b)
  ;;     (if a (if (false) c (true)) (if (true) c (true)))
  ;;     (false))
  (push-proof-log 'case-analysis (if-left-index) 1 t)
  ;; (if (implies a b) (if (if a (false) (true)) c (true)) (false))
  (push-proof-log 'syntax (cons 1 (if-left-index)) t)
  ;; (if (implies a b) (if (not a) c (true)) (false))
  (if (bool-p (if-right formula))
      (push-proof-log 'is-boolean (cons 2 (if-left-index)))
    (log-coerce-expr-in-boolean-context bool-p (cons 2 (if-left-index))))
  ;; (if (implies a b) (if (not a) (if c (true) (false)) (true)) (false))
  (push-proof-log 'syntax (if-left-index) t)
  ;; (if (implies a b) (implies (not a) c) (false))
  (push-proof-log 'is-boolean (if-left-index))
  (push-proof-log 'syntax index t)
  ;; (and (implies a b) (implies (not a) c))
  )
  
(defun log-implies-to-or (index)
  ;; (implies x y)
  (push-proof-log 'syntax index)
  ;; (if x (if y (true) (false)) (true))
  (log-coerce-if-test-to-bool index)
  ;; (if (if x (true) (false)) (if y (true) (false)) (true))
  (log-bool-coercion-is-double-negation (if-test-index))
  ;; (if (if (if x (false) (true)) (false) (true)) (if y (true) (false)) (true))
  (push-proof-log 'case-analysis index 1)
  ;; (if (if x (false) (true))
  ;;     (if (false) (if y (true) (false)) (true))
  ;;     (if (true) (if y (true) (false)) (true)))
  (push-proof-log 'if-false (if-left-index))
  (push-proof-log 'if-true (if-right-index))
  ;; (if (if x (false) (true)) (true) (if y (true) (false)))
  (push-proof-log 'syntax (if-test-index) t)
  (push-proof-log 'syntax index t)
  ;; (or (not x) y)
  )


(defun log-implies-or-to-implies-and-aux (n conclusion index)
  ;; (or x1 ... xn+1)
  (cond ((> n 1)
	 (push-proof-log 'syntax index)
	 ;; (or x1 (or x2 ... xn+1))
	 (log-implies-or-to-implies-and-aux (- n 1) conclusion (or-right-index))
	 ;; (or x1 (implies (and (not x2) ...) xn+1))
	 (push-proof-log 'syntax index)
	 ;; (if x1 (true) (if (implies ...) (true) (false)))
	 (log-coerce-if-test-to-bool index)
	 (log-bool-coercion-is-double-negation (if-test-index))
	 ;; (if (if (if x1 (false) (true)) (false) (true)) (true) ...)
	 (push-proof-log 'case-analysis index 1)
	 ;; (if (if x1 (false) (true))
	 ;;     (if (false) (true) (if (implies ...) (true) (false)))
	 ;;     (if (true) (true) (if (implies ...) (true) (false)))
	 (push-proof-log 'syntax (if-test-index) t)
	 (push-proof-log 'if-false (if-left-index))
	 (push-proof-log 'if-true (if-right-index))
	 ;; (if (not x1) (if (implies ...) (true) (false)) (true))
	 (push-proof-log 'syntax index t)
	 ;; (implies (not x1) (implies ...))
	 (log-unnest-implies conclusion index)
	 ;; (implies (and (not x1) ...) xn+1)
	 )
	(t
	 ;; (or x1 x2)
	 (push-proof-log 'syntax index)
	 ;; (if x1 (true) (if x2 (true) (false)))
	 (log-coerce-if-test-to-bool index)
	 (log-bool-coercion-is-double-negation (if-test-index))
	 (push-proof-log 'case-analysis index 1)
	 ;; (if (if x1 (false) (true))
	 ;;     (if (false) (true) (if x2 (true) (false)))
	 ;;     (if (true) (true) (if x2 (true) (false))))
	 (push-proof-log 'syntax (if-test-index) t)
	 (push-proof-log 'if-false (if-left-index))
	 (push-proof-log 'if-true (if-right-index))
	 ;; (if (not x1) (if x2 (true) (false)) (true))
	 (push-proof-log 'syntax index t)
	 ;; (implies (not x1) x2)
	 )))

(defun log-implies-or-to-implies-and-aux-2 (n index)
  (when (> n 2)
    ;; (and x1 (and x2 ...))
    (log-implies-or-to-implies-and-aux-2 (- n 1) (and-right-index))
    (push-proof-log 'syntax index t)))

(defun log-implies-or-to-implies-and (formula index)
  ;; (implies h (or d1 d2 ... dn))
  (let ((first-hyp (implies-left formula))
	(negated-hyps (butlast (cdr (implies-right formula))))
	(conclusion (car (last (implies-right formula)))))
    (log-implies-or-to-implies-and-aux
     (length negated-hyps) conclusion (implies-right-index))
    ;; (implies h (implies (and (not d1) (and (not d2) ...)) dn))
    (log-unnest-implies conclusion index)
    ;; (implies (and h1 (and (not d1) (and (not d2) ,,,))) dn)
    (log-implies-or-to-implies-and-aux-2 (+ (length negated-hyps) 1)
					 (implies-left-index))
    ;; (implies (and h1 (not d1) (not d2) ...) dn)
    ))

(defun log-=-true-left-to-if (expr index)
  ;; (= (true) expr)
  (log-commute (make-= *true* expr) index)
  (push-proof-log 'is-boolean index)
  ;; (if (= expr (true)) (true) (false))
  (push-proof-log 'if-test index t)
  ;; (if expr (true) (false))
  )

(defun log-=-true-right-to-if (index)
  ;; (= expr (true))
  (push-proof-log 'is-boolean index)
  (push-proof-log 'if-test index t)
  )

(defun log-=-false-left-to-if (expr index)
  ;; (= (false) expr)
  (push-proof-log 'if-equal index expr t)
  ;; (if expr (= (false) expr) (= (false) expr))
  (push-proof-log 'look-up (cons 2 (if-left-index)) *true*)
  (push-proof-log 'compute (if-left-index))
  ;; (if expr (false) (= (false) expr))
  (push-proof-log 'is-boolean (cons 2 (if-right-index)))
  (log-bool-coercion-is-double-negation (cons 2 (if-right-index)))
  ;; (if expr (false) (= (false) (if (if expr (false) (true)) (false) (true))))
  (push-proof-log 'look-up (list* 1 2 (if-right-index)) *true*)
  ;; (if expr (false) (= (false) (if (true) (false) (true))))
  (push-proof-log 'if-true (cons 2 (if-right-index)))
  (push-proof-log 'compute (if-right-index))
  ;; (if expr (false) (true))
  )

(defun log-=-false-right-to-if (expr index)
  ;; (= expr (false))
  (push-proof-log 'if-equal index expr t)
  ;; (if expr (= expr (false)) (= expr (false)))
  (push-proof-log 'look-up (cons 1 (if-left-index)) *true*)
  (push-proof-log 'compute (if-left-index))
  ;; (if expr (false) (= expr (false)))
  (push-proof-log 'is-boolean (cons 1 (if-right-index)))
  (log-bool-coercion-is-double-negation (cons 1 (if-right-index)))
  ;; (if expr (false) (= (if (if expr (false) (true)) (false) (true)) (false)))
  (push-proof-log 'look-up (list* 1 1 (if-right-index)) *true*)
  ;; (if expr (false) (= (if (true) (false) (true)) (false)))
  (push-proof-log 'if-true (cons 1 (if-right-index)))
  (push-proof-log 'compute (if-right-index))
  ;; (if expr (false) (true))
  )
  


;;; ================== Lookups =========================

(defun log-look-up-false-for-coercion (index)
  ;; formula is (if expr (true) (false))
  (log-bool-coercion-is-double-negation index)
  ;; (if (if expr (false) (true)) (false) (true))
  (push-proof-log 'look-up (if-test-index) *true*)
  ;; (if (true) (false) (true))
  (push-proof-log 'if-true index)
  ;; (false)
  )

(defun log-inverse-look-up-false-for-coercion (formula index)
  ;; (false)
  (push-proof-log 'if-true index *true* t)
  ;; (if (true) (false) (true))
  (push-proof-log 'look-up (if-test-index)
		  (make-if (if-test formula) *false* *true*))
  ;; (if (if expr (true) (false)) (false) (true))
  (log-double-negation-is-coercion index)
  ;; (if expr (true) (false))
  )

;;; It is assumed that (if expr (false) (true)) is in context
(defun log-look-up-false (index)
  ;; expr must be boolean
  (push-proof-log 'is-boolean index)
  ;; (if expr (true) (false))
  (log-bool-coercion-is-double-negation index)
  ;; (if (if expr (false) (true)) (false) (true))
  (push-proof-log 'look-up (if-test-index) *true*)
  ;; (if (true) (false) (true))
  (push-proof-log 'if-true index)
  ;; (false)
  )

(defun log-inverse-look-up-false (original index)
  ;; (false)
  (push-proof-log 'if-true index *true* t)
  ;; (if (true) (false) (true))
  (push-proof-log 'look-up (if-test-index) (make-if original *false* *true*))
  ;; (if (if expr (false) (true)) (false) (true))
  (log-double-negation-is-coercion index)
  (push-proof-log 'is-boolean index t)
  ;; expr
  )


;;; =================== Boolean Context Coercion ======================



;;; The purpose of this function is to coerce appropriate trunks
;;; and leaves to boolean, such that the expr at index
;;; is coerced to boolean. Once the appropriate transformation
;;; is done on the coerced expr, a clean up must be performed.

(defun log-create-boolean-coercion (ckind cindex index)
  (cond ((= (length cindex) (length (cdr index)))
	 (cond ((eq (car ckind) 'all)
		;; cindex points to (all vars expr)
		;; index points to expr
		(log-coerce-all-expr-to-bool (second ckind) cindex)
		;; (all vars (if expr (true) (false)))
		)
	       ((eq (car ckind) 'some)
		;; cindex points to (some vars expr)
		;; index points to expr
		(log-coerce-some-expr-to-bool cindex)
		;; (some vars (if expr (true) (false)))
		)
	       ((eq (car ckind) 'if)
		;; cindex points to (if expr L R)
		;; index points to expr
		(log-coerce-if-test-to-bool cindex)
		;; (if (if expr (true) (false)) L R)
		)
	       ((or (eq (car ckind) 'and) (eq (car ckind) 'or)
		    (eq (car ckind) 'implies) (eq (car ckind) 'not))
		;; (op expr1 expr2 ... expri ... exprn)
		;; where op is and/or
		(log-coerce-to-bool-inside-connective ckind (car index) cindex)
		)
	       ))
	((< (length cindex) (length (cdr index)))
	 (log-create-boolean-coercion ckind cindex (cdr index))
	 ;; (cdr index) now points to the following:
	 ;; (if (if test L R) (true) (false))
	 (push-proof-log 'case-analysis (cdr index) 1)
	 ;; (if test (if L (true) (false)) (if R (true) (false)))
	 )))

;;; Cleaning up boolean coercion. Note that the expr at index must
;;; be of a boolean coercion.

(defun log-clean-up-boolean-coercion (ckind cindex index)
  (cond ((= (length cindex) (length (cdr index)))
	 (cond ((eq (car ckind) 'all)
		;; cindex points to (all vars (if expr (true) (false)))
		(log-remove-bool-coercion-from-all-expr cindex)
		;; (all vars expr)
		;; index now points to expr
		)
	       ((eq (car ckind) 'some)
		;; cindex points to (some vars (if expr (true) (false)))
		(log-remove-bool-coercion-from-some-expr cindex)
		;; (some vars expr)
		;; index now points to expr
		)
	       ((eq (car ckind) 'if)
		;; cindex points to (if (if expr (true) (false)) L R)
		(log-remove-bool-coercion-from-if-test cindex)
		;; (if expr L R)
		;; index now points to expr
		)
	       ((or (eq (car ckind) 'and) (eq (car ckind) 'or)
		    (eq (car ckind) 'implies) (eq (car ckind) 'not))
		;; cindex points to (or x1 x2 ... xi ... xn)
		;; index point to xi where i is determined by index
		(log-remove-bool-coercion-from-inside-connective
		 ckind (car index) cindex))
	       ))
	((< (length cindex) (length (cdr index)))
	 ;; (if test (if L (true) (false)) (if R (true) (false)))
	 (push-proof-log 'case-analysis (cdr index) 1 t)
	 ;; (if (if test L R) (true) (false))
	 (log-clean-up-boolean-coercion ckind cindex (cdr index))
	 )))

;;; Generate proof log sequence that converts an expression to
;;; a coerced boolean expression, based on the fact that it is
;;; in a boolean context.

(defun log-coerce-expr-in-boolean-context (bool-p index)
  (let ((context-kind (car bool-p))
	(context-index (second bool-p)))
    (log-create-boolean-coercion context-kind context-index index)
    ;; expr is now (if expr (true) (false))
    ;; other branches are also coerced to Boolean
    ;; (if expr (true) (false))
    ;; need to coerce again before cleaning up
    (push-proof-log 'is-boolean index)
    (log-clean-up-boolean-coercion context-kind context-index index)
    ;; (if expr (true) (false))
    ;; and all other branches have been restored
    ))

(defun log-remove-coercion-from-boolean-context (bool-p index)
  (let ((context-kind (car bool-p))
	(context-index (second bool-p)))
    (log-create-boolean-coercion context-kind context-index index)
    ;; (if expr (true) (false)) is now
    ;; (if (if expr (true) (false)) (true) (false))
    ;; other branches are also coerced to Boolean
    ;; (if expr (true) (false))
    ;; need to remove one coercion from double coercion before cleaning up
    (push-proof-log 'is-boolean index t)
    (log-clean-up-boolean-coercion context-kind context-index index)
    ;; (if expr (true) (false))
    ;; and all other branches have been restored
    ))
  

;;; Logs conversion of expr to false where expr appears in
;;; a Boolean context.

(defun log-look-up-false-in-boolean-context (bool-p index)
  (let ((context-kind (car bool-p))
	(context-index (second bool-p)))
    (log-create-boolean-coercion context-kind context-index index)
    ;; expr is now (if expr (true) (false))
    ;; other branches are also coerced to Boolean
    ;; (if expr (true) (false)
    (log-look-up-false-for-coercion index)
    ;; (false)
    ;; need to coerce first before cleaning up all coercions
    (push-proof-log 'is-boolean index)
    ;; (if (false) (true) (false))
    (log-clean-up-boolean-coercion context-kind context-index index)
    ;; (false)
    ;; and all other branches have been restored
    ))

(defun log-remove-coercion-for-boolean-or-bool-p (expr index bool-p)
  (if (bool-p expr)
      (push-proof-log 'is-boolean index t)
    (log-remove-coercion-from-boolean-context bool-p index)))

(defun log-coerce-expr-for-boolean-or-bool-p (expr index bool-p)
  (if (bool-p expr)
      (push-proof-log 'is-boolean index)
    (log-coerce-expr-in-boolean-context bool-p index)))

;;; ----- Utilities
;;; Not really proof logging but tightly coupled with it.

;;; Create context used for bool-p.
(defun make-context-for-bool-p (formula index)
  (cond ((all-p formula) (list (list 'all (all-vars formula)) index))
	((some-p formula) (list (list 'some (some-vars formula)) index))
	((or (and-p formula) (or-p formula) (implies-p formula) (not-p formula))
	 (list formula index))
	((if-p formula)
	 (list (list 'if) index))))

;;; Coerce expression to boolean if necessary, but log "removal"
;;; of coercion if not.
(defun coerce-to-bool (expr index &optional bool-p)
  (cond ((or (bool-p expr) bool-p)
         (when *record-proof-logs-flag*
	   (log-remove-coercion-for-boolean-or-bool-p expr index bool-p))
	 expr)
	(t (make-if expr *true* *false*))))
