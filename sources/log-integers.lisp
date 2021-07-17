
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


;;; =================== Proof Logging for Integers =================

;;; Code to log integer reasoning in the simplifier. Much of the code
;;; deals with conversion to "linear sum" form. As with other code that
;;; deals with proof logging, there is a lot of mundane book-keeping.


;;; Log transformation of (>= left right) to (>= sum 0),
;;; where left and right each is an arithmetic expression
;;; (i.e., application of +, *, -, negate, ord, or an
;;; integer literal).

(defun log-sum-conversion-of->= (node index)
  (let ((left-node (arg-1-node node))
        (right-node (arg-2-node node))
        (expr (e-node-attribute node)))
    ;; Start with (>= left right)
    (log-use-axiom-as-rewrite
     expr '>=.to.>=.zero `((= |)X| ,(second expr)) (= |)Y| ,(third expr)))
     index)
    ;; (if (= (type-of left) (int))
    ;;     (if (= (type-of right) (int))
    ;;         (>= (- left right) 0)
    ;;         (>= left right))
    ;;     (>= left right))
    (log-type-of-expr (e-node-attribute left-node) (cons 1 (if-test-index)))
    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)
    (log-type-of-expr (e-node-attribute right-node) (cons 1 (if-test-index)))
    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)
    ;; (>= (- left right) 0)
    (let ((sum (log-collect-terms
                (make-- (e-node-attribute left-node)
                        (e-node-attribute right-node))
                (cons 1 index))))
      ;; (>= sum 0)
      ;; Now, shift and normalize if necessary.
      (let ((the-gcd (apply #'gcd (mapcar #'cdr (cdr sum)))))
        (when (> the-gcd 1)
          (let ((diff (mod (car sum) the-gcd))
                (expr (raw-expr-of-sum sum)))
            (cond ((zerop diff)
                   (log-add-zero expr (cons 1 index))
                   ;; (>= (+ 0 sum) 0)
                   )
                  (t
                   (log-add-zero (car sum) (list* 1 1 index))
                   ;; (>= (+ (+ 0 c) rest) 0)
                   (log-convert-zero diff (list* 1 1 1 index))
                   ;; (>= (+ (+ (+ diff -diff) c) rest) 0)
                   (log-use-axiom-as-rewrite
                    `(+ (+ ,diff ,(- diff)) ,(car sum)) '+.associate.right
                    `((= |)X| ,diff) (= |)Y| ,(- diff)) (= |)Z| ,(car sum)))
		    (list* 1 1 index))
                   (push-proof-log 'compute (list* 2 1 1 index))
                   ;; (>= (+ (+ diff c-diff) rest) 0)
                   (log-use-axiom-as-rewrite
                    `(+ (+ ,diff ,(- (car sum) diff)) ,(third expr))
                    '+.associate-right
                    `((= |)X| ,diff) (= |)Y| ,(- (car sum) diff))
		      (= |)Z| ,(third expr)))
		    (cons 1 index))
                   ;; (>= (+ diff (+ c-diff rest)) 0)
                   ))
            (log-shift-and-normalize
             diff the-gcd (cons (- (car sum) diff) (cdr sum)) index)))))))



;;; Log transformation of expr to (+ 0 expr) where expr is either an
;;; addition, multiplication, or an integer literal.

(defun log-add-zero (expr index)
  ;; expr
  (push-proof-log 'if-equal index `(= ,expr (+ 0 ,expr)) t)
  (push-proof-log 'look-up (if-left-index) `(+ 0 ,expr))
  ;; (if (= expr (+ 0 expr)) (+ 0 expr) expr)
  (cond ((integerp expr)
         (push-proof-log 'compute (cons 2 (if-test-index))))
        (t
         (log-use-axiom-as-rewrite
          `(+ 0 ,expr) '+.zero.left `((= |)X| ,expr)) (cons 2 (if-test-index)))
         ;; (if (= expr (if (= (type-of expr) (int)) expr (+ 0 expr)))
         ;;     (+ 0 expr)
         ;;     expr)
         (log-type-of-expr expr (list* 1 1 2 (if-test-index)))
         (push-proof-log 'compute (list* 1 2 (if-test-index)))
         (push-proof-log 'if-true (cons 2 (if-test-index)))))
  ;; (if (= expr expr) (+ 0 expr) expr)
  (push-proof-log 'compute (if-test-index))
  (push-proof-log 'if-true index)
  ;; (+ 0 expr)
  )

;;; Log transformation of 0 to (+ diff -diff) where diff is an integer literal.

(defun log-convert-zero (diff index)
  ;; Start with 0.
  (push-proof-log 'if-equal index `(= 0 (+ ,diff ,(- diff))) t)
  ;; (if (= 0 (+ diff -diff)) 0 0)
  (push-proof-log 'look-up (if-left-index) `(+ ,diff ,(- diff)))
  ;; (if (= 0 (+ diff -diff)) (+ diff -diff) 0)
  (push-proof-log 'compute (cons 2 (if-test-index)))
  (push-proof-log 'compute (if-test-index))
  (push-proof-log 'if-true index)
  ;; (+ diff -diff)
  )



;;; Log transformation of (>= (+ diff sum) 0),
;;; first to (>= (+ diff (* k s)) 0),
;;; then to (>= s 0),
;;; where k > diff >= 0 and k divides coefficients of sum.

(defun log-shift-and-normalize (diff k sum index)
  ;; Start with (>= (+ diff sum) 0).
  (log-factor-out k sum (list* 2 1 index))
  ;; (>= (+ diff (* k s)) 0)
  (let ((s (raw-expr-of-sum
            (cons (quotient (car sum) k)
                  (mapcar #'(lambda (u) (cons (car u) (quotient (cdr u) k)))
                          (cdr sum))))))
    (log-use-axiom-as-rewrite
     `(>= (+ ,diff (* ,k ,s)) 0) 'normalize.>=
     `((= |)X| ,diff) (= |)Y| ,k) (= |)Z| ,s)) index)
    ;; (if (>= diff 0)
    ;;     (if (>= k (+ diff 1))
    ;;         (if (= (type-of s) (int))
    ;;             (>= s 0)
    ;;             (>= (+ diff (* k s)) 0))
    ;;         (>= (+ diff (* k s)) 0))
    ;;     (>= (+ diff (* k s)) 0))
    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)
    (push-proof-log 'compute (cons 2 (if-test-index)))
    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)
    ;; (if (= (type-of s) (int))
    ;;     (>= s 0)
    ;;     (>= (+ diff (* k s)) 0))
    (log-use-axiom-as-rewrite
     `(type-of ,s) '+.type-of-axiom `((= |)X| ,(second s)) (= |)Y| ,(third s)))
     (cons 1 (if-test-index)))
    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)
    ;; (>= s 0)
    )
  )



;;; Log transformation of sum to (* k s) where k is an integer not= 0
;;; that divides the coefficients of sum.

(defun log-factor-out (k sum index)
  (cond ((null (cdr sum))
	 (let ((cc (quotient (car sum) k)))
	   (push-proof-log 'if-equal index `(= ,(car sum) (* ,k ,cc)) t)
	   (push-proof-log 'look-up (if-left-index)
			   `(* ,k ,cc))
	   ;; (if (= c (* k cc)) (* k cc) c)
	   (push-proof-log 'compute (cons 2 (if-test-index)))
	   (push-proof-log 'compute (if-test-index))
	   (push-proof-log 'if-true index)))
	(t
	 (let ((cc (quotient (car sum) k))
	       (r (raw-expr-of-sum-aux
		   (mapcar #'(lambda (u) (cons (car u) (quotient (cdr u) k)))
			   (cdr sum)))))
	   ;; Start with sum which is (+ c rest)
	   (log-factor-out-aux
	    k (raw-expr-of-sum-aux (cdr sum)) (cons 2 index))
	   ;; (+ c (* k r))
	   (push-proof-log
	    'if-equal (cons 1 index) `(= ,(car sum) (* ,k ,cc)) t)
	   ;; (+ (if (= c (* k cc)) c c) r)
	   (push-proof-log 'look-up (list* 2 1 index) `(* ,k ,cc))
	   (push-proof-log 'compute (list* 2 1 1 index))
	   (push-proof-log 'compute (list* 1 1 index))
	   (push-proof-log 'if-true (cons 1 index))
	   ;; (+ (* k cc) (* k r))
	   (log-use-axiom-as-rewrite
	    `(+ (* ,k ,cc) (* ,k ,r)) '*.collect.+.right
	    `((= |)X| ,k) (= |)Y| ,cc) (= |)Z| ,r)) index)
	   ;; (* k (+ cc r))
	   ))))

(defun log-factor-out-aux (k expr index)
  (cond
   ((+-p expr)
    ;; (+ (* c t) rest)
    (let ((left (log-factor-out-product k (second expr) (cons 1 index)))
          (right (log-factor-out-aux k (third expr) (cons 2 index))))
      ;; (+ (* k (* cc t)) (* k r))
      (log-use-axiom-as-rewrite
       `(+ ,left ,right) '*.collect.+.right
       `((= |)X| ,k) (= |)Y| ,(third left)) (= |)Z| ,(third right)))
       index)
      ;; (* k (+ (* cc t) r))
      `(* ,k (+ ,(third left) ,(third right)))))
   (t
    ;; (* c t)
    (log-factor-out-product k expr index))))

(defun log-factor-out-product (k expr index)
  (let ((cc (quotient (second expr) k)))
    (push-proof-log 'if-equal (cons 1 index) `(= ,(second expr) (* ,k ,cc)) t)
    (push-proof-log 'look-up (list* 2 1 index) `(* ,k ,cc))
    ;; (* (if (= c (* k cc)) (* k cc) c) t)
    (push-proof-log 'compute (list* 2 1 1 index))
    (push-proof-log 'compute (list* 1 1 index))
    (push-proof-log 'if-true (cons 1 index))
    ;; (* (* k cc) t)
    (log-use-axiom-as-rewrite
     `(* (* ,k ,cc) ,(third expr)) '*.associate.right
     `((= |)X| ,k) (= |)Y| ,cc) (= |)Z| ,(third expr)))
     index)
    ;; (* k (* cc t))
    `(* ,k (* ,cc ,(third expr)))))



;;; Log transformation of (= left right) to (= sum 0),
;;; where left and right each is an arithmetic expression
;;; (i.e., application of +, *, -, negate, ord, or an
;;; integer literal).

(defun log-sum-conversion-of-= (node index)
  (let ((expr (e-node-attribute node)))
    ;; Start with (= left right)
    (log-convert-=-to-=-zero (second expr) (third expr) index)
    ;; (= (- left right) 0)
    (let ((sum (log-collect-terms (make-- (=-left expr) (=-right expr))
                                  (cons 1 index))))
      ;; (= sum 0)
      ;; Now, normalize if necessary.
      (let ((k (apply #'gcd (mapcar #'cdr (cdr sum)))))
        (when (> k 1)
          (let ((expr (log-factor-out k sum (cons 1 index))))
            ;; (= (* k (+ c rest)) 0)
            (log-use-axiom-as-rewrite
             `(= ,expr 0) 'normalize.=
	     `((= |)X| ,(second expr)) (= |)Y| ,(third expr))) index)
            ;; (if (>= k 1)
            ;;     (if (= (type-of (+ c rest)) (int))
            ;;         (= (+ c rest) 0)
            ;;         (= (* k (+ c rest)) 0))
            ;;     (= (* k (+ c rest)) 0))
            (push-proof-log 'compute (if-test-index))
            (push-proof-log 'if-true index)
            ;; (if (= (type-of (+ c rest)) (int))
            ;;     (= (+ c rest) 0)
            ;;     (= (* k (+ c rest)) 0))
            (log-use-axiom-as-rewrite
             `(type-of ,(third expr)) '+.type-of-axiom
             `((= |)X| ,(second (third expr))) (= |)Y| ,(third (third expr))))
             (cons 1 (if-test-index)))
            (push-proof-log 'compute (if-test-index))
            (push-proof-log 'if-true index)
            ;; (= (+ c rest) 0)
            ))))))



;;; Converts (>= sum1 0) to (true) by way of contradiction when
;;; (>= sum2 0) is asserted, where sum2 is the opposite of sum1.

(defun log-contradict-sum-restriction (sum1 sum2 index)
  ;; Start with (>= sum1 0)
  (push-proof-log 'if-equal index `(>= ,(raw-expr-of-sum sum2) 0) t)
  ;; (if (>= sum2 0) (>= sum1 0) (>= sum1 0))
  (is-inconsistent *true* (if-left-index))
  ;; (if (>= sum2 0) (true) (>= sum1 0))
  (log-use-axiom (if-right-index) 'integer.is.nat.or.negative)
  ;; (if (>= sum2 0)
  ;;     (true)
  ;;     (if (all (x) (if (= (type-of x) (int))
  ;;                      (if (>= x 0) (true) (>= (+ -1 (negate x)) 0))
  ;;                      (true)))
  ;;         (>= sum1 0)
  ;;         (true)))
  (push-proof-log
   'instantiate-universal (cons 1 (if-right-index))
   `(= ,(car (axiom-args (get-event 'integer.is.nat.or.negative)))
       ,(raw-expr-of-sum sum1)))
  ;; (if (>= sum2 0)
  ;;     (true)
  ;;     (if (if (if (= (type-of sum1) (int))
  ;;                 (if (>= sum1 0) (true) (>= (+ -1 (negate sum1)) 0))
  ;;                 (true))
  ;;             (all (x) (if (= (type-of x) (int))
  ;;                          (if (>= x 0) (true) (>= (+ -1 (negate x)) 0))
  ;;                          (true)))
  ;;             (false))
  ;;         (>= sum1 0)
  ;;         (true)))
  (push-proof-log 'use-axiom (list* 2 1 (if-right-index))
                  'integer.is.nat.or.negative t)
  (log-type-of-expr (raw-expr-of-sum sum1) (list* 1 1 1 1 (if-right-index)))
  (push-proof-log 'compute (list* 1 1 1 (if-right-index)))
  (push-proof-log 'if-true (list* 1 1 (if-right-index)))
  ;; (if (>= sum2 0)
  ;;     (true)
  ;;     (if (if (if (>= sum1 0) (true) (>= (+ -1 (negate sum1)) 0))
  ;;             (true)
  ;;             (false))
  ;;         (>= sum1 0)
  ;;         (true)))
  (push-proof-log 'case-analysis (cons 1 (if-right-index)) 1)
  (push-proof-log 'if-true (list* 2 1 (if-right-index)))
  ;; (if (>= sum2 0)
  ;;     (true)
  ;;     (if (if (>= sum1 0) (true) (if (>= + -1 (negate sum1)) (true) (false))
  ;;         (>= sum1 0)
  ;;         (true)))
  (push-proof-log 'case-analysis (if-right-index) 1)
  ;; (if (>= sum2 0)
  ;;     (true)
  ;;     (if (>= sum1 0)
  ;;         (if (true) (>= sum1 0) (true))
  ;;         (if (>= (+ -1 (negate sum1)) 0) (>= sum1 0) (true))))
  (push-proof-log 'if-true (cons 2 (if-right-index)))
  (push-proof-log 'look-up (cons 2 (if-right-index)) *true*)
  ;; (if (>= sum2 0)
  ;;     (true)
  ;;     (if (>= sum1 0)
  ;;         (true)
  ;;         (if (>= (+ -1 (negate sum1)) 0) (>= sum1 0) (true))))
  (let ((expr1 (raw-expr-of-sum sum1))
        (expr2 (raw-expr-of-sum sum2)))
    (log-push-negate-into-sum expr1 (list* 2 1 1 3 (if-right-index)))
    (log-use-axiom-as-rewrite
     `(+ -1 (+ ,(- (car sum1)) ,(third expr2))) '+.associate.left
     `((= |)X| -1) (= |)Y| ,(- (car sum1))) (= |)Z| ,(third expr2)))
     (list* 1 1 3 (if-right-index)))
    (push-proof-log 'compute (list* 1 1 1 3 (if-right-index)))
    ;; (if (>= sum2 0)
    ;;     (true)
    ;;     (if (>= sum1 0) (true) (if (>= sum2 0) (>= sum1 0) (true))))
    (push-proof-log 'if-false (list* 2 3 (if-right-index)) *true* t)
    (push-proof-log 'if-true (list* 3 3 (if-right-index)) `(>= ,expr1 0) t)
    (push-proof-log 'case-analysis (cons 3 (if-right-index)) 1 t)
    ;; (if (>= sum2 0)
    ;;     (true)
    ;;     (if (>= sum1 0)
    ;;         (true)
    ;;         (if (if (>= sum2 0) (false) (true))
    ;;             (true)
    ;;             (>= sum1 0))))
    (push-proof-log 'look-up (list* 1 3 (if-right-index)) *true*)
    (push-proof-log 'if-true (cons 3 (if-right-index)))
    ;; (if (>= sum2 0)
    ;;     (true)
    ;;     (if (>= sum1 0)
    ;;         (true)
    ;;         (true)))
    (push-proof-log 'if-equal (if-right-index))
    (push-proof-log 'if-equal index)
    ;; (true)
    ))



;;; Pushes negate in (negate sum) into the sum, causing the coefficients
;;; to be negated.

(defun log-push-negate-into-sum (sum index)
  (cond ((integerp sum) (push-proof-log 'compute index))
	(t
	 ;; Start with (negate (+ c rest))
	 (log-use-axiom-as-rewrite
	  `(negate ,sum) 'negate.distribute.+
	  `((= |)X| ,(second sum)) (= |)Y| ,(third sum))) index)
	 ;; (+ (negate c) (negate rest))
	 (push-proof-log 'compute (cons 1 index))
	 ;; (+ -c (negate rest))
	 (log-push-negate-into-sum-aux (third sum) (cons 2 index)))))

(defun log-push-negate-into-sum-aux (rest index)
  ;; Start with (negate rest)
  (cond ((+-p rest)
         ;; (negate (+ (* c t) rr))
         (log-use-axiom-as-rewrite
	  `(negate ,rest) 'negate.distribute.+
	  `((= |)X| ,(second rest)) (= |)Y| ,(third rest))) index)
         ;; (+ (negate (* c t)) (negate rr))
         (log-use-axiom-as-rewrite
          `(negate ,(second rest)) 'negate.*.left
          `((= |)X| ,(second (second rest))) (= |)Y| ,(third (second rest))))
	  (cons 1 index))
         ;; (+ (* (negate c) t) (negate rr))
         (push-proof-log 'compute (list* 1 1 index))
         (log-push-negate-into-sum-aux (third rest) (cons 2 index)))
        (t
         ;; (negate (* c t))
         (log-use-axiom-as-rewrite
          `(negate ,rest) 'negate.*.left
	  `((= |)X| ,(second rest)) (= |)Y| ,(third rest))) index)
         ;; (* (negate c) t)
         (push-proof-log 'compute (cons 1 index)))))

;;; Given that (>= expr 0) and (>= (negate expr) 0) are in the
;;; context, transform (= expr 0) to (true).

(defun log-conclude-=-zero (expr index)
  ;; Start with (= expr 0)
  (log-use-axiom-as-rewrite
   `(= ,expr 0) '>=.and.>=.negate.zero `((= |)X| ,expr)) index)
  ;; (if (>= expr 0) (if (>= (negate expr) 0) (true) (= expr 0)) (= expr 0))
  (push-proof-log 'look-up (cons 1 (if-left-index)) *true*)
  (push-proof-log 'if-true (if-left-index))
  ;; (if (>= expr 0) (true) (= expr 0))
  (push-proof-log 'look-up (if-test-index) *true*)
  (push-proof-log 'if-true index)
  ;; (true)
  )

;;; Log transformation of (= left right) to (= (- left right) 0),
;;; where the type of left and right is (int).

(defun log-convert-=-to-=-zero (left right index)
  (log-use-axiom-as-rewrite
   `(= ,left ,right) '=.to.=.zero `((= |)X| ,left) (= |)Y| ,right)) index)
  ;; (if (= (type-of left) (int))
  ;;     (if (= (type-of right) (int)) (= (- left right) 0) (= left right))
  ;;     (= left right))
  (log-type-of-expr left (cons 1 (if-test-index)))
  (push-proof-log 'compute (if-test-index))
  (push-proof-log 'if-true index)
  (log-type-of-expr right (cons 1 (if-test-index)))
  (push-proof-log 'compute (if-test-index))
  (push-proof-log 'if-true index))

;;; Log transformation of (>= left right) to (= (- left right) 0),
;;; where the type of left and right is (int).

(defun log-convert->=-to->=-zero (left right index)
  (log-use-axiom-as-rewrite
   `(>= ,left ,right) '>=.to.>=.zero `((= |)X| ,left) (= |)Y| ,right)) index)
  ;; (if (= (type-of left) (int))
  ;;     (if (= (type-of right) (int)) (>= (- left right) 0) (>= left right))
  ;;     (>= left right))
  (log-type-of-expr left (cons 1 (if-test-index)))
  (push-proof-log 'compute (if-test-index))
  (push-proof-log 'if-true index)
  (log-type-of-expr right (cons 1 (if-test-index)))
  (push-proof-log 'compute (if-test-index))
  (push-proof-log 'if-true index))



;;; expr must be an application of +, -, *, negate, or ord.

(defun log-collect-terms (expr index)
  ;; expr
  (log-add-zero expr index)
  ;; (+ 0 expr)
  (log-collect-terms-recursively expr t (list 0) index))

(defun log-collect-terms-reverse (expr sum index)
  (push-proof-log 'if-equal index `(= ,sum ,expr) t)
  (push-proof-log 'look-up (if-left-index) expr)
  ;; (if (= sum expr) expr sum)
  (log-collect-terms expr (cons 2 (if-test-index)))
  (push-proof-log 'compute (if-test-index))
  (push-proof-log 'if-true index))

;;; (op collected expr)
;;; expr must be an integer literal, an ord, or an arithmetic expression.

(defun log-collect-terms-recursively (expr positive collected-terms index)
  (let* ((raw-sum (raw-expr-of-sum collected-terms))
         (e (log-wrap-ord-arguments expr (cons 2 index)))
         (term (list (if positive '+ '-) raw-sum e)))
    (cond
     ((integerp e)
      (cond ((null (cdr collected-terms))
             (push-proof-log 'compute index))
            (t (if positive
                   (log-use-axiom-as-rewrite
                    `(+ ,raw-sum ,e) '+.left.permute
                    `((= |)X| ,(second raw-sum)) (= |)Y| ,(third raw-sum))
		      (= |)Z| ,e))
		    index)
                 (log-use-axiom-as-rewrite
                  `(- ,raw-sum ,e) '-.+.left.to.+.-.left
                  `((= |)X| ,(second raw-sum)) (= |)Y| ,(third raw-sum))
		    (= |)Z| ,e))
		  index))
               (push-proof-log 'compute (cons 1 index))))
      (cons (+ (car collected-terms) (if positive e (- e)))
            (cdr collected-terms)))
     ((+-p e)
      ;; (op sum (+ left right))
      (let ((axiom (if positive '+.associate.left '-.+.to.left)))
        (log-use-axiom-as-rewrite
	 term axiom
	 `((= |)X| ,raw-sum) (= |)Y| ,(second e)) (= |)Z| ,(third e)))
	 index)
        ;; (op (op sum left) right)
        (log-collect-terms-recursively
         (+-right e) positive
         (log-collect-terms-recursively
          (+-left e) positive collected-terms (cons 1 index)) index)))
     ((--p e)
      (let ((axiom (if positive '+.-.to.left '-.-.to.left)))
        (log-use-axiom-as-rewrite
	 term axiom
	 `((= |)X| ,raw-sum) (= |)Y| ,(second e)) (= |)Z| ,(third e)))
	 index)
        (log-collect-terms-recursively
         (--right e) (not positive)
         (log-collect-terms-recursively
          (--left e) positive collected-terms (cons 1 index)) index)))
     ((*-p e)
      (log-collect-terms-for-multiplication e positive collected-terms index))
     ((negate-p e)
      (let ((axiom (if positive '+.negate '-.negate)))
        (log-use-axiom-as-rewrite
	 term axiom
	 `((= |)X| ,raw-sum) (= |)Y| ,(second e)))
	 index)
        (log-collect-terms-recursively
         (second e) (not positive) collected-terms index)))
     ((and (ord-p e)
           (or (arithmetic-expression-p (ord-expr e))
               (integerp (ord-expr e))
               (ord-p (ord-expr e))))
      (log-remove-ord e (cons 2 index))
      (log-collect-terms-recursively
       (ord-expr e) positive collected-terms index))
     (t 
      (let ((axiom (if positive '+.times.1.right '-.times.minus.1.right)))
        ;; (+ sum expr) or (- sum expr)
        (log-use-axiom-as-rewrite
         `(,(if positive '+ '-) ,raw-sum ,e) axiom
	 `((= |)X| ,raw-sum) (= |)Y| ,e)) index)
        ;; (+ sum (* 1 expr)) or (+ sum (* -1 expr))
        (log-insert-term
         (list e) (if positive 1 -1) collected-terms index))))))



;;; Log the wrapping of arguments with ords.  Integer literals, ords,
;;; and arithmetic operations are not wrapped.

(defun log-wrap-ord-arguments (expr index)
  (cond ((and (or (*-p expr) (+-p expr) (--p expr))
              (or (and (not (integerp (second expr)))
                       (not (ord-p (second expr)))
                       (not (arithmetic-expression-p (second expr))))
                  (and (not (integerp (third expr)))
                       (not (ord-p (third expr)))
                       (not (arithmetic-expression-p (third expr))))))
         (let ((axiom (intern (string-append (car expr) ".ORD")
			      *zk-package*)))
           (push-proof-log
            'if-equal index
            `(= ,expr
                (,(first expr) (ord ,(second expr)) (ord ,(third expr))))
	    t)
           (push-proof-log 'look-up (if-left-index)
                           `(,(first expr) (ord ,(second expr))
                             (ord ,(third expr))))
           ;; (if (= (op left right) (op (ord left) (ord right)))
           ;;     (op (ord left) (ord right))
           ;;     (op left right))
           (log-use-axiom-as-rewrite
            `(,(first expr) (ord ,(second expr)) (ord ,(third expr)))
            axiom `((= |)X| ,(second expr)) (= |)Y| ,(third expr)))
            (cons 2 (if-test-index)))
           (push-proof-log 'compute (if-test-index))
           (push-proof-log 'if-true index)
           ;; (op (ord left) (ord right))
           (when (or (integerp (second expr)) (ord-p (second expr))
                     (arithmetic-expression-p (second expr)))
                 (log-remove-ord
                  (list 'ord (second expr)) (cons 1 index)))
           (when (or (integerp (third expr)) (ord-p (third expr))
                     (arithmetic-expression-p (third expr)))
                 (log-remove-ord
                  (list 'ord (third expr)) (cons 2 index)))
           (list (first expr) (wrap-ord (second expr))
                 (wrap-ord (third expr)))))
        ((and (negate-p expr) (not (integerp (second expr)))
              (not (ord-p (second expr)))
              (not (arithmetic-expression-p (second expr))))
         (let ((axiom 'negate.ord))
           (push-proof-log
            'if-equal index `(= ,expr (negate (ord ,(second expr)))) t)
           (push-proof-log 'look-up (if-left-index)
                           `(negate (ord ,(second expr))))
           ;; (if (= (negate e) (negate (ord e)))
           ;;     (negate (ord e))
           ;;     (negate e))
           (log-use-axiom-as-rewrite
            `(negate (ord ,(second expr))) axiom `((= |)X| ,(second expr)))
            (cons 2 (if-test-index)))
           (push-proof-log 'compute (if-test-index))
           (push-proof-log 'if-true index)
           ;; (negate (ord e))
           `(negate (ord ,(ord-expr expr)))))
        (t expr)))



;;; Log transformation of (ord expr) to expr.

(defun log-remove-ord (expr index)
  (let ((arg (ord-expr expr)))
    (cond
     ((integerp arg)
      (push-proof-log 'compute index))
     (t (log-use-axiom-as-rewrite
         expr (intern (string-append "ORD." (car arg))
		      *zk-package*)
	 (let ((args (cdr arg)))
	   (cond ((= (length args) 1) `((= |)X| ,(car args))))
		 ((= (length args) 2)
		  `((= |)X| ,(car args)) (= |)Y| ,(second args))))))
	 index)))))
  


;;; expr is a * expression with each argument being an integer literal, ord,
;;; or arithmetic expression.

(defun log-collect-terms-for-multiplication
  (expr positive collected-terms index)
  (let ((left (*-left expr))
        (right (*-right expr)))
    (cond ((and (integerp left) (integerp right))
           (push-proof-log 'compute (cons 2 index))
           (log-collect-terms-recursively
            (* left right) positive collected-terms index))
          ((integerp left)
           (cond (positive
                  (log-add-collected-terms
                   collected-terms
                   (log-multiply-collected-terms-by-constant
                    (log-collect-terms right (list* 2 2 index))
                    left (cons 2 index))
                   index))
                 (t ;; (- sum (* c right))
                  (let ((sum (raw-expr-of-sum collected-terms)))
                    (log-use-axiom-as-rewrite
                     `(- ,sum ,expr) '-.times.minus.1.right
		     `((= |)X| ,sum) (= |)Y| ,expr))
                     index)
                    (log-use-axiom-as-rewrite
                     `(* -1 ,expr) '*.associate.left
		     `((= |)X| -1) (= |)Y| ,left) (= |)Z| ,right))
                     (cons 2 index))
                    (push-proof-log 'compute (list* 1 2 index))
                    ;; (+ sum (* -c right))
                    (log-add-collected-terms
                     collected-terms
                     (log-multiply-collected-terms-by-constant
                      (log-collect-terms right (list* 2 2 index))
                      (- left) (cons 2 index))
                     index)))))
          ((integerp right)
           (log-use-axiom-as-rewrite
            expr '*.commutes `((= |)X| ,left) (= |)Y| ,right)) (cons 2 index))
           (cond (positive
                  (log-add-collected-terms
                   collected-terms
                   (log-multiply-collected-terms-by-constant
                    (log-collect-terms left (list* 2 2 index))
                    right (cons 2 index))
                   index))
                 (t
                  (let ((sum (raw-expr-of-sum collected-terms)))
                    (log-use-axiom-as-rewrite
                     `(- ,sum (* ,right ,left)) '-.times.minus.1.right
                     `((= |)X| ,sum) (= |)Y| (* ,right ,left))) index)
                    (log-use-axiom-as-rewrite
                     `(* -1 (* ,right ,left)) '*.associate.left
                     `((= |)X| -1) (= |)Y| ,right) (= |)Z| ,left))
		     (cons 2 index))
                    (push-proof-log 'compute (list* 1 2 index))
                    ;; (+ sum (* -c left))
                    (log-add-collected-terms
                     collected-terms
                     (log-multiply-collected-terms-by-constant
                      (log-collect-terms left (list* 2 2 index))
                      (- right) (cons 2 index))
                     index)))))
          (t (log-multiply-and-collect-terms
              (log-collect-terms left (list* 1 2 index))
              (log-collect-terms right (list* 2 2 index))
              positive
              collected-terms
              index)))))



;;; (* constant sum)

(defun log-multiply-collected-terms-by-constant
  (collected-terms constant index)
  (let ((raw-sum (raw-expr-of-sum collected-terms)))
    (cond ((zerop constant)
           (log-use-axiom-as-rewrite
            (make-* 0 raw-sum) '*.zero.left `((= |)X| ,raw-sum)) index)
           (list 0))
          ((null (cdr collected-terms))
           (push-proof-log 'compute index)
           (list (* constant (car collected-terms))))
          (t (log-use-axiom-as-rewrite
              (make-* constant raw-sum) '*.distribute.+.right
	      `((= |)X| ,constant) (= |)Y| ,(second raw-sum))
		(= |)Z| ,(third raw-sum)))
	      index)
             (push-proof-log 'compute (cons 1 index))
             (cons (* (car collected-terms) constant)
                   (log-multiply-collected-terms-by-constant-aux
                    (cdr collected-terms) (third raw-sum) constant
                    (cons 2 index)))))))

;;; (* constant rest-sum)
;;; collected-terms (rest) is non-nil

(defun log-multiply-collected-terms-by-constant-aux
  (collected-terms rest-sum constant index)
  (cond ((null (cdr collected-terms))
         (log-use-axiom-as-rewrite
          (make-* constant rest-sum) '*.associate.left
	  `((= |)X| ,constant) (= |)Y| ,(second rest-sum))
	    (= |)Z| ,(third rest-sum)))
	  index)
         ;; (* (* constant coeff) bag)
         (push-proof-log 'compute (cons 1 index))
         (list (cons (caar collected-terms)
                     (* constant (cdar collected-terms)))))
        (t (log-use-axiom-as-rewrite
            (make-* constant rest-sum) '*.distribute.+.right
	    `((= |)X| ,constant) (= |)Y| ,(second rest-sum))
	      (= |)Z| ,(third rest-sum)))
	    index)
           (log-use-axiom-as-rewrite
            (make-* constant (second rest-sum)) '*.associate.left
	    `((= |)X| ,constant) (= |)Y| ,(second (second rest-sum)))
	      (= |)Z| ,(third (second rest-sum))))
	    (cons 1 index))
           (push-proof-log 'compute (list* 1 1 index))
           (cons (cons (caar collected-terms)
                       (* constant (cdar collected-terms)))
                 (log-multiply-collected-terms-by-constant-aux
                  (cdr collected-terms) (third rest-sum) constant
                  (cons 2 index))))))
           


;;; (+ collected-terms (* collected-1 collected-2))
;;; or
;;; (- collected-terms (* collected-1 collected-2))

(defun log-multiply-and-collect-terms
  (collected-1 collected-2 positive collected-terms index)
  (cond ((null (cdr collected-1))
	 (cond ((zerop (car collected-1))
		(log-use-axiom-as-rewrite
		 `(* 0 ,(raw-expr-of-sum collected-2)) '*.zero.left
		 `((= |)X| ,(raw-expr-of-sum collected-2))) (cons 2 index))
		(cond (positive
		       (log-add-collected-terms
			collected-terms `(0) index))
		      (t
		       (log-use-axiom-as-rewrite
			`(- ,(raw-expr-of-sum collected-terms) 0)
			'-.times.minus.1.right
			`((= |)X| ,(raw-expr-of-sum collected-terms))
			  (= |)Y| 0))
			index)
		       (push-proof-log 'compute (cons 2 index))
		       (log-add-collected-terms
			collected-terms `(0) index))))
	       (t
		(log-multiply-and-collect-terms-case-1
		 collected-terms (car collected-1) collected-2 positive
		 index))))
        ((null (cdr collected-2))
	 (cond ((zerop (car collected-2))
		(log-use-axiom-as-rewrite
		 `(* ,(raw-expr-of-sum collected-1) 0) '*.zero.right
		 `((= |)X| ,(raw-expr-of-sum collected-1))) (cons 2 index))
		(cond (positive
		       (log-add-collected-terms
			collected-terms `(0) index))
		      (t
		       (log-use-axiom-as-rewrite
			`(- ,(raw-expr-of-sum collected-terms) 0)
			'-.times.minus.1.right
			`((= |)X| ,(raw-expr-of-sum collected-terms))
			  (= |)Y| 0))
			index)
		       (push-proof-log 'compute (cons 2 index))
		       (log-add-collected-terms
			collected-terms `(0) index))))
	       (t
		(log-use-axiom-as-rewrite
		 `(* ,(raw-expr-of-sum collected-1) ,(car collected-2))
		 '*.commutes
		 `((= |)X| ,(raw-expr-of-sum collected-1))
		   (= |)Y| ,(car collected-2)))
		 (cons 2 index))
		(log-multiply-and-collect-terms-case-1
		 collected-terms (car collected-2) collected-1 positive
		 index))))
        (t (log-multiply-and-collect-terms-case-2
            collected-1 collected-2 positive collected-terms index))))


;;; (+ collected-1 (* constant collected-2))
;;; or
;;; (- collected-1 (* constant collected-2))

(defun log-multiply-and-collect-terms-case-1
  (collected-1 constant collected-2 positive index)
  (let ((expr `(,(if positive '+ '-)
                ,(raw-expr-of-sum collected-1)
                (* ,constant ,(raw-expr-of-sum collected-2)))))
    (unless positive
      (log-use-axiom-as-rewrite
       expr '-.times.minus.1.right
       `((= |)X| ,(second expr)) (= |)Y| ,(third expr))) index)
      ;; (+ collected-1 (* -1 (* constant collected-2)))
      (log-use-axiom-as-rewrite
       `(* -1 (* ,constant ,(raw-expr-of-sum collected-2)))
       '*.associate.left
       `((= |)X| -1) (= |)Y| ,constant) (= |)Z| ,(raw-expr-of-sum collected-2)))
       (cons 2 index))
      (push-proof-log 'compute (list* 1 2) index))
    (log-add-collected-terms
     collected-1
     (log-multiply-collected-terms-by-constant
      collected-2 (if positive constant (- constant)) (cons 2 index))
     index)))



;;; (op collected (* collected-1 collected-2))
;;; case where collected-1 and collected-2 are both non-trivial

(defun log-multiply-and-collect-terms-case-2
  (collected-1 collected-2 positive collected-terms index)
  (let ((sum (raw-expr-of-sum collected-terms))
        (sum-1 (raw-expr-of-sum collected-1))
        (sum-2 (raw-expr-of-sum collected-2)))
    ;; (op sum (* (+ c1 r1) (+ c2 r2)))
    (log-use-axiom-as-rewrite
     `(* ,sum-1 ,sum-2) '*.distribute.+
     `((= |)A| ,(second sum-1)) (= |)B| ,(third sum-1))
       (= |)X| ,(second sum-2)) (= |)Y| ,(third sum-2)))
     (cons 2 index))
    ;; (op sum (+ (* c1 c2) (+ (* c1 r2) (+ (* r1 c2) (* r1 r2)))))
    (let* ((op (if positive '+ '-))
           (axiom (if positive '+.associate.left '-.+.right.to.-.-.left))
           (expr `(,op ,sum
                       (+ (* ,(second sum-1) ,(second sum-2))
                          (+ (* ,(second sum-1) ,(third sum-2))
                             (+ (* ,(third sum-1) ,(second sum-2))
                                (* ,(third sum-1) ,(third sum-2)))))))
           (c (* (car collected-1) (car collected-2))))
      (log-use-axiom-as-rewrite
       expr axiom
       `((= |)X| ,(second expr)) (= |)Y| ,(second (third expr)))
	 (= |)Z| ,(third (third expr))))
       index)
      ;; (op (op sum (* c1 c2)) (+ (* c1 r2) (+ (* r1 c2) (* r1 r2))))
      (push-proof-log 'compute (list* 2 1 index))
      ;; (op (op sum c) (+ (* c1 r2) (+ (* r1 c2) (* r1 r2))))
      (cond ((null (cdr collected-terms))
             (push-proof-log 'compute (cons 1 index)))
            (t (log-use-axiom-as-rewrite
                `(,op ,sum ,(* (second sum-1) (second sum-2)))
                (if positive '+.left.permute '-.+.left.to.+.-.left)
                `((= |)X| ,(second sum)) (= |)Y| ,(third sum))
                  (= |)Z| ,(* (second sum-1) (second sum-2))))
                (cons 1 index))
               (push-proof-log 'compute (list* 1 1 index))))
      (let ((collected-3
             (cons (if positive
                       (+ (car collected-terms) c)
                     (- (car collected-terms) c))
                   (cdr collected-terms))))
        ;; (op collected-3 (+ (* c1 r2) (+ (* r1 c2) (* r1 r2))))
        (setq collected-3
              (log-multiply-and-collect-terms-case-2-aux
               collected-3 (second sum-1) (cdr collected-2) op
               `(+ (* ,(third sum-1) ,(second sum-2))
                   (* ,(third sum-1) ,(third sum-2)))
               axiom index))
        ;; (op collected-3 (+ (* r1 c2) (* r1 r2)))
        (log-use-axiom-as-rewrite
         `(* ,(third sum-1) ,(second sum-2)) '*.commutes
         `((= |)X| ,(third sum-1)) (= |)Y| ,(second sum-2))) (list* 1 2 index))
        (setq collected-3
              (log-multiply-and-collect-terms-case-2-aux
               collected-3 (second sum-2) (cdr collected-1) op
               `(* ,(third sum-1) ,(third sum-2))
               axiom index))
        ;; (op collected-3 (* r1 r2))
        (log-multiply-and-insert
         collected-3 (cdr collected-1) (cdr collected-2) positive index)))))



;;; (op collected (+ (* constant rest) expr))
;;; note that the result is for the collected position (cons 1 index)

(defun log-multiply-and-collect-terms-case-2-aux
  (collected constant rest op expr axiom index)
  (let ((sum (raw-expr-of-sum collected))
        (sum-r (raw-expr-of-sum-aux rest)))
    (cond ((zerop constant)
	   (log-use-axiom-as-rewrite
	    `(* 0 ,sum-r) '*.zero.left `((= |)X| ,sum-r)) (list* 1 2 index))
	   (log-use-axiom-as-rewrite
	    `(+ 0 ,expr) '+.zero.left `((= |)X| ,expr)) (cons 2 index))
	   (log-type-of-expr expr (list* 1 1 2 index))
	   (push-proof-log 'compute (list* 1 2 index))
	   (push-proof-log 'if-true (cons 2 index))
	   collected)
	  (t
	   ;; (op collected (+ (* constant rest) expr))
	   (log-use-axiom-as-rewrite
	    `(,op ,sum (+ (* ,constant ,sum-r) ,expr)) axiom
	    `((= |)X| ,sum) (= |)Y| (* ,constant ,sum-r)) (= |)Z| ,expr)) index)
	   ;; (op (op collected (* constant rest)) expr)
	   (unless (eq op '+)
	     (log-use-axiom-as-rewrite
	      `(op ,sum (* ,constant ,sum-r)) '-.times.minus.1.right
	      `((= |)X| ,sum) (= |)Y| (* ,constant ,sum-r))) (cons 1 index))
	     ;; (- (+ collected (* -1 (* constant rest))) expr)
	     (log-use-axiom-as-rewrite
	      `(* -1 (* ,constant ,sum-r)) '*.associate.left
	      `((= |)X| -1) (= |)Y| ,constant) (= |)Z| ,sum-r))
	      (list* 2 1 index))
	     (push-proof-log 'compute (list* 1 2 1 index))
	     ;; (- (+ collected (* -constant rest)) expr)
	     )
	   (let ((c (if (eq op '+) constant (- constant))))
	     ;; (op (+ collected (* c rest)) expr)
	     (cond ((null (cdr collected))
		    (cons (car collected)
			  (log-multiply-collected-terms-by-constant-aux
			   rest sum-r c (list* 2 1 index))))
		   (t (log-use-axiom-as-rewrite
		       `(+ ,sum (* ,c ,sum-r)) '+.associate.right
		       `((= |)X| ,(second sum)) (= |)Y| ,(third sum))
			 (= |)Z| (* ,c ,sum-r)))
		       (cons 1 index))
		      ;; (op (+ cs (+ rs (* c rest))) expr)
		      (let ((r (log-add-collected-terms-recursively
				(cdr collected)
				(log-multiply-collected-terms-by-constant-aux
				 rest sum-r c (list* 2 2 1 index))
				(list* 2 1 index))))
			(when (null r)
			  (push-proof-log 'compute (cons 1 index)))
			(cons (car collected) r)))))))))



;;; (op collected (* rest-1 rest-2))
;;; rest-1 and rest-2 are non-trivial

(defun log-multiply-and-insert (collected rest-1 rest-2 positive index)
  (let ((sum-2 (raw-expr-of-sum-aux rest-2))
        (axiom (if positive '+.associate.left '-.+.right.to.-.-.left))
        (op (if positive '+ '-)))
    (loop for r = rest-1 then (cdr r)
          while r
          do (let ((sum (raw-expr-of-sum collected))
                   (sum-1 (raw-expr-of-sum-aux r)))
               (cond ((null (cdr r))
                      ;; (op sum (* term rest-2))
                      (setq collected
                            (log-multiply-and-insert-aux
                             collected (car r) rest-2 positive index)))
                     (t (log-use-axiom-as-rewrite
                         `(* ,sum-1 ,sum-2) '*.distribute.+.left
                         `((= |)X| ,(second sum-1)) (= |)Y| ,(third sum-1))
			   (= |)Z| ,sum-2))
                         (cons 2 index))
                        ;; (op sum (+ (* term rest-2) (* rr rest-2)))
                        (log-use-axiom-as-rewrite
                         `(,op ,sum (+ (* ,(second sum-1) ,sum-2)
                                       (* ,(third sum-1),sum-2)))
                         axiom
                         `((= |)X| ,sum) (= |)Y| (* ,(second sum-1) ,sum-2))
			   (= |)Z| (* ,(third sum-1),sum-2)))
                         index)
                        ;; (op (op sum (* term rest-2)) (* rr rest-2))
                        (setq collected
                              (log-multiply-and-insert-aux
                               collected (car r) rest-2 positive
                               (cons 1 index)))))))
    collected))



;;; (op collected (* term rest))
;;; (car term) is a bag
;;; (cdr term) is a coefficient

(defun log-multiply-and-insert-aux (collected term rest positive index)
  (let ((axiom (if positive '+.associate.left '-.+.right.to.-.-.left))
        (op (if positive '+ '-))
        (expr (raw-expr-of-sum-aux (list term))))
    (loop for r = rest then (cdr r)
          while r
          do (let ((sum (raw-expr-of-sum collected))
                   (sum-r (raw-expr-of-sum-aux rest)))
               (cond ((null (cdr r))
                      ;; (op sum (* term1 term2))
                      (setq collected
                            (log-multiply-terms-and-insert
                             collected term (car r) positive index)))
                     (t (log-use-axiom-as-rewrite
                         `(* ,expr ,sum-r) '*.distribute.+.right
                         `((= |)X| ,expr) (= |)Y| ,(second sum-r))
			   (= |)Z| ,(third sum-r)))
                         (cons 2 index))
                        ;; (op sum (+ (* term term2) (* term rest2)))
                        (log-use-axiom-as-rewrite
                         `(,op ,sum (+ (* ,expr ,(second sum-r))
                                       (* ,expr ,(third sum-r))))
                         axiom
                         `((= |)X| ,sum) (= |)Y| (* ,expr ,(second sum-r)))
			   (= |)Z| (* ,expr ,(third sum-r))))
                         index)
                        ;; (op (op sum (* term term2)) (* term rest2))
                        (setq collected
                              (log-multiply-terms-and-insert
                               collected term (car r) positive
                               (cons 1 index)))))))
    collected))



;;; (op collected (* term-1 term-2))

(defun log-multiply-terms-and-insert (collected term-1 term-2 positive index)
  (let ((expr-1 (raw-expr-of-sum-aux (list term-1)))
        (expr-2 (raw-expr-of-sum-aux (list term-2)))
        (sum (raw-expr-of-sum collected)))
    (log-use-axiom-as-rewrite
     `(* ,expr-1 ,expr-2) '*.associate.left
     `((= |)X| ,expr-1) (= |)Y| ,(second expr-2)) (= |)Z| ,(third expr-2)))
     (cons 2 index))
    ;; (op sum (* (* term-1 coeff-2) factor-2))
    (log-use-axiom-as-rewrite
     `(* (* ,(second expr-1) ,(third expr-1)) ,(second expr-2))
     '*.left.permute
     `((= |)X| ,(second expr-1)) (= |)Y| ,(third expr-1))
       (= |)Z| ,(second expr-2)))
     (list* 1 2 index))
    ;; (op sum (* (* (* coeff-1 coeff-2) factor-1) factor-2))
    (push-proof-log 'compute (list* 1 1 2 index))
    (let ((c (* (second expr-1) (second expr-2))))
      ;; (op sum (* (* c factor-1) factor-2))
      (log-use-axiom-as-rewrite
       `(* (* ,c ,(third expr-1)) ,(third expr-2)) '*.associate.right
       `((= |)X| ,c) (= |)Y| ,(third expr-1)) (= |)Z| ,(third expr-2)))
       (cons 2 index))
      ;; (op sum (* c (* factor-1 factor-2)))
      (let* ((factor (log-coalesce-bags
                      (car term-1) (car term-2) (list* 2 2 index)))
             (expr (raw-expr-of-sum-aux (list (cons factor c)))))
        ;; (op sum (* c factor))
        (unless positive
          (log-use-axiom-as-rewrite
           `(- ,sum ,expr) '-.times.minus.1.right
	   `((= |)X| ,sum) (= |)Y| ,expr)) index)
          ;; (+ sum (* -1 (* c factor)))
          (log-use-axiom-as-rewrite
           `(* -1 ,expr) '*.associate.left
	   `((= |)X| -1) (= |)Y| ,(second expr)) (= |)Z| ,(third expr)))
           (cons 2 index))
          ;; (+ sum (* (* -1 c) factor))
          (push-proof-log 'compute (list* 1 2 index))
          (setq c (- c)))
        ;; (+ sum (* c factor))
        (log-insert-term factor c collected index)))))



;;; (+ sum (* coeff factor))

(defun log-insert-term (factor coeff collected index)
  (let ((expr (raw-expr-of-sum-aux (list (cons factor coeff))))
        (sum (raw-expr-of-sum collected)))
    (cond
     ((null (cdr collected))
      (cons (car collected) (list (cons factor coeff))))
     (t (log-use-axiom-as-rewrite
         `(+ ,sum ,expr) '+.commutes `((= |)X| ,sum) (= |)Y| ,expr)) index)
        ;; (+ (* coeff factor) (+ first-sum rest-sum))
        (log-use-axiom-as-rewrite
         `(+ ,expr ,sum) '+.right.permute
         `((= |)X| ,expr) (= |)Y| ,(second sum)) (= |)Z| ,(third sum))) index)
        ;; (+ first-sum (+ (* coeff factor) rest-sum))
        (let ((rest (log-insert-term-aux
                     factor coeff expr (cdr collected) (cons 2 index))))
          (when (null rest) (push-proof-log 'compute index))
          (cons (car collected) rest))))))

(defun log-common-factor (factor coeff expr coeff-2 index)
  ;; (+ (* c1 factor) (* c2 factor))
  (let ((expr-2 (raw-expr-of-sum-aux (list (cons factor coeff-2)))))
    (log-use-axiom-as-rewrite
     `(+ ,expr ,expr-2) '*.collect.+.left
     `((= |)X| ,(second expr)) (= |)Y| ,(third expr)) (= |)Z| ,(second expr-2)))
     index)
    ;; (* (+ c1 c2) factor)
    (push-proof-log 'compute (cons 1 index))
    (cond ((zerop (+ coeff coeff-2))
           (log-use-axiom-as-rewrite
            `(* 0 ,(third expr)) '*.zero.left `((= |)X| ,(third expr))) index)
           nil)
          (t (list (cons factor (+ coeff coeff-2)))))))



(defun log-insert-term-aux (factor coeff expr collected index)
  (let ((term (car collected))
        (right (raw-expr-of-sum-aux collected)))
    (cond
     ((null (cdr collected))
      (cond ((equal factor (car term))
             ;; (+ (* c1 factor) (* c2 factor))
             (log-common-factor factor coeff expr (cdr term) index)
             ;; ***** can this return nil?
             )
            ((smaller-bag-p factor (car term))
             (cons (cons factor coeff) collected))
            (t
             (log-use-axiom-as-rewrite
              `(+ ,expr ,right) '+.commutes `((= |)X| ,expr) (= |)Y| ,right))
	      index)
             `(,(car collected) (,factor . ,coeff)))))
     (t (cond
         ((equal factor (car term))
          ;; (+ (* c1 factor) (+ (* c2 factor) rest))
          (log-use-axiom-as-rewrite
           `(+ ,expr ,right) '+.associate.left
           `((= |)X| ,expr) (= |)Y| ,(second right)) (= |)Z| ,(third right)))
	   index)
          ;; (+ (+ (* c1 factor) (* c2 factor)) rest)
          (let ((common (log-common-factor factor coeff expr (cdr term)
                                           (cons 1 index))))
            (when (null common)
              ;; (+ 0 rest)
              (log-use-axiom-as-rewrite
               `(+ 0 ,(raw-expr-of-sum-aux (cdr collected))) '+.zero.left
               `((= |)X| ,(raw-expr-of-sum-aux (cdr collected)))) index)
              (log-type-of-expr (raw-expr-of-sum-aux (cdr collected))
                                (cons 1 (if-test-index)))
              (push-proof-log 'compute (if-test-index))
              (push-proof-log 'if-true index)
              )
            (append common (cdr collected))))
         ((smaller-bag-p factor (car term))
          (cons (cons factor coeff) collected))
         (t (log-use-axiom-as-rewrite
             `(+ ,expr ,right) '+.right.permute
             `((= |)X| ,expr) (= |)Y| ,(second right)) (= |)Z| ,(third right)))
	     index)
            ;; (+ first (+ (* c factor) rest))
            (let ((rest (log-insert-term-aux
                         factor coeff expr (cdr collected) (cons 2 index))))
              (when (null rest)
                ;; (+ (* c factor) 0)
                (log-use-axiom-as-rewrite
                 `(+ ,(second right) 0) '+.zero.right
		 `((= |)X| ,(second right)))
                 index)
                (log-type-of-expr (second right) (cons 1 (if-test-index)))
                (push-proof-log 'compute (if-test-index))
                (push-proof-log 'if-true index)
                ;; (* c factor)
                )
              (cons (car collected) rest))))))))



;;; (+ collected-1 collected-2)

(defun log-add-collected-terms (collected-1 collected-2 index)
  (let ((c1 (car collected-1))
        (c2 (car collected-2)))
    (cond ((null (cdr collected-1))
           (cond ((null (cdr collected-2))
                  ;; (+ c1 c2)
                  (push-proof-log 'compute index)
                  (list (+ c1 c2)))
                 (t
                  ;; (+ c1 (+ c2 r2))
                  (let ((sum (raw-expr-of-sum collected-2)))
                    (log-use-axiom-as-rewrite
                     `(+ ,c1 ,sum) '+.associate.left
		     `((= |)X| ,c1) (= |)Y| ,(second sum))
		       (= |)Z| ,(third sum)))
		     index)
                    ;; (+ (+ c1 c2) r2)
                    (push-proof-log 'compute (cons 1 index))
                    (cons (+ c1 c2) (cdr collected-2))))))
          ((null (cdr collected-2))
           ;; (+ (+ c1 r1) c2)
           (let ((sum (raw-expr-of-sum collected-1)))
             (log-use-axiom-as-rewrite
              `(+ ,sum ,c2) '+.left.permute
	      `((= |)X| ,c1) (= |)Y| ,(third sum)) (= |)Z| ,c2)) index)
             ;; (+ (+ c1 c2) r1)
             (push-proof-log 'compute (cons 1 index))
             (cons (+ c1 c2) (cdr collected-1))))
          (t
           ;; (+ (+ c1 r1) (+ c2 r2))
           (let ((sum-1 (raw-expr-of-sum collected-1))
                 (sum-2 (raw-expr-of-sum collected-2)))
             (log-use-axiom-as-rewrite
              `(+ ,sum-1 ,sum-2) '+.associate.left
	      `((= |)X| ,sum-1) (= |)Y| ,c2) (= |)Z| ,(third sum-2)))
              index)
             ;; (+ (+ (+ c1 r1) c2) r2)
             (log-use-axiom-as-rewrite
              `(+ ,sum-1 ,c2) '+.left.permute
	      `((= |)X| ,c1) (= |)Y| ,(third sum-1)) (= |)Z| ,c2))
              (cons 1 index))
             ;; (+ (+ (+ c1 c2) r1) r2)
             (push-proof-log 'compute (list* 1 1 index))
             ;; (+ (+ c r1) r2)
             (log-use-axiom-as-rewrite
              `(+ (+ ,(+ c1 c2) ,(third sum-1)) ,(third sum-2))
              '+.associate.right
	      `((= |)X| ,(+ c1 c2)) (= |)Y| ,(third sum-1))
		(= |)Z| ,(third sum-2)))
              index)
             ;; (+ c (+ r1 r2))
             (let ((r (log-add-collected-terms-recursively
                       (cdr collected-1) (cdr collected-2) (cons 2 index))))
               (when (null r)
                 (push-proof-log 'compute index))
               (cons (+ c1 c2) r)))))))



;;; (+ collected-1 collected-2)
;;; Both collected-1 and collected-2 are non-constant terms and are non-nil.

(defun log-add-collected-terms-recursively (collected-1 collected-2 index)
  (let ((sum-1 (raw-expr-of-sum-aux collected-1))
        (sum-2 (raw-expr-of-sum-aux collected-2)))
    (cond ((null (cdr collected-1))
           (cond ((null (cdr collected-2))
                  ;; (+ t1 t2)
                  (log-add-terms collected-1 collected-2 index))
                 (t (log-add-term-to-collected-terms
                     collected-1 collected-2 index))))
          ((null (cdr collected-2))
           ;; (+ (+ (* c1 f1) r1) (* c2 f2))
           (log-use-axiom-as-rewrite
            `(+ ,sum-1 ,sum-2) '+.commutes `((= |)X| ,sum-1) (= |)Y| ,sum-2))
	    index)
           (log-add-term-to-collected-terms collected-2 collected-1 index))
          ((equal (caar collected-1) (caar collected-2))
           (log-add-collected-terms-recursively-equal
            collected-1 collected-2 index))
          ((smaller-bag-p (caar collected-1) (caar collected-2))
           ;; (+ (+ (* c1 f1) r1) (+ (* c2 f2) r2))
           (log-use-axiom-as-rewrite
            `(+ ,sum-1 ,sum-2) '+.associate.right
            `((= |)X| ,(second sum-1)) (= |)Y| ,(third sum-1)) (= |)Z| ,sum-2))
	    index)
           ;; (+ (* c1 f1) (+ r1 (+ (* c2 f2) r2)))
           (let ((r (log-add-collected-terms-recursively
                     (cdr collected-1) collected-2 (cons 2 index))))
             (cond ((null r)
                    ;; (+ (* c1 f1) 0)
                    (log-use-axiom-as-rewrite
                     `(+ ,(second sum-1) 0) '+.zero.right
		     `((= |)X| ,(second sum-1)))
                     index)
                    (log-type-of-expr (second sum-1) (cons 1 (if-test-index)))
                    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    (list (car collected-1)))
                   (t (cons (car collected-1) r)))))
          (t (log-use-axiom-as-rewrite
              `(+ ,sum-1 ,sum-2) '+.right.permute
              `((= |)X| ,sum-1) (= |)Y| ,(second sum-2))
		(= |)Z| ,(third sum-2)))
	      index)
             ;; (+ (* c2 f2) (+ (+ (* c1 f1) r1) r2))
             (let ((r (log-add-collected-terms-recursively
                       collected-1 (cdr collected-2) (cons 2 index))))
               (cond ((null r)
                      ;; (+ (* c2 f2) 0)
                      (log-use-axiom-as-rewrite
                       `(+ ,(second sum-2) 0) '+.zero.right
		       `((= |)X| ,(second sum-2)))
                       index)
                      (log-type-of-expr
                       (second sum-2) (cons 1 (if-test-index)))
                      (push-proof-log 'compute (if-test-index))
                      (push-proof-log 'if-true index)
                      (list (car collected-2)))
                     (t (cons (car collected-2) r))))))))



(defun log-add-collected-terms-recursively-equal
  (collected-1 collected-2 index)
  (let ((expr-1 (raw-expr-of-sum-aux collected-1))
        (expr-2 (raw-expr-of-sum-aux collected-2)))
    (cond ((null (cdr collected-1))
           (cond ((null (cdr collected-2))
                  ;; (+ (* c1 t) (* c2 t))
                  (log-common-factor
                   (caar collected-1) (cdar collected-1) expr-1
                   (cdar collected-2) index))
                 (t
                  ;; (+ (* c1 t) (+ (* c2 t) rest2))
                  (log-use-axiom-as-rewrite
                   `(+ ,expr-1 ,expr-2) '+.associate.left
                   `((= |)X| ,expr-1) (= |)Y| ,(second expr-2))
		     (= |)Z| ,(third expr-2)))
		   index)
                  ;; (+ (+ (* c1 t) (* c2 t)) rest2)
                  (let ((common (log-common-factor
                                 (caar collected-1) (cdar collected-1) expr-1
                                 (cdar collected-2) (cons 1 index))))
                    (when (null common)
                      ;; (+ 0 rest2)
                      (log-use-axiom-as-rewrite
                       `(+ 0 ,(raw-expr-of-sum-aux (cdr collected-2)))
                       '+.zero.left
                       `((= |)X| ,(raw-expr-of-sum-aux (cdr collected-2))))
		       index)
                      (log-type-of-expr (raw-expr-of-sum-aux (cdr collected-2))
                                        (cons 1 (if-test-index)))
                      (push-proof-log 'compute (if-test-index))
                      (push-proof-log 'if-true index))
                    (append common (cdr collected-2))))))
          ((null (cdr collected-2))
           ;; (+ (+ (* c1 t) rest1) (* c2 t))
           (log-use-axiom-as-rewrite
            `(+ ,expr-1 ,expr-2) '+.commutes
	    `((= |)X| ,expr-1) (= |)Y| ,expr-2)) index)
           ;; (+ (* c2 t) (+ (* c1 t) rest1))
           (log-use-axiom-as-rewrite
            `(+ ,expr-2 ,expr-1) '+.associate.left
            `((= |)X| ,expr-2) (= |)Y| ,(second expr-1))
	      (= |)Z| ,(third expr-1)))
	    index)
           ;; (+ (+ (* c2 t) (* c1 t)) rest1)
           (let ((common (log-common-factor
                          (caar collected-2) (cdar collected-2) expr-2
                          (cdar collected-1) (cons 1 index))))
             (when (null common)
               ;; (+ 0 rest1)
               (log-use-axiom-as-rewrite
                `(+ 0 ,(raw-expr-of-sum-aux (cdr collected-1))) '+.zero.left
                `((= |)X| ,(raw-expr-of-sum-aux (cdr collected-1)))) index)
               (log-type-of-expr (raw-expr-of-sum-aux (cdr collected-1))
                                 (cons 1 (if-test-index)))
               (push-proof-log 'compute (if-test-index))
               (push-proof-log 'if-true index))
             (append common (cdr collected-1))))
          (t
           ;; (+ (+ (* c1 t) rest1) (+ (* c2 t) rest2))
           (log-use-axiom-as-rewrite
            `(+ ,expr-1 ,expr-2) '+.associate.left
            `((= |)X| ,expr-1) (= |)Y| ,(second expr-2))
	      (= |)Z| ,(third expr-2)))
	    index)
           ;; (+ (+ (+ (* c1 t) rest1) (* c2 t)) rest2)
           (log-use-axiom-as-rewrite
            `(+ ,expr-1 ,(second expr-2)) '+.commutes
            `((= |)X| ,expr-1) (= |)Y| ,(second expr-2))) (cons 1 index))
           ;; (+ (+ (* c2 t) (+ (* c1 t) rest1)) rest2)
           (log-use-axiom-as-rewrite
            `(+ ,(second expr-2) ,expr-1) '+.associate.left
            `((= |)X| ,(second expr-2)) (= |)Y| ,(second expr-1))
	      (= |)Z| ,(third expr-1)))
            (cons 1 index))
           ;; (+ (+ (+ (* c2 t) (* c1 t)) rest1) rest2)
           (log-use-axiom-as-rewrite
            `(+ (+ (+ ,(second expr-2) ,(second expr-1)) ,(third expr-1))
                ,(third expr-2))
            '+.associate.right
            `((= |)X| (+ ,(second expr-2) ,(second expr-1)))
	      (= |)Y| ,(third expr-1)) (= |)Z| ,(third expr-2)))
            index)
           ;; (+ (+ (* c2 t) (* c1 t)) (+ rest1 rest2))
           (let ((common
                  (log-common-factor
                   (caar collected-2) (cdar collected-2) (second expr-2)
                   (cdar collected-1) (cons 1 index)))
                 (rest
                  (log-add-collected-terms-recursively
                   (cdr collected-1) (cdr collected-2) (cons 2 index))))
             (cond ((null common)
                    (cond ((null rest)
                           (push-proof-log 'compute index))
                          (t
                           ;; (+ 0 rest)
                           (log-use-axiom-as-rewrite
                            `(+ 0 ,(raw-expr-of-sum-aux rest)) '+.zero.left
                            `((= |)X| ,(raw-expr-of-sum-aux rest))) index)
                           (log-type-of-expr (raw-expr-of-sum-aux rest)
                                             (cons 1 (if-test-index)))
                           (push-proof-log 'compute (if-test-index))
                           (push-proof-log 'if-true index))))
                   ((null rest)
                    ;; (+ (* c t) 0)
                    (log-use-axiom-as-rewrite
                     `(+ ,(raw-expr-of-sum-aux common) 0) '+.zero.right
                     `((= |)X| ,(raw-expr-of-sum-aux common))) index)
                    (log-type-of-expr (raw-expr-of-sum-aux common)
                                      (cons 1 (if-test-index)))
                    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)))
             (append common rest))))))
                   



;;; (+ (* c1 f1) (* c2 f2))
;;; Both collected-1 and collected-2 have nil as cdrs.

(defun log-add-terms (collected-1 collected-2 index)
  (let ((factor-1 (caar collected-1))
        (factor-2 (caar collected-2))
        (c1 (cdar collected-1))
        (c2 (cdar collected-2))
        (sum-1 (raw-expr-of-sum-aux collected-1))
        (sum-2 (raw-expr-of-sum-aux collected-2)))
    (cond ((equal factor-1 factor-2)
           ;; (+ (* c1 f) (* c2 f))
           (log-use-axiom-as-rewrite
            `(+ ,sum-1 ,sum-2) '*.collect.+.left
            `((= |)X| ,(second sum-1)) (= |)Y| ,(third sum-1))
	      (= |)Z| ,(second sum-2)))
            index)
           ;; (* (+ c1 c2) f)
           (push-proof-log 'compute (cons 1 index))
           (cond ((zerop (+ c1 c2))
                  (log-use-axiom-as-rewrite
                   `(* 0 ,(third sum-1)) '*.zero.left
                   `((= |)X| ,(third sum-1))) index)
                  nil)
                 (t (list (cons factor-1 (+ c1 c2))))))
          ((smaller-bag-p factor-1 factor-2)
           ;; (+ (* c1 f1) (* c2 f2))
           (list (car collected-1) (car collected-2)))
          (t (log-use-axiom-as-rewrite
              `(+ ,sum-1 ,sum-2) '+.commutes
              `((= |)X| ,sum-1) (= |)Y| ,sum-2)) index)
             ;; (+ (* c2 f2) (* c1 f1))
             (list (car collected-2) (car collected-1))))))



;;; (+ (* c1 f1) (+ (* c2 f2) r))
;;; collected-1 has nil as cdr.

(defun log-add-term-to-collected-terms (collected-1 collected-2 index)
  (let ((factor-1 (caar collected-1))
        (factor-2 (caar collected-2))
        (c1 (cdar collected-1))
        (c2 (cdar collected-2))
        (sum-1 (raw-expr-of-sum-aux collected-1))
        (sum-2 (raw-expr-of-sum-aux collected-2)))
    (cond ((equal factor-1 factor-2)
           ;; (+ (* c1 f) (+ (* c2 f) r2))
           (log-use-axiom-as-rewrite
            `(+ ,sum-1 ,sum-2) '+.associate.left
            `((= |)X| ,sum-1) (= |)Y| ,(second sum-2)) (= |)Z| ,(third sum-2)))
	    index)
           ;; (+ (+ (* c1 f) (* c2 f)) r2)
           (log-use-axiom-as-rewrite
            `(+ ,sum-1 ,(second sum-2)) '*.collect.+.left
            `((= |)X| ,(second sum-1)) (= |)Y| ,(third sum-1))
	      (= |)Z| ,(second (second sum-2))))
            (cons 1 index))
           ;; (+ (* (+ c1 c2) f) r2)
           (push-proof-log 'compute (list* 1 1 index))
           ;; (+ (* c f) r2)
           (cond ((zerop (+ c1 c2))
                  (log-use-axiom-as-rewrite
                   `(* 0 ,(third sum-1)) '*.zero.left
                   `((= |)X| ,(third sum-1))) (cons 1 index))
                  ;; (+ 0 r2)
                  (log-use-axiom-as-rewrite
                   `(+ 0 ,(third sum-2)) '+.zero.left
		   `((= |)X| ,(third sum-2))) index)
                  (log-type-of-expr (third sum-2) (cons 1 (if-test-index)))
                  (push-proof-log 'compute (if-test-index))
                  (push-proof-log 'if-true index)
                  (cdr collected-2))
                 (t (cons (cons factor-1 (+ c1 c2))
                          (cdr collected-2)))))
          ((smaller-bag-p factor-1 factor-2)
           (cons (car collected-1) collected-2))
          (t
           ;; (+ (* c1 f1) (+ (* c2 f2) r2))
           (log-use-axiom-as-rewrite
            `(+ ,sum-1 ,sum-2) '+.right.permute
            `((= |)X| ,sum-1) (= |)Y| ,(second sum-2)) (= |)Z| ,(third sum-2)))
	    index)
           ;; (+ (* c2 f2) (+ (* c1 f1) r2))
           (let ((r (log-add-collected-terms-recursively
                     collected-1 (cdr collected-2) (cons 2 index))))
             (cond ((null r)
                    ;; (+ (* c2 f2) 0)
                    (log-use-axiom-as-rewrite
                     `(+ ,(second sum-2) 0) '+.zero.right
                     `((= |)X| ,(second sum-2))) index)
                    (log-type-of-expr (second sum-2) (cons 1 (if-test-index)))
                    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    (list (car collected-2)))
                   (t (cons (car collected-2) r))))))))



;;; (* bag-1 bag-2)
;;; bag-1 and bag-2 are lexically sorted factors

(defun log-coalesce-bags (bag-1 bag-2 index)
  (let ((expr-1 (make-times-from-bag bag-1))
        (expr-2 (make-times-from-bag bag-2)))
    (when (ord-p expr-1)
      (log-use-axiom-as-rewrite
       `(* ,expr-1 ,expr-2) '*.ord.left
       `((= |)X| ,(ord-expr expr-1)) (= |)Y| ,expr-2)) index)
      (setq expr-1 (ord-expr expr-1))
      (setq bag-1 (list (second (car bag-1)))))
    (when (ord-p expr-2)
      (log-use-axiom-as-rewrite
       `(* ,expr-1 ,expr-2) '*.ord.right
       `((= |)X| ,expr-1) (= |)Y| ,(ord-expr expr-2))) index)
      (setq expr-2 (ord-expr expr-2))
      (setq bag-2 (list (second (car bag-2)))))
    (cond ((lexically-smaller-p (car bag-2) (car bag-1))
           (cond ((null (cdr bag-2))
                  ;; (* bag-1 factor)
                  (log-use-axiom-as-rewrite
                   `(* ,expr-1 ,expr-2) '*.commutes
		   `((= |)X| ,expr-1) (= |)Y| ,expr-2)) index)
                  (cons (car bag-2) bag-1))
                 (t
                  ;; (* bag-1 (* factor rest-2))
                  (log-use-axiom-as-rewrite
                   `(* ,expr-1 ,expr-2) '*.right.permute
                   `((= |)X| ,expr-1) (= |)Y| ,(second expr-2))
		     (= |)Z| ,(third expr-2)))
		   index)
                  ;; (* factor (* bag-1 rest-2))
                  (cons (car bag-2)
                        (log-coalesce-bags
                         bag-1 (cdr bag-2) (cons 2 index))))))
          ((null (cdr bag-1))
           ;; (* factor bag-2)
           (cons (car bag-1) bag-2))
          (t
           ;; (* (* factor rest-1) bag-2)
           (log-use-axiom-as-rewrite
            `(* ,expr-1 ,expr-2) '*.associate.right
            `((= |)X| ,(second expr-1)) (= |)Y| ,(third expr-1))
	      (= |)Z| ,expr-2))
	    index)
           ;; (* factor (* rest-1 bag-2))
           (cons (car bag-1)
                 (log-coalesce-bags (cdr bag-1) bag-2 (cons 2 index)))))))


;;; (+ collected (* coeff expr))
;;; coeff is either 1 or -1.

(defun log-collect-non-constant (expr coeff collected index)
  (let ((sum (raw-expr-of-sum collected)))
    (log-use-axiom-as-rewrite
     `(+ ,sum (* ,coeff ,expr)) '+.commutes
     `((= |)X| ,sum) (= |)Y| (* ,coeff ,expr))) index)
    ;; (+ (* coeff expr) collected)
    (log-insert-term (list expr) coeff collected index)))



;;; Log transformation of (= left right) to (true) or (true) to (= left right)
;;; It is based on the fact that sum and its negation are both restricted
;;; where (= sum 0) is equivalent to (= left right).

(defun log-justify-anti-symmetric (node1 node2 index)
  (let ((expr (e-node-attribute node2)))
    (cond ((eq node1 *true-node*)
           ;; (true)
           (push-proof-log 'if-equal index `(= (true) ,expr) t)
           (push-proof-log 'look-up (if-left-index) expr)
           ;; (if (= (true) (= left right)) (= left right) (true))
           (log-justify-anti-symmetric-aux node2 (cons 2 (if-test-index)))
           (push-proof-log 'compute (if-test-index))
           (push-proof-log 'if-true index)
           ;; (= left right)
           )
          (t
           ;; (= left right)
           (log-justify-anti-symmetric-aux node1 index)
           ;; (true)
           ))))

(defun log-justify-anti-symmetric-aux (node index)
  ;; Start with (= left right).
  (log-sum-conversion-of-= node index)
  ;; (= sum 0)
  (let ((sum (raw-expr-of-sum (sum-of-node node 0))))
    (log-use-axiom-as-rewrite
     `(= ,sum 0) '>=.and.>=.negate.zero `((= |)X| ,sum)) index)
    ;; (if (>= sum 0) (if (>= (negate sum) 0) (true) (= sum 0)) (= sum 0))
    (log-justify-restriction node 0 (if-test-index))
    (push-proof-log 'if-true index)
    ;; (if (>= (negate sum) 0) (true) (= sum 0))
    (log-push-negate-into-sum sum (cons 1 (if-test-index)))
    (log-justify-restriction node 1 (if-test-index))
    (push-proof-log 'if-true index)
    ;; (true)
    ))



;;; Code to log the transformation of (>= sum 0) to (true),
;;; where sum represents the ith tableau entry for node.

(defun log-justify-restriction (node i index)
  (let* ((hdr (aref (e-node-tableau-entry node) i))
         (justification (cond ((row-p hdr) (row-reason-restricted hdr))
                              ((col-p hdr) (col-reason-restricted hdr)))))
    (cond (justification
           (log-justify-restriction-aux justification index))
          (t
           (push-proof-log 'if-equal index
                           `(= ,(raw-expr-of-sum (sum-of-node node i)) 0)
			   t)
           ;; (if (= sum 0) (>= sum 0) (>= sum 0))
           (push-proof-log 'look-up (cons 1 (if-left-index)) 0)
           (push-proof-log 'compute (if-left-index))
           (log-justify-killed node i (if-test-index))
           (push-proof-log 'if-true index)))))

;;; Code to log the transformation of (true) to (>= sum 0),
;;; where sum represents the ith tableau entry for node.

(defun log-justify-restriction-reverse (node i index)
  (let ((sum (raw-expr-of-sum (sum-of-node node i))))
    (push-proof-log 'if-equal index `(= (true) (>= ,sum 0)) t)
    (push-proof-log 'look-up (if-left-index) `(>= ,sum 0))
    ;; (if (= (true) (>= sum 0)) (>= sum 0) (true))
    (log-justify-restriction node i (cons 2 (if-test-index)))
    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)))



(defun log-justify-restriction-aux (justification index)
  (cond ((atom justification)
         (case justification
           (contradict
            (push-proof-log 'look-up index *true*))))
        (t
         (case (car justification)
           (square-nonneg
            (log-justify-square-nonneg (second justification) index))
           (>=-true (log-justify->=-true (second justification) index))
           (>=-false (log-justify->=-false (second justification) index))
           (shift (log-justify-shift
                   (second justification) (third justification) index))
           (equal-restrict
            (log-justify-equal-restrict
             (second justification) (third justification)
             (fourth justification) index))
           (square (log-justify-square (second justification) index))
           (opposite-manifestly-negative
            (log-justify-opposite-negatively-maximized
             (second justification) (third justification) index))
           (*-up (log-justify-*-up
                  (second justification) (third justification)
                  (fourth justification) (fifth justification)
                  (sixth justification) index))
           (*-l (log-justify-*-l
                 (second justification) (third justification)
                 (fourth justification) (fifth justification)
                 (sixth justification) (seventh justification) index))
           (*-ll (log-justify-*-ll
                  (second justification) (third justification)
                  (fourth justification) (fifth justification)
                  (sixth justification) index))
           (*-r (log-justify-*-r
                 (second justification) (third justification)
                 (fourth justification) (fifth justification)
                 (sixth justification) (seventh justification) index))
           (*-rr (log-justify-*-rr
                  (second justification) (third justification)
                  (fourth justification) (fifth justification)
                  (sixth justification) index))
           
           )))
  )




;;; Log transformation of (>= sum 0) to (true),
;;; where sum is the sum for (* a b),
;;;       a = b, and
;;;       node represents (* a b).

(defun log-justify-square-nonneg (node index)
  (let ((expr (e-node-attribute node))
        (sum (raw-expr-of-sum (sum-of-node node 0))))
    ;; (>= sum 0)
    (push-proof-log 'if-equal index `(= ,sum ,expr) t)
    (push-proof-log 'look-up (cons 1 (if-left-index)) expr)
    ;; (if (= sum (* a b)) (>= (* a b) 0) (>= sum 0))
    (log-collect-terms expr (cons 2 (if-test-index)))
    ;; (if (= sum sum) (>= (* a b) 0) (>= sum 0))
    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)
    ;; (>= (* a b) 0)
    (log-node-equality
     (arg-2-node node) (arg-1-node node) (list* 2 1 index))
    ;; (>= (* a a) 0)
    (log-use-axiom-as-rewrite
     `(>= (* ,(second expr) ,(second expr)) 0) 'square.non.negative
     `((= |)X| ,(second expr))) index)
    ;; (true)
    ))

;;; Log transformation of (>= sum 0) to (true) based on the fact that
;;; (>= a b) is equivalent to (true), where sum is sum for the inequality
;;; (>= a b) and node represents (>= a b).

(defun log-justify->=-true (node index)
  (let ((sum (raw-expr-of-sum (sum-of-node node 0)))
        (expr (e-node-attribute node)))
    (push-proof-log 'if-equal index `(= (>= ,sum 0) ,expr) t)
    ;; (if (= (>= sum 0) (>= a b)) (>= sum 0) (>= sum 0))
    (push-proof-log 'look-up (if-left-index) expr)
    (log-sum-conversion-of->= node (cons 2 (if-test-index)))
    ;; (if (= (>= sum 0) (>= sum 0)) (>= a b) (>= sum 0))
    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)
    ;; (>= a b)
    (log-node-equality node *true-node* index)
    ;; (true)
    ))



;;; Log transformation of (>= sum1 0) to (true) based on the fact that
;;; (>= a b) is equivalent to (false), where sum1 is the opposite sum
;;; for the inequality (>= a b) and node represents (>= a b).

(defun log-justify->=-false (node index)
  (let ((sum (raw-expr-of-sum (sum-of-node node 0)))
        (sum1 (raw-expr-of-sum (sum-of-node node 1)))
        (expr (e-node-attribute node)))
    ;; Start with (>= sum1 0)
    (log-use-axiom index 'integer.is.nat.or.negative)
    ;; (if (all (x) (if (= (type-of x) (int))
    ;;                  (if (>= x 0) (true) (>= (+ -1 (negate x)) 0))
    ;;                  (true)))
    ;;     (>= sum1 0)
    ;;     (true))
    (push-proof-log
     'instantiate-universal (if-test-index)
     `(= ,(car (axiom-args (get-event 'integer.is.nat.or.negative))) ,sum))
    ;; (if (if (if (= (type-of sum) (int))
    ;;             (if (>= sum 0) (true) (>= (+ -1 (negate sum)) 0))
    ;;             (true))
    ;;         (all (x) (if (= (type-of x) (int))
    ;;                      (if (>= x 0) (true) (>= (+ -1 (negate x)) 0))
    ;;                      (true)))
    ;;         (false))
    ;;     (>= sum1 0)
    ;;     (true))
    (push-proof-log 'use-axiom (cons 2 (if-test-index))
                    'integer.is.nat.or.negative t)
    (log-type-of-expr sum (list* 1 1 1 (if-test-index)))
    (push-proof-log 'compute (list* 1 1 (if-test-index)))
    (push-proof-log 'if-true (cons 1 (if-test-index)))
    ;; (if (if (if (>= sum 0) (true) (>= (+ -1 (negate sum)) 0))
    ;;         (true)
    ;;         (false))
    ;;     (>= sum1 0)
    ;;     (true))
    (log-push-negate-into-sum sum (list* 2 1 3 1 (if-test-index)))
    (log-use-axiom-as-rewrite
     `(+ -1 (+ ,(- (second sum)) ,(third sum1))) '+.associate.left
     `((= |)X| -1) (= |)Y| ,(- (second sum))) (= |)Z| ,(third sum1)))
     (list* 1 3 1 (if-test-index)))
    (push-proof-log 'compute (list* 1 1 3 1 (if-test-index)))
    ;; (if (if (if (>= sum 0) (true) (>= sum1 0)) (true) (false))
    ;;     (>= sum1 0)
    ;;     (true))
    (push-proof-log
     'if-equal (list* 1 1 (if-test-index)) `(= (>= ,sum 0) ,expr) t)
    (push-proof-log 'look-up (list* 2 1 1 (if-test-index)) expr)
    ;; (if (if (if (if (= (>= sum 0) (>= a b)) (>= a b) (>= sum 0))
    ;;             (true)
    ;;             (>= sum1 0))
    ;;         (true)
    ;;         (false))
    ;;     (>= sum1 0)
    ;;     (true))
    (log-sum-conversion-of->= node (list* 2 1 1 1 (if-test-index)))
    (push-proof-log 'compute (list* 1 1 1 (if-test-index)))
    (push-proof-log 'if-true (list* 1 1 (if-test-index)))
    ;; (if (if (if (>= a b) (true) (>= sum1 0)) (true) (false))
    ;;     (>= sum1 0)
    ;;     (true))
    (log-node-equality node *false-node* (list* 1 1 (if-test-index)))
    (push-proof-log 'if-false (cons 1 (if-test-index)))
    ;; (if (if (>= sum1 0) (true) (false))
    ;;     (>= sum1 0)
    ;;     (true))
    (push-proof-log 'case-analysis index 1)
    ;; (if (>= sum1 0)
    ;;     (if (true) (>= sum1 0) (true))
    ;;     (if (false) (>= sum1 0) (true)))
    (push-proof-log 'if-true (if-left-index))
    (push-proof-log 'if-false (if-right-index))
    ;; (if (>= sum1 0) (>= sum1 0) (true))
    (push-proof-log 'look-up (if-left-index) *true*)
    (push-proof-log 'if-equal index)
    ;; (true)
    ))



;;; Log the transformation of (>= sum1 0) to (true)
;;; based on (= a b) is false and (>= sum 0)
;;; where sum1 = (+ -1 sum),
;;;       sum represents the inequality (>= a b) or (>= b a), and
;;;       node is the node for (= a b)

(defun log-justify-shift (node i index)
  (let ((sum (raw-expr-of-sum (sum-of-node node i)))
        (expr (e-node-attribute node)))
    ;; (>= sum1 0)
    (push-proof-log 'if-equal (list* 1 1 index)
                    `(= ,(+ -1 (second sum)) (+ -1 ,(second sum))) t)
    (push-proof-log 'look-up (list* 2 1 1 index) `(+ -1 ,(second sum)))
    (push-proof-log 'compute (list* 2 1 1 1 index))
    (push-proof-log 'compute (list* 1 1 1 index))
    (push-proof-log 'if-true (list* 1 1 index))
    (log-use-axiom-as-rewrite
     `(+ (+ -1 ,(second sum)) ,(third sum)) '+.associate.right
     `((= |)X| -1) (= |)Y| ,(second sum)) (= |)Z| ,(third sum))) (cons 1 index))
    ;; (>= (+ -1 sum) 0)
    (log-use-axiom index '>=.zero.and.not.=.zero)
    ;; (if (all (x) (if (= x 0)
    ;;                  (true)
    ;;                  (if (= (type-of x) (int))
    ;;                      (= (>= x 0) (>= (+ -1 x) 0))
    ;;                      (true))))
    ;;     (>= (+ -1 sum) 0)
    ;;     (true))
    (push-proof-log 'instantiate-universal (if-test-index)
                    `(= ,(car (axiom-args (get-event '>=.zero.and.not.=.zero)))
                        ,sum))
    (push-proof-log
     'use-axiom (cons 2 (if-test-index)) '>=.zero.and.not.=.zero t)
    ;; (if (if (if (= sum 0) (true) (if (= (type-of sum) (int))
    ;;                                  (= (>= sum 0) (>= (+ -1 sum) 0))
    ;;                                  (true)))
    ;;         (true)
    ;;         (false))
    ;;     (>= (+ -1 sum) 0)
    ;;     (true))
    (log-type-of-expr sum (list* 1 1 3 1 (if-test-index)))
    (push-proof-log 'compute (list* 1 3 1 (if-test-index)))
    (push-proof-log 'if-true (list* 3 1 (if-test-index)))
    ;; (if (if (if (= sum 0) (true) (= (>= sum 0) (>= (+ -1 sum) 0)))
    ;;         (true)
    ;;         (false))
    ;;     (>= (+ -1 sum) 0)
    ;;     (true))
    (push-proof-log
     'if-equal (list* 1 1 (if-test-index)) `(= (= ,sum 0) ,expr) t)
    (push-proof-log 'look-up (list* 2 1 1 (if-test-index)) expr)
    ;; (if (if (if (if (= (= sum 0) (= a b)) (= a b) (= sum 0))
    ;;             (true)
    ;;             (= (>= sum 0) (>= (+ -1 sum) 0)))
    ;;         (true)
    ;;         (false))
    ;;     (>= (+ -1 sum) 0)
    ;;     (true))
    (push-proof-log 'case-analysis index 1)
    (push-proof-log 'if-true (if-left-index))
    (push-proof-log 'if-false (if-right-index))
    (log-node-equality node *false-node* (list* 2 1 (if-test-index)))
    ;; (if (if (if (= (= sum 0) (= a b)) (false) (= sum 0))
    ;;         (true)
    ;;         (= (>= sum 0) (>= (+ -1 sum) 0)))
    ;;     (>= (+ -1 sum) 0)
    ;;     (true))
    (log-sum-conversion-of-= node (list* 2 1 1 (if-test-index)))
    (when (= i 1) (log-negate-=-zero sum (list* 1 1 1 (if-test-index))))
    (push-proof-log 'compute (list* 1 1 (if-test-index)))
    (push-proof-log 'if-true (cons 1 (if-test-index)))
    ;; (if (if (false) (true) (= (>= sum 0) (>= (+ -1 sum) 0)))
    ;;     (>= (+ -1 sum) 0)
    ;;     (true))
    (push-proof-log 'if-false (if-test-index))
    (push-proof-log 'look-up (if-left-index) `(>= ,sum 0))
    (log-justify-restriction node i (if-left-index))
    (push-proof-log 'if-equal index)
    ;; (true)
    ))



;;; Log transformation of (= sum 0) to (= sum1 0),
;;; where sum1 is the negation of sum.

(defun log-negate-=-zero (sum index)
  (log-use-axiom-as-rewrite `(= ,sum 0) 'negate.=.zero `((= |)X| ,sum)) index)
  ;; (if (= (type-of sum) (int)) (= (negate sum) 0) (= sum 0))
  (log-type-of-expr sum (cons 1 (if-test-index)))
  (push-proof-log 'compute (if-test-index))
  (push-proof-log 'if-true index)
  ;; (= (negate sum) 0)
  (log-push-negate-into-sum sum (cons 1 index)))

;;; Log the transformation of (>= sum 0) to (true)
;;; based on (>= sum1 0) and sum = sum1 (sums are equal after
;;; deleting zero terms).
;;; owner1 is owner of sum, owner2 is owner of sum1,
;;; justification is justification for equality between sum and sum1
;;; and is of the form: (=-sums owner1 owner2 triples1 triples2)

(defun log-justify-equal-restrict (owner1 owner2 justification index)
  ;; (>= sum 0)
  (let ((sum (sum-of-node (cdr owner1) (car owner1)))
        (sum1 (sum-of-node (cdr owner2) (car owner2))))
    (let ((expr (raw-expr-of-sum sum))
          (expr1 (raw-expr-of-sum sum1)))
      (push-proof-log 'if-equal index `(= (>= ,expr 0) (>= ,expr1 0)) t)
      (push-proof-log 'look-up (if-left-index) `(>= ,expr1 0))
      ;; (if (= (>= sum 0) (>= sum1 0)) (>= sum1 0) (>= sum 0))
      (log-justify-restriction (cdr owner2) (car owner2) (if-left-index))
      ;; (if (= (>= sum 0) (>= sum1 0)) (true) (>= sum 0))
      (push-proof-log 'if-equal index `(= ,expr ,expr1) t)
      (push-proof-log 'look-up (list* 1 1 1 (if-left-index)) expr1)
      ;; (if (= sum sum1)
      ;;     (if (= (>= sum1 0) (>= sum1 0)) (true) (>= sum 0))
      ;;     (if (= (>= sum 0) (>= sum1 0)) (true) (>= sum 0)))
      (push-proof-log 'compute (cons 1 (if-left-index)))
      (push-proof-log 'if-true (if-left-index))
      ;; (if (= sum sum1)
      ;;     (true)
      ;;     (if (= (>= sum 0) (>= sum1 0)) (true) (>= sum 0)))
      (unless (equal owner1 (second justification))
	(log-use-axiom-as-rewrite
	 `(= ,expr ,expr1) '=.commutes `((= |)X| ,expr) (= |)Y| ,expr1))
	 (if-test-index)))
      (log-justify-=-sums justification (if-test-index))
      (push-proof-log 'if-true index)
      ;; (true)
      )))


;;; Log transformation of (>= sum 0) based on the fact that sum
;;; is the sum for (* a b) and a is equal to b.
;;; node is the e-node for (* a b)

(defun log-justify-square (node index)
  (let ((sum (raw-expr-of-sum (sum-of-node node 0)))
        (expr (e-node-attribute node)))
    (push-proof-log 'if-equal index `(= ,sum ,expr) t)
    (push-proof-log 'look-up (cons 1 (if-left-index)) expr)
    ;; (if (= sum (* a b)) (>= (* a b) 0) (>= sum 0))
    (log-collect-terms expr (cons 2 (if-test-index)))
    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)
    ;; (>= (* a b) 0)
    (log-node-equality (arg-1-node node) (arg-2-node node) (list* 2 1 index))
    ;; (>= (* a a) 0)
    (log-use-axiom-as-rewrite
     `(>= (* ,(second expr) ,(second expr)) 0) 'square.non.negative
     `((= |)X| ,(second expr))) index)))



;;; Log transformation of (>= sum 0) to true based on the fact
;;; that the opposite sum is manifestly maximized at a negative
;;; value.

(defun log-justify-opposite-negatively-maximized (owner coll-triples index)
  ;; (>= sum 0)
  (let* ((sum (sum-of-node (cdr owner) (car owner)))
         (osum (sum-of-node (cdr owner)
                            (opposite-index (cdr owner) (car owner))))
         (sum-gcd (if (null (cdr sum))
                      1
                    (apply #'gcd (mapcar #'cdr (cdr sum)))))
         (osum-gcd (if (null (cdr osum))
                       1
                     (apply #'gcd (mapcar #'cdr (cdr osum))))))
    (cond
     ((and (= sum-gcd 1) (= osum-gcd 1))
      (let* ((k (apply #'lcm (mapcar #'(lambda (u) (denominator (car u)))
                                     coll-triples)))
             (n (- (* k (car (car (last coll-triples))))))
             (triples (mapcar #'(lambda (u) (cons (* (- k) (car u)) (cdr u)))
                              coll-triples)))
        (cond
         ((= k 1)
          ;; remainder of sum (- n 1) will be taken care of by
          ;; log-justify-triples, since n >= 1.
          (log-justify-triples sum triples index))
         (t
          (log-justify-opposite-negatively-maximized-aux
           sum triples k n index)))))
     ((= sum-gcd 1)                     ; (osum-gcd <> 1)
      (let* ((k (apply #'lcm (mapcar #'(lambda (u) (denominator (car u)))
                                     coll-triples)))
             ;; Need to adjust n to take into account the fact that osum
             ;; is not normalized.  The adjustment corresponds to
             ;; a plane shift.
             (n (+ (- (* k (car (car (last coll-triples)))))
                   (* k (mod (car osum) osum-gcd))))
             (triples (mapcar #'(lambda (u) (cons (* (- k) (car u)) (cdr u)))
                              coll-triples)))
        (cond
         ((= k 1)
          (log-multiply->=-zero osum-gcd (raw-expr-of-sum sum) index)
          ;; (>= (* osum-gcd sum) 0)
          (log-multiply-collected-terms-by-constant sum osum-gcd index)
          ;; (>= osum-gcd*sum 0)
          ;; Although osum is not normalized, the non-constant part of the
          ;; triples would still be enough to justify the inequality.
          ;; Shifting osum without normalizing the coefficients would still
          ;; result in a sum that is manifestly maximized at a negative
          ;; value (shifting can only reduce the sample value).
          (log-justify-triples
           (multiply-collected-terms-by-constant sum osum-gcd) triples index))
         (t
          (log-multiply->=-zero osum-gcd (raw-expr-of-sum sum) index)
          ;; (>= (* osum-gcd sum) 0)
          (log-multiply-collected-terms-by-constant sum osum-gcd index)
          ;; (>= osum-gcd*sum 0)
          (log-justify-opposite-negatively-maximized-aux
           (multiply-collected-terms-by-constant sum osum-gcd)
           triples k n index)
          )))
      )
     (t                                 ; (osum-gcd = 1, sum-gcd <> 1)
      (let* ((k (apply #'lcm (mapcar #'(lambda (u) (denominator (car u)))
                                     coll-triples)))
             (k1 (* k sum-gcd))
             ;; Need to adjust n here as well.
             (n (+ (- (* k1 (car (car (last coll-triples)))))
                   (* k (mod (car sum) sum-gcd))))
             (triples (mapcar #'(lambda (u) (cons (* (- k1) (car u)) (cdr u)))
                              coll-triples)))
        (cond
         ((= k 1)
          (log-justify-triples sum triples index))
         (t
          (log-justify-opposite-negatively-maximized-aux
           sum triples k n index))))))))

(defun log-justify-opposite-negatively-maximized-aux (sum triples k n index)
  (let* ((ksum (multiply-collected-terms-by-constant sum k))
         (expr (raw-expr-of-sum ksum))
         (sum-expr (raw-expr-of-sum sum)))
    (log-multiply->=-zero k sum-expr index)
    ;; (>= (* k sum) 0)
    ;; We now need to transform this to (>= tsum 0)
    ;; where tsum is the negation of the sum represented
    ;; by the non-constant entries of the multiplied triples
    ;; tsum is equal to (- -k*osum n)
    (cond
     ((>= n k)
      (log-multiply-collected-terms-by-constant sum k (cons 1 index))
      ;; (>= ksum 0)
      (log-use-axiom index 'inequality.lemma)
      (let ((event (get-event 'inequality.lemma)))
        (log-rewrite
         (make-if (make-series-of-quantification
                   'all (axiom-args event) (axiom-formula event))
                  `(>= ,expr 0)
                  *true*)
         `((= ,(first (axiom-args event)) ,expr)
           (= ,(second (axiom-args event)) ,(- n k)))
         index)
        (push-proof-log
         'use-axiom (if-test-index) 'inequality.lemma t)
        (push-proof-log 'if-true index)
        ;; (if (= (type-of expr) (int))
        ;;     (if (>= n-k 0)
        ;;         (if (>= (- expr n-k) 0)
        ;;             (true)
        ;;             (>= expr 0))
        ;;         (>= expr 0))
        ;;     (>= expr 0))
        ;; expr is really ksum
        (log-type-of-expr expr (cons 1 (if-test-index)))
        (push-proof-log 'compute (if-test-index))
        (push-proof-log 'if-true index)
        (push-proof-log 'compute (if-test-index))
        (push-proof-log 'if-true index)
        ;; (if (>= (- expr n-k) 0) (true) (>= expr 0))
        (log-use-axiom-as-rewrite
         `(- ,expr ,(- n k)) '-.+.left.to.+.-.left
         `((= |)X| ,(second expr)) (= |)Y| ,(third expr)) (= |)Z| ,(- n k)))
         (cons 1 (if-test-index)))
        (push-proof-log 'compute (list* 1 1 (if-test-index)))
        ;; (if (>= triples 0) (true) (>= expr 0))
        (log-justify-triples
         (cons (- (car ksum) (- n k)) (cdr ksum)) triples
         (if-test-index))
        (push-proof-log 'if-true index)))
     (t
      ;; (>= (* k sum) 0)
      (let ((sum-expr (raw-expr-of-sum sum)))
        (push-proof-log
         'if-equal index
         `(= (>= (* ,k ,sum-expr) 0)
             (>= (+ ,(- k n) (* ,k ,sum-expr)) 0))
	 t)
        (push-proof-log 'look-up (if-left-index)
                        `(>= (+ ,(- k n) (* ,k ,sum-expr)) 0))
        ;; (if (= (>= (* k sum) 0)
        ;;        (>= (+ k-n (* k sum)) 0))
        ;;     (>= (+ k-n (* k sum)) 0)
        ;;     (>= (* k sum) 0))
        (log-use-axiom-as-rewrite
         `(>= (+ ,(- k n) (* ,k ,sum-expr)) 0) 'normalize.>=
         `((= |)X| ,(- k n)) (= |)Y| ,k) (= |)Z| ,sum-expr))
	 (cons 2 (if-test-index)))
        ;; (if (= (>= (* k sum) 0)
        ;;        (if (>= k-n 0)
        ;;            (if (>= k (+ k-n 1))
        ;;                (if (= (type-of sum) (int))
        ;;                    (>= sum 0)
        ;;                    (>= (+ k-n (* k sum)) 0))
        ;;                (>= (+ k-n (* k sum)) 0))
        ;;            (>= (+ k-n (* k sum)) 0)))
        ;;     (>= (+ k-n (* k sum)) 0)
        ;;     (>= (* k sum) 0))
        (push-proof-log 'compute (list* 1 2 (if-test-index)))
        (push-proof-log 'if-true (cons 2 (if-test-index)))
        ;; (if (= (>= (* k sum) 0)
        ;;        (if (>= k (+ k-n 1))
        ;;            (if (= (type-of sum) (int))
        ;;                (>= sum 0)
        ;;                (>= (+ k-n (* k sum)) 0))
        ;;            (>= (+ k-n (* k sum)) 0)))
        ;;     (>= (+ k-n (* k sum)) 0)
        ;;     (>= (* k sum) 0))
        (push-proof-log 'compute (list* 2 1 2 (if-test-index)))
        (push-proof-log 'compute (list* 1 2 (if-test-index)))
        (push-proof-log 'if-true (cons 2 (if-test-index)))
        (log-type-of-expr sum-expr (list* 1 1 2 (if-test-index)))
        (push-proof-log 'compute (list* 1 2 (if-test-index)))
        (push-proof-log 'if-true (cons 2 (if-test-index)))
        ;; (if (= (>= (* k sum) 0)
        ;;        (>= sum 0))
        ;;     (>= (+ k-n (* k sum)) 0)
        ;;     (>= (* k sum) 0))
        (log-multiply->=-zero k sum-expr (cons 2 (if-test-index)))
        (push-proof-log 'compute (if-test-index))
        (push-proof-log 'if-true index)
        ;; (>= (+ k-n (* k sum)) 0)
        (log-multiply-collected-terms-by-constant
         sum k (list* 2 1 index))
        ;; (>= (+ k-n ksum) 0)
        (log-use-axiom-as-rewrite
         `(+ ,(- k n) ,expr) '+.associate.left
         `((= |)X| ,(- k n)) (= |)Y| ,(second expr)) (= |)Z| ,(third expr)))
         (cons 1 index))
        (push-proof-log 'compute (list* 1 1 index))
        ;; (>= triples 0)
        (log-justify-triples
         (cons (- (car ksum) (- n k)) (cdr ksum))
         triples index))))))  





;;; Log the transformation of (= sum sum1) to (true).
;;; The form of justification is: (=-sums owner1 owner2 triples1 triples2)

(defun log-justify-=-sums (justification index)
  (let ((owner1 (second justification))
        (owner2 (third justification))
        (triples1 (fourth justification))
        (triples2 (fifth justification)))
    (let ((mult (lcm (apply #'lcm (mapcar #'(lambda (u) (denominator (car u)))
                                          triples1))
                     (apply #'lcm (mapcar #'(lambda (u) (denominator (car u)))
                                          triples2))))
          (sum (sum-of-node (cdr owner1) (car owner1)))
          (sum1 (sum-of-node (cdr owner2) (car owner2))))
      (let ((expr (raw-expr-of-sum sum))
            (expr1 (raw-expr-of-sum sum1)))
        (when (>= mult 2)
          (push-proof-log
           'if-equal index
           `(= (= ,expr ,expr1) (= (* ,mult ,expr) (* ,mult ,expr1)))
	   t)
          (push-proof-log 'look-up (if-left-index)
                          `(= (* ,mult ,expr) (* ,mult ,expr1)))
          ;; (if (= (= sum sum1) (= (* mult sum) (* mult sum1)))
          ;;     (= (* mult sum) (* mult sum1))
          ;;     (= sum sum1))
          (log-remove-common-multiplier
           mult expr expr1 (cons 2 (if-test-index)))
          (push-proof-log 'compute (if-test-index))
          (push-proof-log 'if-true index)
          ;; (= (* mult sum) (* mult sum1))
          (log-push-multiplier-in mult expr (cons 1 index))
          (log-push-multiplier-in mult expr1 (cons 2 index)))
        ;; (= msum msum1)
        (log-remove-dead-triples
         (cons (* mult (car sum))
               (mapcar #'(lambda (u) (cons (car u) (* mult (cdr u))))
                       (cdr sum)))
         (mapcar #'(lambda (u) (cons (* mult (car u)) (cdr u))) triples1)
         (cons 1 index))
        (log-remove-dead-triples
         (cons (* mult (car sum1))
               (mapcar #'(lambda (u) (cons (car u) (* mult (cdr u))))
                       (cdr sum1)))
         (mapcar #'(lambda (u) (cons (* mult (car u)) (cdr u))) triples2)
         (cons 2 index))
        (push-proof-log 'compute index)
        ;; (true)
        ))))



;;; Log transformation of (= (* c expr1) (* c expr2)) to (= expr1 expr2)
;;; where c is a non-zero constant, expr1 and expr2 each is an integer
;;; literal or an arithmetic expression.

(defun log-remove-common-multiplier (c expr1 expr2 index)
  ;; Start with (= (* c expr1) (* c expr2)).
  (log-use-axiom-as-rewrite
   `(= (* ,c ,expr1) (* ,c ,expr2)) 'remove.common.multiplier
   `((= |)X| ,c) (= |)Y| ,expr1) (= |)Z| ,expr2)) index)
  ;; (if (= (type-of c) (int))
  ;;     (if (= c 0)
  ;;         (= (* c expr1) (* c expr2))
  ;;         (if (= (type-of expr1) (int))
  ;;             (if (= (type-of expr2) (int))
  ;;                 (= expr1 expr2)
  ;;                 (= (* c expr1) (* c expr2)))
  ;;             (= (* c expr1) (* c expr2))))
  ;;     (= (* c expr1) (* c expr2)))
  (push-proof-log 'compute (cons 1 (if-test-index)))
  (push-proof-log 'compute (if-test-index))
  (push-proof-log 'if-true index)
  (push-proof-log 'compute (if-test-index))
  (push-proof-log 'if-false index)
  ;; (if (= (type-of expr1) (int))
  ;;     (if (= (type-of expr2) (int))
  ;;         (= expr1 expr2)
  ;;         (= (* c expr1) (* c expr2)))
  ;;     (= (* c expr1) (* c expr2)))
  (log-type-of-expr expr1 (cons 1 (if-test-index)))
  (push-proof-log 'compute (if-test-index))
  (push-proof-log 'if-true index)
  ;; (if (= (type-of expr2) (int))
  ;;     (= expr1 expr2)
  ;;     (= (* c expr1) (* c expr2)))
  (log-type-of-expr expr2 (cons 1 (if-test-index)))
  (push-proof-log 'compute (if-test-index))
  (push-proof-log 'if-true index)
  ;; (= expr1 expr2)
  )



;;; Log the multiplication of coefficients of expr (which is a sum).

(defun log-push-multiplier-in (c expr index)
  ;; Start with (* c expr)
  (cond ((integerp expr)
         (push-proof-log 'compute index))
        (t
         ;; expr is (+ constant rest)
         (log-use-axiom-as-rewrite
	  `(* ,c ,expr) '*.distribute.+.right
	  `((= |)X| ,c) (= |)Y| ,(second expr)) (= |)Z| ,(third expr))) index)
         (push-proof-log 'compute (cons 1 index))
         ;; (+ cc (* c rest))
         (log-push-multiplier-in-aux c (third expr) (cons 2 index)))))

(defun log-push-multiplier-in-aux (c expr index)
  ;; Start with (* c expr)
  (cond ((+-p expr)
         ;; expr is (+ (* constant term) rest)
         (log-use-axiom-as-rewrite
	  `(* ,c ,expr) '*.distribute.+.right
	  `((= |)X| ,c) (= |)Y| ,(second expr)) (= |)Z| ,(third expr))) index)
         ;; (+ (* c (* constant term)) (* c rest))
         (log-use-axiom-as-rewrite
          `(* ,c ,(second expr)) '*.associate.left
          `((= |)X| ,c) (= |)Y| ,(second (second expr)))
	    (= |)Z| ,(third (second expr))))
	  (cons 1 index))
         (push-proof-log 'compute (list* 1 1 index))
         ;; (+ (* cc term) (* c rest))
         (log-push-multiplier-in-aux c (third expr) (cons 2 index)))
        (t
         ;; expr is (* constant term)
         (log-use-axiom-as-rewrite
	  `(* ,c ,expr) '*.associate.left
	  `((= |)X| ,c) (= |)Y| ,(second expr)) (= |)Z| ,(third expr))) index)
         (push-proof-log 'compute (cons 1 index))
         ;; (* cc term)
         )))



;;; Log the subtraction of dead triples from sum.

(defun log-remove-dead-triples (sum triples index)
  (setq sum (convert-e-node-in-sum sum))
  (loop for triple in triples
        when (eq (third triple) 'dead)
        do (setq sum (log-subtract-dead-sum
                      sum (first triple) (second triple) index)))
  sum)

(defun convert-e-node-in-sum (sum)
  (cons (car sum)
        (mapcar #'(lambda (u)
                    (cons (if (e-node-p (car u))
                              (make-bag (e-node-attribute (car u)))
                            (car u))
                          (cdr u)))
                (cdr sum))))

;;; Log the subtraction of (* c sum1) from sum based on the fact that
;;; sum1 is 0.

(defun log-subtract-dead-sum (sum c owner index)
  (let ((sum1 (convert-e-node-in-sum (sum-of-node (cdr owner) (car owner))))
        (expr (raw-expr-of-sum sum)))
    ;; Start with sum.
    ;; We actually add (* -c sum1) rather than subtract (* c sum1).
    (let ((sum2 (cons (* (- c) (car sum1))
                      (mapcar #'(lambda (u) (cons (car u) (* (- c) (cdr u))))
                              (cdr sum1)))))
      (push-proof-log 'if-equal index
                      `(= ,expr (+ ,expr ,(raw-expr-of-sum sum2)))
		      t)
      (push-proof-log 'look-up (if-left-index)
                      `(+ ,expr ,(raw-expr-of-sum sum2)))
      ;; (if (= sum (+ sum sum2)) (+ sum sum2) sum)
      (log-factor-out (- c) sum2 (list* 2 2 (if-test-index)))
      ;; (if (= sum (+ sum (* -c sum1))) (+ sum sum2) sum)
      (push-proof-log 'if-equal (list* 2 2 2 (if-test-index))
                      `(= ,(raw-expr-of-sum sum1) 0)
		      t)
      (push-proof-log 'look-up (list* 2 2 2 2 (if-test-index)) 0)
      ;; (if (= sum (+ sum (* -c (if (= sum1 0) 0 sum1))))
      ;;     (+ sum sum2)
      ;;     sum)
      (log-justify-killed
       (cdr owner) (car owner) (list* 1 2 2 2 (if-test-index)))
      (push-proof-log 'if-true (list* 2 2 2 (if-test-index)))
      ;; (if (= sum (+ sum (* -c 0))) (+ sum sum2) sum)
      (log-use-axiom-as-rewrite
       `(* ,(- c) 0) '*.zero.right `((= |)X| ,(- c)))
       (list* 2 2 (if-test-index)))
      (log-use-axiom-as-rewrite
       `(+ ,expr 0) '+.zero.right `((= |)X| ,expr)) (cons 2 (if-test-index)))
      (log-type-of-expr expr (list* 1 1 2 (if-test-index)))
      (push-proof-log 'compute (list* 1 2 (if-test-index)))
      (push-proof-log 'if-true (cons 2 (if-test-index)))
      ;; (if (= sum sum) (+ sum sum2) sum)
      (push-proof-log 'compute (if-test-index))
      (push-proof-log 'if-true index)
      ;; (+ sum sum2)
      (log-add-collected-terms sum sum2 index)
      )))




;;; Log the transformation of (= sum 0) to (true),
;;; where sum represents the ith tableau entry for node.

(defun log-justify-killed (node i index)
  (let* ((hdr (aref (e-node-tableau-entry node) i))
         (justification (cond ((row-p hdr) (row-reason-killed hdr))
                              ((col-p hdr) (col-reason-killed hdr)))))
    (log-justify-killed-aux justification index)))

(defun log-justify-killed-aux (justification index)
  (cond ((eq justification 'zero-row)
         (push-proof-log 'compute index))
        ((and (consp justification) (eq (car justification) '=-true))
         (log-justify-kill-=-true (second justification) index))
        ((and (consp justification) (eq (car justification) 'zero))
         (log-justify-kill-zero (second justification) index))
        ((and (consp justification) (eq (car justification) 'constant-sum))
         (log-justify-kill-constant-sum
          (second justification) (third justification) index))
        ((and (consp justification) (eq (car justification) 'anti-symmetric))
         (let ((owner (second (third justification))))
           (log-justify-kill-anti-symmetric
            (cdr owner) (car owner) (second justification)
            (third justification) index)))
        ((and (consp justification) (eq (car justification) 'minimized-col))
         (log-justify-kill-minimized-col
          (second justification) (third justification)
          (fourth justification) index)))
  )

;;; Log transformation of (= sum 0) to (true) based on the knowledge
;;; that (= a b) is (true),
;;; where sum represents the sum for (= a b),
;;;       node is the e-node for (= a b)

(defun log-justify-kill-=-true (node index)
  ;; Start with (= sum 0)
  (let ((sum (raw-expr-of-sum (sum-of-node node 0))))
    (push-proof-log 'if-equal index `(= (= ,sum 0) ,(e-node-attribute node)) t)
    (push-proof-log 'look-up (if-left-index) (e-node-attribute node))
    ;; (if (= (= sum 0) (= a b)) (= a b) (= sum 0))
    (log-node-equality node *true-node* (if-left-index))
    ;; (if (= (= sum 0) (= a b)) (true) (= sum 0))
    (log-sum-conversion-of-= node (cons 2 (if-test-index)))
    ;; (if (= (= sum 0) (= sum 0)) (true) (= sum 0))
    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)
    ;; (true)
    ))

;;; Log transformation of (= sum 0) to (true) based on the knowledge
;;; that expr = 0
;;; where sum represents the sum for expr,
;;;       node is the e-node for expr

(defun log-justify-kill-zero (node index)
  ;; Start with (= sum 0)
  (let ((sum (raw-expr-of-sum (sum-of-node node 0))))
    (push-proof-log 'if-equal index `(= ,sum ,(e-node-attribute node)) t)
    (push-proof-log 'look-up (cons 1 (if-left-index))
                    (e-node-attribute node))
    ;; (if (= sum expr) (= expr 0) (= sum 0))
    (log-node-equality node *zero-node* (cons 1 (if-left-index)))
    ;; (if (= sum expr) (= 0 0) (= sum 0))
    (push-proof-log 'compute (if-left-index))
    ;; (if (= sum expr) (true) (= sum 0))
    (log-collect-terms (e-node-attribute node) (cons 2 (if-test-index)))
    ;; (if (= sum sum) (true) (= sum 0))
    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)
    ;; (true)
    ))




;;; Log transformation of (= sum 0) to (true) based on detection that
;;; the triples for sum are all dead.

(defun log-justify-kill-constant-sum (owner triples index)
  ;; (= sum 0)
  (let ((c (lcm (apply #'lcm (mapcar #'(lambda (u) (denominator (car u)))
                                     triples))))
        (sum (sum-of-node (cdr owner) (car owner))))
    (unless (= c 1)
      (let ((expr (raw-expr-of-sum sum)))
        (log-multiply-=-zero c expr index)
        (log-push-multiplier-in c expr (cons 1 index))))
    (log-remove-dead-triples
     (multiply-collected-terms-by-constant sum c)
     (mapcar #'(lambda (u) (cons (* c (car u)) (cdr u))) triples)
     (cons 1 index))
    (push-proof-log 'compute index)))



;;; Log transformation of (= sum 0) to (true) based on the knowledge
;;; that (>= sum 0) and sum is maximized at 0.
;;; just1 is justification for restriction for sum
;;; just2 is justification for sum maximized at 0.

(defun log-justify-kill-anti-symmetric (node i just1 just2 index)
  (let ((sum (raw-expr-of-sum (sum-of-node node i))))
    (log-use-axiom-as-rewrite `(= ,sum 0) '>=.and.>=.negate.zero
			      `((= |)X| ,sum)) index)
    ;; (if (>= sum 0) (if (>= (negate sum) 0) (true) (= sum 0)) (= sum 0))
    (log-justify-restriction-aux just1 (if-test-index))
    (push-proof-log 'if-true index)
    ;; (if (>= (negate sum) 0) (true) (= sum 0))
    (let* ((triples (third just2))
           (lcm (apply #'lcm (mapcar #'(lambda (u) (denominator (car u)))
                                     triples))))
      (log-push-negate-into-sum sum (cons 1 (if-test-index)))
      ;; (if (>= -sum 0) (true) (= sum 0))
      (let ((nsum (raw-expr-of-sum (negative-sum (sum-of-node node i)))))
        (when (> lcm 1)
          (push-proof-log 'if-equal (if-test-index)
                          `(= (>= ,nsum 0) (>= (* ,lcm ,nsum) 0))
			  t)
          (push-proof-log 'look-up (cons 2 (if-test-index))
                          `(>= (* ,lcm ,nsum) 0))
          ;; (if (if (= (>= -sum 0) (>= (* lcm -sum) 0))
          ;;         (>= (* lcm -sum) 0)
          ;;         (>= -sum 0))
          ;;     (true)
          ;;     (= sum 0))
          (log-use-axiom-as-rewrite
           `(>= (* ,lcm ,nsum) 0) '*.>=.zero.>=.one.left
           `((= |)X| ,lcm) (= |)Y| ,nsum)) (list* 2 1 (if-test-index)))
          (push-proof-log 'compute (list* 1 2 1 (if-test-index)))
          (push-proof-log 'if-true (list* 2 1 (if-test-index)))
          ;; (if (if (= (>= -sum 0)
          ;;            (if (= (type-of -sum) (int))
          ;;                (>= -sum 0)
          ;;                (>= (* lcm -sum) 0)))
          ;;         (>= (* lcm -sum) 0)
          ;;         (>= -sum 0))
          ;;     (true)
          ;;     (= sum 0))
          (log-type-of-expr nsum (list* 1 1 2 1 (if-test-index)))
          (push-proof-log 'compute (list* 1 2 1 (if-test-index)))
          (push-proof-log 'if-true (list* 2 1 (if-test-index)))
          (push-proof-log 'compute (cons 1 (if-test-index)))
          (push-proof-log 'if-true (if-test-index))
          ;; (if (>= (* lcm -sum) 0) (true) (= sum 0))
          (log-push-multiplier-in lcm nsum (cons 1 (if-test-index)))
          ;; (if (>= ksum 0) (true) (= sum 0))
          )
        (log-justify-triples
         (cons (* (- lcm) (car (sum-of-node node i)))
               (mapcar #'(lambda (u) (cons (car u) (* (- lcm) (cdr u))))
                       (cdr (sum-of-node node i))))
         (mapcar #'(lambda (u) (cons (* (- lcm) (car u)) (cdr u)))
                 triples)
         (if-test-index))
        (push-proof-log 'if-true index)
        ;; (true)
        ))))



;;; Log transformation of (>= sum 0) to (true) based on restrictions in
;;; triples.

(defun log-justify-triples (sum triples index)
  (log-justify-triples-aux (convert-e-node-in-sum sum) triples index)
  )

(defun log-justify-triples-aux (sum triples index)
  (cond ((null triples)
         ;; (>= c 0)
         (push-proof-log 'compute index))
        (t (let ((coeff (first (car triples)))
                 (owner (second (car triples)))
                 (restriction (third (car triples))))
             (cond ((eq restriction 'dead)
                    (log-justify-triples-aux
                     (log-subtract-dead-sum
                      sum coeff owner (cons 1 index)) (cdr triples) index))
                   ((eq restriction 'restricted)
                    (let* ((sumc (convert-e-node-in-sum
                                  (sum-of-node (cdr owner) (car owner))))
                           (ksumc (cons (* coeff (car sumc))
                                        (mapcar #'(lambda (u)
                                                    (cons (car u)
                                                          (* coeff (cdr u))))
                                                (cdr sumc)))))
                      (let ((expr (raw-expr-of-sum sum))
                            (kexprc (raw-expr-of-sum ksumc)))
                        (push-proof-log
                         'if-equal index
			 `(= ,expr (+ ,kexprc (- ,expr ,kexprc)))
			 t)
                        (push-proof-log 'look-up (cons 1 (if-left-index))
                                        `(+ ,kexprc (- ,expr ,kexprc)))
                        ;; (if (= sum (+ ksumc (- sum ksumc)))
                        ;;     (>= (+ ksumc (- sum ksumc)) 0)
                        ;;     (>= sum 0))
                        (log-use-axiom-as-rewrite
                         `(>= (+ ,kexprc (- ,expr ,kexprc)) 0)
                         '+.>=.zero.>=.left.right
                         `((= |)X| ,kexprc) (= |)Y| (- ,expr ,kexprc)))
			 (if-left-index))
                        ;; (if (= sum (+ ksumc (- sum ksumc)))
                        ;;     (if (>= ksumc 0)
                        ;;         (if (>= (- sum ksumc) 0)
                        ;;             (true)
                        ;;             (>= (+ ksumc (- sum ksumc)) 0))
                        ;;         (>= (+ ksumc (- sum ksumc)) 0))
                        ;;     (>= sum 0))
                        (log-use-axiom-as-rewrite
                         `(+ ,kexprc (- ,expr ,kexprc)) '+.-.lemma
                         `((= |)X| ,kexprc) (= |)Y| ,expr))
			 (cons 2 (if-test-index)))
			(cond ((integerp expr)
			       (push-proof-log 'compute
					       (cons 2 (if-test-index))))
			      (t
			       (log-use-axiom-as-rewrite
				`(ord ,expr) 'ord.+
				`((= |)X| ,(second expr))
				  (= |)Y| ,(third expr)))
				(cons 2 (if-test-index)))))
                        (push-proof-log 'compute (if-test-index))
                        (push-proof-log 'if-true index)
                        ;; (if (>= ksumc 0)
                        ;;     (if (>= (- sum ksumc) 0)
                        ;;         (true)
                        ;;         (>= (+ ksumc (- sum ksumc)) 0))
                        ;;     (>= (+ ksumc (- sum ksumc)) 0))
                        (log-justify-multiply-restriction
                         coeff sumc ksumc owner
                         (if-test-index))
                        (push-proof-log 'if-true index)
                        ;; (if (>= (- sum ksumc) 0)
                        ;;     (true)
                        ;;     (>= (+ ksumc (- sum ksumc)) 0))
                        (log-convert-subtract-sum-to-add-sum
                         expr kexprc (cons 1 (if-test-index)))
                        (log-justify-triples-aux
                         (log-add-collected-terms
                          sum (negative-sum ksumc) (cons 1 (if-test-index)))
                         (cdr triples) (if-test-index))
                        ;; (if (true) (true) (>= (+ ksumc (- sum ksumc)) 0))
                        (push-proof-log 'if-true index)
                        )))
                   (t ; skip constant
                    (log-justify-triples-aux sum (cdr triples) index))))))
  )



;;; Log transformation of (- expr1 expr2) to (+ expr1 -expr2)
;;; where expr1 and expr2 are sums.

(defun log-convert-subtract-sum-to-add-sum (expr1 expr2 index)
  (log-use-axiom-as-rewrite
   `(- ,expr1 ,expr2) '-.times.minus.1.right
   `((= |)X| ,expr1) (= |)Y| ,expr2)) index)
  ;; (+ expr1 (* -1 expr2))
  (log-push-multiplier-in -1 expr2 (cons 2 index))
  ;; (+ expr1 -expr2)
  )

;;; Log transformation of (>= ksum 0) to (true) based on (>= sum 0),
;;; where k > 0

(defun log-justify-multiply-restriction (k sum ksum owner index)
  (log-factor-out k ksum (cons 1 index))
  ;; (>= (* k sum) 0)
  (log-justify-multiply-restriction-aux k sum owner index)
  )

(defun log-justify-multiply-restriction-aux (k sum owner index)
  (let ((expr (raw-expr-of-sum sum)))
    ;; (>= (* k sum) 0)
    (log-add-zero `(* ,k ,expr) (cons 1 index))
    ;; (>= (+ 0 (* k sum)) 0)
    (log-use-axiom-as-rewrite
     `(>= (+ 0 (* ,k ,expr)) 0) 'normalize.>=
     `((= |)X| 0) (= |)Y| ,k) (= |)Z| ,expr)) index)
    ;; (if (>= 0 0)
    ;;     (if (>= k (+ 0 1))
    ;;         (if (= (type-of sum) (int))
    ;;             (>= sum 0)
    ;;             (>= (+ 0 (* k sum)) 0))
    ;;         (>= (+ 0 (* k sum)) 0))
    ;;     (>= (+ 0 (* k sum)) 0))
    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)
    ;; (if (>= k (+ 0 1))
    ;;     (if (= (type-of sum) (int)) (>= sum 0) (>= (+ 0 (* k sum)) 0))
    ;;     (>= (+ 0 (* k sum)) 0))
    (push-proof-log 'compute (cons 2 (if-test-index)))
    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)
    ;; (if (= (type-of sum) (int)) (>= sum 0) (>= (+ 0 (* k sum)) 0))
    (log-type-of-expr expr (cons 1 (if-test-index)))
    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)
    ;; (>= sum 0)
    (log-justify-restriction (cdr owner) (car owner) index)))



;;; Log transformation of (= sumc 0) based on the fact that sumc was
;;; restricted and it was represented as one of the columns involved
;;; in the detection of maximization of row at 0.
;;; owner1 is the owner of the row involved.
;;; owner2 is the owner of the column.
;;; triples is the snapshot of the row entry.

(defun log-justify-kill-minimized-col (owner1 owner2 triples index)
  (let ((lcm (apply #'lcm (mapcar #'(lambda (u) (denominator (car u)))
                                  triples)))
        (sumr (convert-e-node-in-sum (sum-of-node (cdr owner1) (car owner1))))
        (sumc (convert-e-node-in-sum (sum-of-node (cdr owner2) (car owner2))))
        (coeff (car (find-triple owner2 triples))))
    (let ((nksumr (multiply-collected-terms-by-constant sumr (- lcm)))
          (msumc (multiply-collected-terms-by-constant sumc (* (- lcm) coeff)))
          (exprc (raw-expr-of-sum sumc)))
      ;; Start with (= sumc 0)
      (log-multiply-=-zero (* (- lcm) coeff) exprc index)
      ;; (= (* m sumc) 0)
      (let* ((rest (add-collected-terms nksumr (negative-sum msumc)))
             (restexpr (raw-expr-of-sum rest))
             (m (* (- lcm) coeff)))
        (log-use-axiom-as-rewrite
         `(= (* ,m ,exprc) 0) 'minimized.col.lemma
         `((= |)X| (* ,m ,exprc)) (= |)Y| ,restexpr)) index)
        ;; (if (>= (* m sumc) 0)
        ;;     (if (>= rest 0)
        ;;         (if (= (+ (* m sumc) rest) 0) (true) (= (* m sumc) 0))
        ;;         (= (* m sumc) 0))
        ;;     (= (* m sumc) 0))
        (log-justify-multiply-restriction-aux m sumc owner2 (if-test-index))
        (push-proof-log 'if-true index)
        (log-justify-triples
         rest
         (mapcar #'(lambda (u) (cons (* (- lcm) (car u)) (cdr u)))
                 (remove-if #'(lambda (u) (equal (second u) owner2)) triples))
         (if-test-index))
        (push-proof-log 'if-true index)
        ;; (if (= (+ (* m sumc) rest) 0) (true) (= (* m sumc) 0))
        (log-multiply-collected-terms-by-constant
         sumc m (list* 1 1 (if-test-index)))
        (log-add-collected-terms msumc rest (cons 1 (if-test-index)))
        ;; (if (= nksumr 0) (true) (= (* m sumc) 0))
        (log-factor-out (- lcm) nksumr (cons 1 (if-test-index)))
        ;; (if (= (* -lcm sumr) 0) (true) (= (* m sumc) 0))
        (log-factor-out-=-zero (- lcm) (raw-expr-of-sum sumr) (if-test-index))
        ;; (if (= sumr 0) (true) (= (* m sumc) 0))
        (log-justify-killed (cdr owner1) (car owner1) (if-test-index))
        (push-proof-log 'if-true index)
        ;; (true)
        ))))

(defun find-triple (owner triples)
  (loop for triple in triples
        when (equal owner (second triple))
        return triple))



;;; Log transformation of (= expr 0) to (= (* k expr) 0) where k is non-zero.

(defun log-multiply-=-zero (k expr index)
  ;; (= expr 0)
  (push-proof-log 'if-equal index `(= (= ,expr 0) (= (* ,k ,expr) (* ,k 0))) t)
  (push-proof-log 'look-up (if-left-index) `(= (* ,k ,expr) (* ,k 0)))
  (push-proof-log 'compute (cons 2 (if-left-index)))
  ;; (if (= (= expr 0) (= (* k expr) (* k 0))) (= (* k expr) 0) (= expr 0))
  (log-remove-common-multiplier k expr 0 (cons 2 (if-test-index)))
  ;; (if (= (= expr 0) (= expr 0)) (= (* k expr) 0) (= expr 0))
  (push-proof-log 'compute (if-test-index))
  (push-proof-log 'if-true index)
  ;; (= (* k expr) 0)
  )

;;; Log transformation of (>= expr 0) to (>= (* k expr) 0) where k > 0.

(defun log-multiply->=-zero (k expr index)
  ;; (>= expr 0)
  (push-proof-log 'if-equal index `(= (>= ,expr 0) (>= (* ,k ,expr) 0)) t)
  (push-proof-log 'look-up (if-left-index) `(>= (* ,k ,expr) 0))
  ;; (if (= (>= expr 0) (>= (* k expr) 0)) (>= (* k expr) 0) (>= expr 0))
  (log-use-axiom-as-rewrite
   `(>= (* ,k ,expr) 0) '*.>=.zero.>=.one.left `((= |)X| ,k) (= |)Y| ,expr))
   (cons 2 (if-test-index)))
  ;; (if (= (>= expr 0)
  ;;        (if (>= k 1)
  ;;            (if (= (type-of expr) (int)) (>= expr 0) (>= (* k expr) 0))
  ;;            (>= (* k expr) 0)))
  ;;     (>= (* k expr) 0)
  ;;     (>= expr 0))
  (push-proof-log 'compute (list* 1 2 (if-test-index)))
  (push-proof-log 'if-true (cons 2 (if-test-index)))
  (log-type-of-expr expr (list* 1 1 2 (if-test-index)))
  (push-proof-log 'compute (list* 1 2 (if-test-index)))
  (push-proof-log 'if-true (cons 2 (if-test-index)))
  ;; (if (= (>= expr 0) (>= expr 0)) (>= (* k expr) 0) (>= expr 0))
  (push-proof-log 'compute (if-test-index))
  (push-proof-log 'if-true index)
  ;; (>= (* k expr) 0)
  )

;;; Log transformation of (= (* k expr) 0) to (= expr 0) where k is non-zero.

(defun log-factor-out-=-zero (k expr index)
  ;; (= (* k expr) 0)
  (push-proof-log 'if-equal (cons 2 index) `(= 0 (* ,k 0)) t)
  (push-proof-log 'look-up (list* 2 2 index) `(* ,k 0))
  ;; (= (* k expr) (if (= 0 (* k 0)) (* k 0) 0))
  (push-proof-log 'compute (list* 2 1 2 index))
  (push-proof-log 'compute (list* 1 2 index))
  (push-proof-log `if-true (cons 2 index))
  ;; (= (* k expr) (* k 0))
  (log-remove-common-multiplier k expr 0 index)
  ;; (= expr 0)
  )



;;; Log transformation of (>= expr 0) to (true) based on the fact
;;; that the node for expr is in the same equivalence class as the
;;; node for ref, and the 0th tableau entry for ref is restricted.

(defun log-justify-ge (node ref index)
  ;; (>= expr 0)
  (log-node-equality node ref (cons 1 index))
  (log-collect-terms (e-node-attribute ref) (cons 1 index))
  ;; (>= sum0 0)
  (log-justify-restriction ref 0 index))

;;; Log transformation of (>= (negate expr) 0) to (true) based on the
;;; fact that the node for expr is in the same equivalence class as the
;;; node for ref, and the 1st tableau entry for ref is restricted.

(defun log-justify-le (node ref index)
  ;; (>= (negate expr) 0)
  (log-node-equality node ref (list* 1 1 index))
  (log-collect-terms `(negate ,(e-node-attribute ref)) (cons 1 index))
  ;; (>= sum1 0)
  (log-justify-restriction ref 1 index))

;;; Log transformation of (>= (- expr 1) 0) to (true) based on the fact
;;; that the node for expr is in the same equivalence class as the
;;; node for ref, and the 2nd tableau entry for ref is restricted.

(defun log-justify-gt (node ref index)
  ;; (>= (- expr 1) 0)
  (log-node-equality node ref (list* 1 1 index))
  (log-collect-terms `(- ,(e-node-attribute ref) 1) (cons 1 index))
  ;; (>= sum2 0)
  (log-justify-restriction ref 2 index))

;;; Log transformation of (>= (- (negate expr) 1) 0) to (true) based on
;;; the fact that the node for expr is in the same equivalence class as
;;; the node for ref, and the 3rd tableau entry for ref is restricted.

(defun log-justify-lt (node ref index)
  ;; (>= (- (negate expr) 1) 0)
  (log-node-equality node ref (list* 1 1 1 index))
  (log-collect-terms `(- (negate ,(e-node-attribute ref)) 1) (cons 1 index))
  ;; (>= sum3 0)
  (log-justify-restriction ref 3 index))



;;; Code to log non-linear arithmetic inferences.

;;; Log transformation of (>= sum 0) to (true) based on the fact that
;;; sum is a sum entry for prod,
;;; left and right are restricted,
;;; left is equivalent to the first argument of prod,
;;; and right is equivalent to the second argument of prod.

(defun log-justify-*-up (i1 i2 prod left right index)
  ;; (>= sum 0)
  (let ((pexpr (e-node-attribute prod))
	(sexpr0 (raw-expr-of-sum (sum-of-node prod 0))))
    (cond ((= i1 0)
	   (cond ((= i2 0)
		  (push-proof-log 'if-equal index `(= ,sexpr0 ,pexpr) t)
		  (push-proof-log 'look-up (cons 1 (if-left-index))
				  pexpr)
		  ;; (if (= sum0 (* l r)) (>= (* l r) 0) (>= sum0 0))
		  (log-collect-terms pexpr (cons 2 (if-test-index)))
		  (push-proof-log 'compute (if-test-index))
		  (push-proof-log 'if-true index)
		  ;; (>= (* l r) 0)
		  (log-use-axiom-as-rewrite
		   `(>= ,pexpr 0) '*.up.1
		   `((= |)X| ,(second pexpr)) (= |)Y| ,(third pexpr)))
		   index)
		  ;; (if (>= l 0)
		  ;;     (if (>= r 0) (true) (>= (* l r) 0))
		  ;;     (>= (* l r) 0))
                  (log-justify-ge (arg-1-node prod) left (if-test-index))
                  (push-proof-log 'if-true index)
		  ;; (if (>= r 0) (true) (>= (* l r) 0))
                  (log-justify-ge (arg-2-node prod) right (if-test-index))
                  (push-proof-log 'if-true index))
		 ((= i2 1)
		  (let ((sexpr1 (raw-expr-of-sum (sum-of-node prod 1))))
		    (push-proof-log
		     'if-equal index `(= ,sexpr1 (negate ,pexpr)) t)
		    (push-proof-log 'look-up (cons 1 (if-left-index))
				    `(negate ,pexpr))
		    ;; (if (= sum1 (negate (* l r)))
		    ;;     (>= (negate (* l r)) 0)
		    ;;     (>= sum1 0))
		    (log-collect-terms `(negate ,pexpr)
                                       (cons 2 (if-test-index)))
		    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (negate (* l r)) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (negate ,pexpr) 0) '*.up.2
                     `((= |)X| ,(second pexpr)) (= |)Y| ,(third pexpr))) index)
                    ;; (if (>= l 0)
                    ;;     (if (>= (negate r) 0)
		    ;;         (true)
		    ;;         (>= (negate (* l r)) 0))
                    ;;     (>= (negate (* l r)) 0))
                    (log-justify-ge (arg-1-node prod) left (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (if (>= (negate r) 0) (true) (>= (negate (* l r)) 0))
                    (log-justify-le (arg-2-node prod) right (if-test-index))
                    (push-proof-log 'if-true index)))
                 ((= i2 2)
		  (push-proof-log 'if-equal index `(= ,sexpr0 ,pexpr) t)
		  (push-proof-log 'look-up (cons 1 (if-left-index))
				  pexpr)
		  ;; (if (= sum0 (* l r)) (>= (* l r) 0) (>= sum0 0))
		  (log-collect-terms pexpr (cons 2 (if-test-index)))
		  (push-proof-log 'compute (if-test-index))
		  (push-proof-log 'if-true index)
		  ;; (>= (* l r) 0)
		  (log-use-axiom-as-rewrite
		   `(>= ,pexpr 0) '*.up.3
		   `((= |)X| ,(second pexpr)) (= |)Y| ,(third pexpr)))
		   index)
		  ;; (if (>= l 0)
		  ;;     (if (>= (- r 1) 0) (true) (>= (* l r) 0))
		  ;;     (>= (* l r) 0))
                  (log-justify-ge (arg-1-node prod) left (if-test-index))
                  (push-proof-log 'if-true index)
		  ;; (if (>= (- r 1) 0) (true) (>= (* l r) 0))
                  (log-justify-gt (arg-2-node prod) right (if-test-index))
                  (push-proof-log 'if-true index))
		 ((= i2 3)
		  (let ((sexpr1 (raw-expr-of-sum (sum-of-node prod 1))))
		    (push-proof-log
		     'if-equal index `(= ,sexpr1 (negate ,pexpr)) t)
		    (push-proof-log 'look-up (cons 1 (if-left-index))
				    `(negate ,pexpr))
		    ;; (if (= sum1 (negate (* l r)))
		    ;;     (>= (negate (* l r)) 0)
		    ;;     (>= sum1 0))
		    (log-collect-terms `(negate ,pexpr)
                                       (cons 2 (if-test-index)))
		    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (negate (* l r)) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (negate ,pexpr) 0) '*.up.4
                     `((= |)X| ,(second pexpr)) (= |)Y| ,(third pexpr))) index)
                    ;; (if (>= l 0)
                    ;;     (if (>= (- (negate r) 1) 0)
		    ;;         (true)
		    ;;         (>= (negate (* l r)) 0))
                    ;;     (>= (negate (* l r)) 0))
                    (log-justify-ge (arg-1-node prod) left (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (if (>= (- (negate r) 1) 0) (true) (>= (* l r) 0))
                    (log-justify-lt (arg-2-node prod) right (if-test-index))
                    (push-proof-log 'if-true index)))))
          ((= i1 1)
           (cond ((= i2 0)
		  (let ((sexpr1 (raw-expr-of-sum (sum-of-node prod 1))))
		    (push-proof-log
		     'if-equal index `(= ,sexpr1 (negate ,pexpr)) t)
		    (push-proof-log 'look-up (cons 1 (if-left-index))
				    `(negate ,pexpr))
		    ;; (if (= sum1 (negate (* l r)))
		    ;;     (>= (negate (* l r)) 0)
		    ;;     (>= sum1 0))
		    (log-collect-terms `(negate ,pexpr)
                                       (cons 2 (if-test-index)))
		    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (negate (* l r)) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (negate ,pexpr) 0) '*.up.5
                     `((= |)X| ,(second pexpr)) (= |)Y| ,(third pexpr))) index)
                    ;; (if (>= (negate l) 0)
                    ;;     (if (>= r 0)
		    ;;         (true)
		    ;;         (>= (negate (* l r)) 0))
                    ;;     (>= (negate (* l r)) 0))
                    (log-justify-le (arg-1-node prod) left (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (if (>= r 0) (true) (>= (negate (* l r)) 0))
                    (log-justify-ge (arg-2-node prod) right (if-test-index))
                    (push-proof-log 'if-true index)))
                 ((= i2 1)
		  (push-proof-log 'if-equal index `(= ,sexpr0 ,pexpr) t)
		  (push-proof-log 'look-up (cons 1 (if-left-index))
				  pexpr)
		  ;; (if (= sum0 (* l r)) (>= (* l r) 0) (>= sum0 0))
		  (log-collect-terms pexpr (cons 2 (if-test-index)))
		  (push-proof-log 'compute (if-test-index))
		  (push-proof-log 'if-true index)
		  ;; (>= (* l r) 0)
		  (log-use-axiom-as-rewrite
		   `(>= ,pexpr 0) '*.up.6
		   `((= |)X| ,(second pexpr)) (= |)Y| ,(third pexpr))) index)
		  ;; (if (>= (negate l) 0)
		  ;;     (if (>= (negate r) 0) (true) (>= (* l r) 0))
		  ;;     (>= (* l r) 0))
                  (log-justify-le (arg-1-node prod) left (if-test-index))
                  (push-proof-log 'if-true index)
		  ;; (if (>= (negate r) 0) (true) (>= (* l r) 0))
                  (log-justify-le (arg-2-node prod) right (if-test-index))
                  (push-proof-log 'if-true index))
                 ((= i2 2)
		  (let ((sexpr1 (raw-expr-of-sum (sum-of-node prod 1))))
		    (push-proof-log
		     'if-equal index `(= ,sexpr1 (negate ,pexpr)) t)
		    (push-proof-log 'look-up (cons 1 (if-left-index))
				    `(negate ,pexpr))
		    ;; (if (= sum1 (negate (* l r)))
		    ;;     (>= (negate (* l r)) 0)
		    ;;     (>= sum1 0))
		    (log-collect-terms `(negate ,pexpr)
                                       (cons 2 (if-test-index)))
		    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (negate (* l r)) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (negate ,pexpr) 0) '*.up.7
                     `((= |)X| ,(second pexpr)) (= |)Y| ,(third pexpr))) index)
                    ;; (if (>= (negate l) 0)
                    ;;     (if (>= (- r 1) 0)
		    ;;         (true)
		    ;;         (>= (negate (* l r)) 0))
                    ;;     (>= (negate (* l r)) 0))
                    (log-justify-le (arg-1-node prod) left (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (if (>= (- r 1) 0) (true) (>= (negate (* l r)) 0))
                    (log-justify-gt (arg-2-node prod) right (if-test-index))
                    (push-proof-log 'if-true index)))
                 ((= i2 3)
		  (push-proof-log 'if-equal index `(= ,sexpr0 ,pexpr) t)
		  (push-proof-log 'look-up (cons 1 (if-left-index))
				  pexpr)
		  ;; (if (= sum0 (* l r)) (>= (* l r) 0) (>= sum0 0))
		  (log-collect-terms pexpr (cons 2 (if-test-index)))
		  (push-proof-log 'compute (if-test-index))
		  (push-proof-log 'if-true index)
		  ;; (>= (* l r) 0)
		  (log-use-axiom-as-rewrite
		   `(>= ,pexpr 0) '*.up.8
		   `((= |)X| ,(second pexpr)) (= |)Y| ,(third pexpr))) index)
		  ;; (if (>= (negate l) 0)
		  ;;     (if (>= (- (negate r) 1) 0) (true) (>= (* l r) 0))
		  ;;     (>= (* l r) 0))
                  (log-justify-le (arg-1-node prod) left (if-test-index))
                  (push-proof-log 'if-true index)
		  ;; (if (>= (- (negate right) 1) 0) (true) (>= (* l r) 0))
                  (log-justify-lt (arg-2-node prod) right (if-test-index))
                  (push-proof-log 'if-true index))))
          ((= i1 2)
           (cond ((= i2 0)
		  (push-proof-log 'if-equal index `(= ,sexpr0 ,pexpr) t)
		  (push-proof-log 'look-up (cons 1 (if-left-index))
				  pexpr)
		  ;; (if (= sum0 (* l r)) (>= (* l r) 0) (>= sum0 0))
		  (log-collect-terms pexpr (cons 2 (if-test-index)))
		  (push-proof-log 'compute (if-test-index))
		  (push-proof-log 'if-true index)
		  ;; (>= (* l r) 0)
		  (log-use-axiom-as-rewrite
		   `(>= ,pexpr 0) '*.up.9
		   `((= |)X| ,(second pexpr)) (= |)Y| ,(third pexpr))) index)
		  ;; (if (>= (- l 1) 0)
		  ;;     (if (>= r 0) (true) (>= (* l r) 0))
		  ;;     (>= (* l r) 0))
                  (log-justify-gt (arg-1-node prod) left (if-test-index))
                  (push-proof-log 'if-true index)
		  ;; (if (>= r 0) (true) (>= (* l r) 0))
                  (log-justify-ge (arg-2-node prod) right (if-test-index))
                  (push-proof-log 'if-true index))
                 ((= i2 1)
                  (let ((sexpr1 (raw-expr-of-sum (sum-of-node prod 1))))
                    (push-proof-log
		     'if-equal index `(= ,sexpr1 (negate ,pexpr)) t)
                    (push-proof-log 'look-up (cons 1 (if-left-index))
                                    `(negate ,pexpr))
                    ;; (if (= sum1 (negate (* l r)))
                    ;;     (>= (negate (* l r)) 0)
                    ;;     (>= sum1 0))
                    (log-collect-terms `(negate ,pexpr)
                                       (cons 2 (if-test-index)))
                    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (negate (* l r)) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (negate ,pexpr) 0) '*.up.10
                     `((= |)X| ,(second pexpr)) (= |)Y| ,(third pexpr))) index)
                    ;; (if (>= (- l 1) 0)
                    ;;     (if (>= (negate r) 0)
                    ;;         (true)
                    ;;         (>= (negate (* l r)) 0))
                    ;;     (>= (* l r) 0))
                    (log-justify-gt (arg-1-node prod) left (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (if (>= (negate r) 0) (true) (>= (negate (* l r)) 0))
                    (log-justify-le (arg-2-node prod) right (if-test-index))
                    (push-proof-log 'if-true index)))
                 ((= i2 2)
		  (let ((sexpr2 (raw-expr-of-sum (sum-of-node prod 2))))
		    (push-proof-log 'if-equal index `(= ,sexpr2 (- ,pexpr 1)) t)
		    (push-proof-log 'look-up (cons 1 (if-left-index))
				    `(- ,pexpr 1))
		    ;; (if (= sum1 (- (* l r) 1))
		    ;;     (>= (- (* l r) 1) 0)
		    ;;     (>= sum2 0))
		    (log-collect-terms `(- ,pexpr 1)
                                       (cons 2 (if-test-index)))
		    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (- (* l r) 1) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (- ,pexpr 1) 0) '*.up.11
                     `((= |)X| ,(second pexpr)) (= |)Y| ,(third pexpr))) index)
                    ;; (if (>= (- l 1) 0)
                    ;;     (if (>= (- r 1) 0) (true) (>= (- (* l r) 1) 0))
                    ;;     (>= (- (* l r) 1) 0))
                    (log-justify-gt (arg-1-node prod) left (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (if (>= (- r 1) 0) (true) (>= (- (* l r) 1) 0))
                    (log-justify-gt (arg-2-node prod) right (if-test-index))
                    (push-proof-log 'if-true index)))
                 ((= i2 3)
		  (let ((sexpr3 (raw-expr-of-sum (sum-of-node prod 3))))
		    (push-proof-log 'if-equal index
                                    `(= ,sexpr3 (- (negate ,pexpr) 1))
				    t)
		    (push-proof-log 'look-up (cons 1 (if-left-index))
				    `(- (negate ,pexpr) 1))
		    ;; (if (= sum3 (- (negate (* l r)) 1))
		    ;;     (>= (- (negate (* l r)) 1) 0)
		    ;;     (>= sum3 0))
		    (log-collect-terms `(- (negate ,pexpr) 1)
                                       (cons 2 (if-test-index)))
		    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (- (negate (* l r)) 1) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (- (negate ,pexpr) 1) 0) '*.up.12
                     `((= |)X| ,(second pexpr)) (= |)Y| ,(third pexpr))) index)
                    ;; (if (>= (- l 1) 0)
                    ;;     (if (>= (- (negate r) 1) 0)
                    ;;         (true)
                    ;;         (>= (- (negate (* l r)) 1) 0))
                    ;;     (>= (- (negate (* l r)) 1) 0))
                    (log-justify-gt (arg-1-node prod) left (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (if (>= (- (negate r) 1) 0) (true) (>= (- (* l r) 1) 0))
                    (log-justify-lt (arg-2-node prod) right (if-test-index))
                    (push-proof-log 'if-true index)))))
          ((= i1 3)
           (cond ((= i2 0)
                  (let ((sexpr1 (raw-expr-of-sum (sum-of-node prod 1))))
                    (push-proof-log
		     'if-equal index `(= ,sexpr1 (negate ,pexpr)) t)
                    (push-proof-log 'look-up (cons 1 (if-left-index))
                                    `(negate ,pexpr))
                    ;; (if (= sum1 (negate (* l r)))
                    ;;     (>= (negate (* l r)) 0)
                    ;;     (>= sum1 0))
                    (log-collect-terms `(negate ,pexpr)
                                       (cons 2 (if-test-index)))
                    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (negate (* l r)) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (negate ,pexpr) 0) '*.up.13
                     `((= |)X| ,(second pexpr)) (= |)Y| ,(third pexpr))) index)
                    ;; (if (>= (- (negate l) 1) 0)
                    ;;     (if (>= r 0) (true) (>= (negate (* l r)) 0))
                    ;;     (>= (negate (* l r)) 0))
                    (log-justify-lt (arg-1-node prod) left (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (if (>= r 0) (true) (>= (negate (* l r)) 0))
                    (log-justify-ge (arg-2-node prod) right (if-test-index))
                    (push-proof-log 'if-true index)))
                 ((= i2 1)
		  (push-proof-log 'if-equal index `(= ,sexpr0 ,pexpr) t)
		  (push-proof-log 'look-up (cons 1 (if-left-index))
				  pexpr)
		  ;; (if (= sum0 (* l r)) (>= (* l r) 0) (>= sum 0))
		  (log-collect-terms pexpr (cons 2 (if-test-index)))
		  (push-proof-log 'compute (if-test-index))
		  (push-proof-log 'if-true index)
		  ;; (>= (* l r) 0)
		  (log-use-axiom-as-rewrite
		   `(>= ,pexpr 0) '*.up.14
		   `((= |)X| ,(second pexpr)) (= |)Y| ,(third pexpr))) index)
		  ;; (if (>= (- (negate l) 1) 0)
		  ;;     (if (>= (negate r) 0) (true) (>= (* l r) 0))
		  ;;     (>= (* l r) 0))
                  (log-justify-lt (arg-1-node prod) left (if-test-index))
                  (push-proof-log 'if-true index)
                  ;; (if (>= (negate r) 0) (true) (>= (* l r) 0))
                  (log-justify-le (arg-2-node prod) right (if-test-index))
                  (push-proof-log 'if-true index))
                 ((= i2 2)
		  (let ((sexpr3 (raw-expr-of-sum (sum-of-node prod 3))))
		    (push-proof-log 'if-equal index
                                    `(= ,sexpr3 (- (negate ,pexpr) 1))
				    t)
		    (push-proof-log 'look-up (cons 1 (if-left-index))
				    `(- (negate ,pexpr) 1))
		    ;; (if (= sum3 (- (negate (* l r)) 1))
		    ;;     (>= (- (negate (* l r)) 1) 0)
		    ;;     (>= sum3 0))
		    (log-collect-terms `(- (negate ,pexpr) 1)
                                       (cons 2 (if-test-index)))
		    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (- (negate (* l r)) 1) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (- ,pexpr 1) 0) '*.up.15
                     `((= |)X| ,(second pexpr)) (= |)Y| ,(third pexpr))) index)
                    ;; (if (>= (- (negate l) 1) 0)
                    ;;     (if (>= (- r 1) 0)
                    ;;         (true)
                    ;;         (>= (- (negate (* l r)) 1) 0))
                    ;;     (>= (- (negate (* l r)) 1) 0))
                    (log-justify-lt (arg-1-node prod) left (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (if (>= (- r 1) 0) (true) (>= (- (negate (* l r)) 1) 0))
                    (log-justify-gt (arg-2-node prod) right (if-test-index))
                    (push-proof-log 'if-true index)))
                 ((= i2 3)
		  (let ((sexpr2 (raw-expr-of-sum (sum-of-node prod 2))))
		    (push-proof-log 'if-equal index `(= ,sexpr2 (- ,pexpr 1)) t)
		    (push-proof-log 'look-up (cons 1 (if-left-index))
				    `(- ,pexpr 1))
		    ;; (if (= sum2 (- (* l r) 1))
                    ;;     (>= (- (* l r) 1) 0)
                    ;;     (>= sum2 0))
		    (log-collect-terms `(- ,pexpr 1) (cons 2 (if-test-index)))
		    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (- (* l r) 1) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (- ,pexpr 1) 0) '*.up.16
                     `((= |)X| ,(second pexpr)) (= |)Y| ,(third pexpr))) index)
                    ;; (if (>= (- (negate l) 1) 0)
                    ;;     (if (>= (- (negate r) 1) 0)
                    ;;         (true)
                    ;;         (>= (- (* l r) 1) 0))
                    ;;     (>= (- (* l r) 1) 0))
                    (log-justify-lt (arg-1-node prod) left (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (if (>= (- (negate r) 1) 0) (true) (>= (- (* l r) 1) 0))
                    (log-justify-lt (arg-2-node prod) right (if-test-index))
                    (push-proof-log 'if-true index))))))))



;;; Log transformation of (>= sum 0) to (true) based on the fact
;;; that a product and its right argument are (indirectly) restricted,
;;; and sum is the (indirect) sum of the left argument.

(defun log-justify-*-l (i1 i2 ref prod left right index)
  (let ((pexpr (e-node-attribute prod))
        (lexpr (e-node-attribute left)))
    (cond ((= i1 0)
           (cond ((= i2 2)
                  (let ((sum (raw-expr-of-sum (sum-of-node left 0))))
                    (push-proof-log 'if-equal index `(= ,sum (ord ,lexpr)) t)
                    (push-proof-log 'look-up (cons 1 (if-left-index))
                                    `(ord ,lexpr))
                    ;; (if (= sum (ord left)) (>= (ord left) 0) (>= sum 0))
                    (log-collect-terms `(ord ,lexpr) (cons 2 (if-test-index)))
                    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (ord left) 0)
                    (log-node-equality
                     left (arg-1-node prod) (list* 1 1 index))
                    ;; (>= (ord l) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (ord ,(second pexpr)) 0) '*.l.1
                     `((= |)X| ,(second pexpr)) (= |)Y| ,(third pexpr))) index)
                    ;; (if (>= (* l r) 0)
                    ;;     (if (>= (- r 1) 0) (true) (>= (ord l) 0))
                    ;;     (>= (ord l) 0))
                    (log-justify-ge prod ref (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (if (>= (- r 1) 0) (true) (>= (ord l) 0))
                    (log-justify-gt (arg-2-node prod) right (if-test-index))
                    (push-proof-log 'if-true index)))
                 ((= i2 3)
                  (let ((sum (raw-expr-of-sum (sum-of-node left 1))))
                    (push-proof-log 'if-equal index `(= ,sum (negate ,lexpr)) t)
                    (push-proof-log 'look-up (cons 1 (if-left-index))
                                    `(negate ,lexpr))
                    ;; (if (= sum (negate left))
                    ;;     (>= (negate left) 0)
                    ;;     (>= sum 0))
                    (log-collect-terms `(negate ,lexpr)
                                       (cons 2 (if-test-index)))
                    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (negate left) 0)
                    (log-node-equality
                     left (arg-1-node prod) (list* 1 1 index))
                    ;; (>= (negate l) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (negate ,(second pexpr)) 0) '*.l.2
                     `((= |)X| ,(second pexpr)) (= |)Y| ,(third pexpr))) index)
                    ;; (if (>= (* l r) 0)
                    ;;     (if (>= (- (negate r) 1) 0)
                    ;;         (true)
                    ;;         (>= (negate l) 0))
                    ;;     (>= (negate l) 0))
                    (log-justify-ge prod ref (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (if (>= (- (negate r) 1) 0) (true) (>= (negate l) 0))
                    (log-justify-lt (arg-2-node prod) right (if-test-index))
                    (push-proof-log 'if-true index)))))
          ((= i1 1)
           (cond ((= i2 2)
                  (let ((sum (raw-expr-of-sum (sum-of-node left 1))))
                    (push-proof-log 'if-equal index `(= ,sum (negate ,lexpr)) t)
                    (push-proof-log 'look-up (cons 1 (if-left-index))
                                    `(negate ,lexpr))
                    ;; (if (= sum (negate left))
                    ;;     (>= (negate left) 0)
                    ;;     (>= sum 0))
                    (log-collect-terms `(negate ,lexpr)
                                       (cons 2 (if-test-index)))
                    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (negate left) 0)
                    (log-node-equality
                     left (arg-1-node prod) (list* 1 1 index))
                    ;; (>= (negate l) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (negate ,(second pexpr)) 0) '*.l.3
                     `((= |)X| ,(second pexpr)) (= |)Y| ,(third pexpr))) index)
                    ;; (if (>= (negate (* l r)) 0)
                    ;;     (if (>= (- r 1) 0) (true) (>= (negate l) 0))
                    ;;     (>= (negate l) 0))
                    (log-justify-le prod ref (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (if (>= (- (negate r) 1) 0) (true) (>= (negate l) 0))
                    (log-justify-gt (arg-2-node prod) right (if-test-index))
                    (push-proof-log 'if-true index)))
                 ((= i2 3)
                  (let ((sum (raw-expr-of-sum (sum-of-node left 0))))
                    (push-proof-log 'if-equal index `(= ,sum (ord ,lexpr)) t)
                    (push-proof-log 'look-up (cons 1 (if-left-index))
                                    `(ord ,lexpr))
                    ;; (if (= sum (ord left)) (>= (ord left) 0) (>= sum 0))
                    (log-collect-terms `(ord ,lexpr) (cons 2 (if-test-index)))
                    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (ord left) 0)
                    (log-node-equality
                     left (arg-1-node prod) (list* 1 1 index))
                    ;; (>= (ord l) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (ord ,(second pexpr)) 0) '*.l.4
                     `((= |)X| ,(second pexpr)) (= |)Y| ,(third pexpr))) index)
                    ;; (if (>= (negate (* l r)) 0)
                    ;;     (if (>= (- (negate r) 1) 0) (true) (>= (ord l) 0))
                    ;;     (>= (ord l) 0))
                    (log-justify-le prod ref (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (if (>= (- (negate r) 1) 0) (true) (>= (ord l) 0))
                    (log-justify-lt (arg-2-node prod) right (if-test-index))
                    (push-proof-log 'if-true index)))))
          ((= i1 2)
           (cond ((= i2 0)
                  (let ((sum (raw-expr-of-sum (sum-of-node left 2))))
                    (push-proof-log 'if-equal index `(= ,sum (- ,lexpr 1)) t)
                    (push-proof-log 'look-up (cons 1 (if-left-index))
                                    `(- ,lexpr 1))
                    ;; (if (= sum (- left 1)) (>= (- left 1) 0) (>= sum 0))
                    (log-collect-terms `(- ,lexpr 1) (cons 2 (if-test-index)))
                    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (- left 1) 0)
                    (log-node-equality
                     left (arg-1-node prod) (list* 1 1 index))
                    ;; (>= (- l 1) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (- ,(second pexpr) 1) 0) '*.l.5
                     `((= |)X| ,(second pexpr)) (= |)Y| ,(third pexpr))) index)
                    ;; (if (>= (- (* l r) 1) 0)
                    ;;     (if (>= r 0) (true) (>= (- l 1) 0))
                    ;;     (>= (- l 1) 0))
                    (log-justify-gt prod ref (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (if (>= r 0) (true) (>= (- l 1) 0))
                    (log-justify-ge (arg-2-node prod) right (if-test-index))
                    (push-proof-log 'if-true index)))
                 ((= i2 1)
                  (let ((sum (raw-expr-of-sum (sum-of-node left 3))))
                    (push-proof-log 'if-equal index
                                    `(= ,sum (- (negate ,lexpr) 1))
				    t)
                    (push-proof-log 'look-up (cons 1 (if-left-index))
                                    `(- (negate ,lexpr) 1))
                    ;; (if (= sum (- (negate left) 1))
                    ;;     (>= (- (negate left) 1) 0)
                    ;;     (>= sum 0))
                    (log-collect-terms `(- (negate ,lexpr) 1)
                                       (cons 2 (if-test-index)))
                    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (- (negate left) 1) 0)
                    (log-node-equality
                     left (arg-1-node prod) (list* 1 1 1 index))
                    ;; (>= (- (negate l) 1) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (- (negate ,(second pexpr)) 1) 0) '*.l.6
                     `((= |)X| ,(second pexpr)) (= |)Y| ,(third pexpr))) index)
                    ;; (if (>= (- (* l r) 1) 0)
                    ;;     (if (>= (negate r) 0)
                    ;;         (true)
                    ;;         (>= (- (negate l) 1) 0))
                    ;;     (>= (- (negate l) 1) 0))
                    (log-justify-gt prod ref (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (if (>= (negate r) 0) (true) (>= (- (negate l) 1) 0))
                    (log-justify-le (arg-2-node prod) right (if-test-index))
                    (push-proof-log 'if-true index)))
                 ((= i2 2)
                  (let ((sum (raw-expr-of-sum (sum-of-node left 2))))
                    (push-proof-log 'if-equal index `(= ,sum (- ,lexpr 1)) t)
                    (push-proof-log 'look-up (cons 1 (if-left-index))
                                    `(- ,lexpr 1))
                    ;; (if (= sum (- left 1)) (>= (- left 1) 0) (>= sum 0))
                    (log-collect-terms `(- ,lexpr 1) (cons 2 (if-test-index)))
                    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (- left 1) 0)
                    (log-node-equality
                     left (arg-1-node prod) (list* 1 1 index))
                    ;; (>= (- l 1) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (- ,(second pexpr) 1) 0) '*.l.7
                     `((= |)X| ,(second pexpr)) (= |)Y| ,(third pexpr))) index)
                    ;; (if (>= (- (* l r) 1) 0)
                    ;;     (if (>= (- r 1) 0) (true) (>= (- l 1) 0))
                    ;;     (>= (- l 1) 0))
                    (log-justify-gt prod ref (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (if (>= (- r 1) 0) (true) (>= (- l 1) 0))
                    (log-justify-gt (arg-2-node prod) right (if-test-index))
                    (push-proof-log 'if-true index)))
                 ((= i2 3)
                  (let ((sum (raw-expr-of-sum (sum-of-node left 3))))
                    (push-proof-log 'if-equal index
                                    `(= ,sum (- (negate ,lexpr) 1))
				    t)
                    (push-proof-log 'look-up (cons 1 (if-left-index))
                                    `(- (negate ,lexpr) 1))
                    ;; (if (= sum (- (negate left) 1))
                    ;;     (>= (- (negate left) 1) 0)
                    ;;     (>= sum 0))
                    (log-collect-terms `(- (negate ,lexpr) 1)
                                       (cons 2 (if-test-index)))
                    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (- (negate left) 1) 0)
                    (log-node-equality
                     left (arg-1-node prod) (list* 1 1 1 index))
                    ;; (>= (- (negate l) 1) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (- (negate ,(second pexpr)) 1) 0) '*.l.8
                     `((= |)X| ,(second pexpr)) (= |)Y| ,(third pexpr))) index)
                    ;; (if (>= (- (* l r) 1) 0)
                    ;;     (if (>= (- (negate r) 1) 0)
                    ;;         (true)
                    ;;         (>= (- (negate l) 1) 0))
                    ;;     (>= (- (negate l) 1) 0))
                    (log-justify-gt prod ref (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (if (>= (- (negate r) 1) 0)
                    ;;     (true)
                    ;;     (>= (- (negate l) 1) 0))
                    (log-justify-lt (arg-2-node prod) right (if-test-index))
                    (push-proof-log 'if-true index)))))
          ((= i1 3)
           (cond ((= i2 0)
                  (let ((sum (raw-expr-of-sum (sum-of-node left 3))))
                    (push-proof-log 'if-equal index
                                    `(= ,sum (- (negate ,lexpr) 1))
				    t)
                    (push-proof-log 'look-up (cons 1 (if-left-index))
                                    `(- (negate ,lexpr) 1))
                    ;; (if (= sum (- (negate left) 1))
                    ;;     (>= (- (negate left) 1) 0)
                    ;;     (>= sum 0))
                    (log-collect-terms `(- (negate ,lexpr) 1)
                                       (cons 2 (if-test-index)))
                    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (- (negate left) 1) 0)
                    (log-node-equality
                     left (arg-1-node prod) (list* 1 1 1 index))
                    ;; (>= (- (negate l) 1) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (- (negate ,(second pexpr)) 1) 0) '*.l.9
                     `((= |)X| ,(second pexpr)) (= |)Y| ,(third pexpr))) index)
                    ;; (if (>= (- (negate (* l r)) 1) 0)
                    ;;     (if (>= r 0) (true) (>= (- (negate l) 1) 0))
                    ;;     (>= (- (negate l) 1) 0))
                    (log-justify-lt prod ref (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (if (>= r 0) (true) (>= (- (negate l) 1) 0))
                    (log-justify-ge (arg-2-node prod) right (if-test-index))
                    (push-proof-log 'if-true index)))
                 ((= i2 1)
                  (let ((sum (raw-expr-of-sum (sum-of-node left 2))))
                    (push-proof-log 'if-equal index `(= ,sum (- ,lexpr 1)) t)
                    (push-proof-log 'look-up (cons 1 (if-left-index))
                                    `(- ,lexpr 1))
                    ;; (if (= sum (- left 1)) (>= (- left 1) 0) (>= sum 0))
                    (log-collect-terms `(- ,lexpr 1) (cons 2 (if-test-index)))
                    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (- left 1) 0)
                    (log-node-equality
                     left (arg-1-node prod) (list* 1 1 index))
                    ;; (>= (- l 1) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (- ,(second pexpr) 1) 0) '*.l.10
                     `((= |)X| ,(second pexpr)) (= |)Y| ,(third pexpr))) index)
                    ;; (if (>= (- (negate (* l r)) 1) 0)
                    ;;     (if (>= (negate r) 0) (true) (>= (- l 1) 0))
                    ;;     (>= (- l 1) 0))
                    (log-justify-lt prod ref (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (if (>= (negate r) 0) (true) (>= (- l 1) 0))
                    (log-justify-le (arg-2-node prod) right (if-test-index))
                    (push-proof-log 'if-true index)))
                 ((= i2 2)
                  (let ((sum (raw-expr-of-sum (sum-of-node left 3))))
                    (push-proof-log 'if-equal index
                                    `(= ,sum (- (negate ,lexpr) 1))
				    t)
                    (push-proof-log 'look-up (cons 1 (if-left-index))
                                    `(- (negate ,lexpr) 1))
                    ;; (if (= sum (- left 1)) (>= (- left 1) 0) (>= sum 0))
                    (log-collect-terms `(- (negate ,lexpr) 1)
                                       (cons 2 (if-test-index)))
                    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (- (negate left) 1) 0)
                    (log-node-equality
                     left (arg-1-node prod) (list* 1 1 1 index))
                    ;; (>= (- (negate l) 1) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (- (negate ,(second pexpr)) 1) 0) '*.l.11
                     `((= |)X| ,(second pexpr)) (= |)Y| ,(third pexpr))) index)
                    ;; (if (>= (- (negate (* l r)) 1) 0)
                    ;;     (if (>= (- r 1) 0) (true) (>= (- (negate l) 1) 0))
                    ;;     (>= (- (negate l) 1) 0))
                    (log-justify-lt prod ref (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (if (>= (- r 1) 0) (true) (>= (- (negate l) 1) 0))
                    (log-justify-gt (arg-2-node prod) right (if-test-index))
                    (push-proof-log 'if-true index)))
                 ((= i2 3)
                  (let ((sum (raw-expr-of-sum (sum-of-node left 2))))
                    (push-proof-log 'if-equal index `(= ,sum (- ,lexpr 1)) t)
                    (push-proof-log 'look-up (cons 1 (if-left-index))
                                    `(- ,lexpr 1))
                    ;; (if (= sum (- left 1)) (>= (- left 1) 0) (>= sum 0))
                    (log-collect-terms `(- ,lexpr 1) (cons 2 (if-test-index)))
                    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (- left 1) 0)
                    (log-node-equality
                     left (arg-1-node prod) (list* 1 1 index))
                    ;; (>= (- l 1) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (- ,(second pexpr) 1) 0) '*.l.12
                     `((= |)X| ,(second pexpr)) (= |)Y| ,(third pexpr))) index)
                    ;; (if (>= (- (negate (* l r)) 1) 0)
                    ;;     (if (>= (- (negate r) 1) 0) (true) (>= (- l 1) 0))
                    ;;     (>= (- l 1) 0))
                    (log-justify-lt prod ref (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (if (>= (- (negate r) 1) 0) (true) (>= (- l 1) 0))
                    (log-justify-lt (arg-2-node prod) right (if-test-index))
                    (push-proof-log 'if-true index))))))))



;;; Log transformation of (>= sum1 0) to (TRUE) based on the fact that
;;; (>= sum2 0) and (>= sum3 0),
;;; where sum3 is a (non-strict) restriction on left,
;;; sum1 is the strict version of sum2,
;;; sum2 is the sum of a node that is equivalent to a product
;;; that has a left argument equivalent to left.

(defun log-justify-*-ll (i1 i2 ref prod left index)
  (let ((pexpr (e-node-attribute prod))
        (lexpr (e-node-attribute left)))
    (cond ((= i1 2)
           (cond ((= i2 0)
                  (let ((sum1 (raw-expr-of-sum (sum-of-node left 2))))
                    (push-proof-log 'if-equal index `(= ,sum1 (- ,lexpr 1)) t)
                    (push-proof-log 'look-up (cons 1 (if-left-index))
                                    `(- ,lexpr 1))
                    ;; (if (= sum1 (- left 1)) (>= (- left 1) 0) (>= sum1 0))
                    (log-collect-terms `(- ,lexpr 1) (cons 2 (if-test-index)))
                    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (- left 1) 0)
                    (log-node-equality
                     left (arg-1-node prod) (list* 1 1 index))
                    ;; (>= (- l 1) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (- ,(second pexpr) 1) 0) '*.ll.1
                     `((= |)X| ,(second pexpr)) (= |)Y| ,(third pexpr))) index)
                    ;; (if (>= (- (* l r) 1) 0) (>= (ord l) 0) (>= (- l 1) 0))
                    (log-justify-gt prod ref (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (ord l) 0)
                    (log-node-equality
                     (arg-1-node prod) left (list* 1 1 index))
                    (log-collect-terms `(ord ,lexpr) (cons 1 index))
                    (log-justify-restriction left 0 index)))
                 ((= i2 1)
                  (let ((sum1 (raw-expr-of-sum (sum-of-node left 3))))
                    (push-proof-log 'if-equal index
                                    `(= ,sum1 (- (negate ,lexpr) 1))
				    t)
                    (push-proof-log 'look-up (cons 1 (if-left-index))
                                    `(- (negate ,lexpr) 1))
                    ;; (if (= sum1 (- (negate left) 1))
                    ;;     (>= (- (negate left) 1) 0)
                    ;;     (>= sum1 0))
                    (log-collect-terms `(- (negate ,lexpr) 1)
                                       (cons 2 (if-test-index)))
                    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (- (negate left) 1) 0)
                    (log-node-equality
                     left (arg-1-node prod) (list* 1 1 1 index))
                    ;; (>= (- (negate l) 1) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (- (negate ,(second pexpr)) 1) 0) '*.ll.2
                     `((= |)X| ,(second pexpr)) (= |)Y| ,(third pexpr))) index)
                    ;; (if (>= (- (* l r) 1) 0)
                    ;;     (>= (negate l) 0)
                    ;;     (>= (- (negate l) 1) 0))
                    (log-justify-gt prod ref (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (negate l) 0)
                    (log-node-equality
                     (arg-1-node prod) left (list* 1 1 index))
                    (log-collect-terms `(negate ,lexpr) (cons 1 index))
                    (log-justify-restriction left 1 index)))))
          ((= i1 3)
           (cond ((= i2 0)
                  (let ((sum1 (raw-expr-of-sum (sum-of-node left 2))))
                    (push-proof-log 'if-equal index `(= ,sum1 (- ,lexpr 1)) t)
                    (push-proof-log 'look-up (cons 1 (if-left-index))
                                    `(- ,lexpr 1))
                    ;; (if (= sum1 (- left 1)) (>= (- left 1) 0) (>= sum1 0))
                    (log-collect-terms `(- ,lexpr 1) (cons 2 (if-test-index)))
                    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (- left 1) 0)
                    (log-node-equality
                     left (arg-1-node prod) (list* 1 1 index))
                    ;; (>= (- l 1) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (- ,(second pexpr) 1) 0) '*.ll.3
                     `((= |)X| ,(second pexpr)) (= |)Y| ,(third pexpr))) index)
                    ;; (if (>= (- (negate (* l r)) 1) 0)
                    ;;     (>= (ord l) 0)
                    ;;     (>= (- l 1) 0))
                    (log-justify-lt prod ref (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (ord l) 0)
                    (log-node-equality
                     (arg-1-node prod) left (list* 1 1 index))
                    (log-collect-terms `(ord ,lexpr) (cons 1 index))
                    (log-justify-restriction left 0 index)))
                 ((= i2 1)
                  (let ((sum1 (raw-expr-of-sum (sum-of-node left 3))))
                    (push-proof-log 'if-equal index
                                    `(= ,sum1 (- (negate ,lexpr) 1))
				    t)
                    (push-proof-log 'look-up (cons 1 (if-left-index))
                                    `(- (negate ,lexpr) 1))
                    ;; (if (= sum1 (- (negate left) 1))
                    ;;     (>= (- (negate left) 1) 0)
                    ;;     (>= sum1 0))
                    (log-collect-terms `(- (negate ,lexpr) 1)
                                       (cons 2 (if-test-index)))
                    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (- (negate left) 1) 0)
                    (log-node-equality
                     left (arg-1-node prod) (list* 1 1 1 index))
                    ;; (>= (- (negate l) 1) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (- (negate ,(second pexpr)) 1) 0) '*.ll.4
                     `((= |)X| ,(second pexpr)) (= |)Y| ,(third pexpr))) index)
                    ;; (if (>= (- (negate (* l r)) 1) 0)
                    ;;     (>= (negate l) 0)
                    ;;     (>= (- (negate l) 1) 0))
                    (log-justify-lt prod ref (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (negate l) 0)
                    (log-node-equality
                     (arg-1-node prod) left (list* 1 1 index))
                    (log-collect-terms `(negate ,lexpr) (cons 1 index))
                    (log-justify-restriction left 1 index))))))))



;;; Log transformation of (>= sum 0) to (true) based on the fact
;;; that a product and its left argument are (indirectly) restricted,
;;; and sum is the (indirect) sum of the right argument.

(defun log-justify-*-r (i1 i2 ref prod left right index)
  (let ((pexpr (e-node-attribute prod))
        (rexpr (e-node-attribute right)))
    (cond ((= i1 0)
           (cond ((= i2 2)
                  (let ((sum (raw-expr-of-sum (sum-of-node right 0))))
                    (push-proof-log 'if-equal index `(= ,sum (ord ,rexpr)) t)
                    (push-proof-log 'look-up (cons 1 (if-left-index))
                                    `(ord ,rexpr))
                    ;; (if (= sum (ord right)) (>= (ord right) 0) (>= sum 0))
                    (log-collect-terms `(ord ,rexpr) (cons 2 (if-test-index)))
                    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (ord right) 0)
                    (log-node-equality
                     right (arg-2-node prod) (list* 1 1 index))
                    ;; (>= (ord r) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (ord ,(third pexpr)) 0) '*.r.1
                     `((= |)X| ,(third pexpr)) (= |)Y| ,(second pexpr))) index)
                    ;; (if (>= (* l r) 0)
                    ;;     (if (>= (- l 1) 0) (true) (>= (ord r) 0))
                    ;;     (>= (ord r) 0))
                    (log-justify-ge prod ref (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (if (>= (- l 1) 0) (true) (>= (ord r) 0))
                    (log-justify-gt (arg-1-node prod) left (if-test-index))
                    (push-proof-log 'if-true index)))
                 ((= i2 3)
                  (let ((sum (raw-expr-of-sum (sum-of-node right 1))))
                    (push-proof-log 'if-equal index `(= ,sum (negate ,rexpr)) t)
                    (push-proof-log 'look-up (cons 1 (if-left-index))
                                    `(negate ,rexpr))
                    ;; (if (= sum (negate right))
                    ;;     (>= (negate right) 0)
                    ;;     (>= sum 0))
                    (log-collect-terms `(negate ,rexpr)
                                       (cons 2 (if-test-index)))
                    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (negate right) 0)
                    (log-node-equality
                     right (arg-2-node prod) (list* 1 1 index))
                    ;; (>= (negate r) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (negate ,(third pexpr)) 0) '*.r.2
                     `((= |)X| ,(third pexpr)) (= |)Y| ,(second pexpr))) index)
                    ;; (if (>= (* l r) 0)
                    ;;     (if (>= (- (negate l) 1) 0)
                    ;;         (true)
                    ;;         (>= (negate r) 0))
                    ;;     (>= (negate r) 0))
                    (log-justify-ge prod ref (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (if (>= (- (negate l) 1) 0) (true) (>= (negate r) 0))
                    (log-justify-lt (arg-1-node prod) left (if-test-index))
                    (push-proof-log 'if-true index)))))
          ((= i1 1)
           (cond ((= i2 2)
                  (let ((sum (raw-expr-of-sum (sum-of-node right 1))))
                    (push-proof-log 'if-equal index `(= ,sum (negate ,rexpr)) t)
                    (push-proof-log 'look-up (cons 1 (if-left-index))
                                    `(negate ,rexpr))
                    ;; (if (= sum (negate right))
                    ;;     (>= (negate right) 0)
                    ;;     (>= sum 0))
                    (log-collect-terms `(negate ,rexpr)
                                       (cons 2 (if-test-index)))
                    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (negate right) 0)
                    (log-node-equality
                     right (arg-2-node prod) (list* 1 1 index))
                    ;; (>= (negate r) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (negate ,(third pexpr)) 0) '*.r.3
                     `((= |)X| ,(third pexpr)) (= |)Y| ,(second pexpr))) index)
                    ;; (if (>= (negate (* l r)) 0)
                    ;;     (if (>= (- l 1) 0) (true) (>= (negate r) 0))
                    ;;     (>= (negate r) 0))
                    (log-justify-le prod ref (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (if (>= (- (negate l) 1) 0) (true) (>= (negate r) 0))
                    (log-justify-gt (arg-1-node prod) left (if-test-index))
                    (push-proof-log 'if-true index)))
                 ((= i2 3)
                  (let ((sum (raw-expr-of-sum (sum-of-node right 0))))
                    (push-proof-log 'if-equal index `(= ,sum (ord ,rexpr)) t)
                    (push-proof-log 'look-up (cons 1 (if-left-index))
                                    `(ord ,rexpr))
                    ;; (if (= sum (ord right)) (>= (ord right) 0) (>= sum 0))
                    (log-collect-terms `(ord ,rexpr) (cons 2 (if-test-index)))
                    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (ord right) 0)
                    (log-node-equality
                     right (arg-2-node prod) (list* 1 1 index))
                    ;; (>= (ord r) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (ord ,(third pexpr)) 0) '*.r.4
                     `((= |)X| ,(third pexpr)) (= |)Y| ,(second pexpr))) index)
                    ;; (if (>= (negate (* l r)) 0)
                    ;;     (if (>= (- (negate l) 1) 0) (true) (>= (ord r) 0))
                    ;;     (>= (ord r) 0))
                    (log-justify-le prod ref (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (if (>= (- (negate l) 1) 0) (true) (>= (ord r) 0))
                    (log-justify-lt (arg-1-node prod) left (if-test-index))
                    (push-proof-log 'if-true index)))))
          ((= i1 2)
           (cond ((= i2 0)
                  (let ((sum (raw-expr-of-sum (sum-of-node right 2))))
                    (push-proof-log 'if-equal index `(= ,sum (- ,rexpr 1)) t)
                    (push-proof-log 'look-up (cons 1 (if-left-index))
                                    `(- ,rexpr 1))
                    ;; (if (= sum (- right 1)) (>= (- right 1) 0) (>= sum 0))
                    (log-collect-terms `(- ,rexpr 1) (cons 2 (if-test-index)))
                    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (- right 1) 0)
                    (log-node-equality
                     right (arg-2-node prod) (list* 1 1 index))
                    ;; (>= (- r 1) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (- ,(third pexpr) 1) 0) '*.r.5
                     `((= |)X| ,(third pexpr)) (= |)Y| ,(second pexpr))) index)
                    ;; (if (>= (- (* l r) 1) 0)
                    ;;     (if (>= l 0) (true) (>= (- r 1) 0))
                    ;;     (>= (- r 1) 0))
                    (log-justify-gt prod ref (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (if (>= r 0) (true) (>= (- l 1) 0))
                    (log-justify-ge (arg-1-node prod) left (if-test-index))
                    (push-proof-log 'if-true index)))
                 ((= i2 1)
                  (let ((sum (raw-expr-of-sum (sum-of-node right 3))))
                    (push-proof-log 'if-equal index
                                    `(= ,sum (- (negate ,rexpr) 1))
				    t)
                    (push-proof-log 'look-up (cons 1 (if-left-index))
                                    `(- (negate ,rexpr) 1))
                    ;; (if (= sum (- (negate right) 1))
                    ;;     (>= (- (negate right) 1) 0)
                    ;;     (>= sum 0))
                    (log-collect-terms `(- (negate ,rexpr) 1)
                                       (cons 2 (if-test-index)))
                    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (- (negate right) 1) 0)
                    (log-node-equality
                     right (arg-2-node prod) (list* 1 1 1 index))
                    ;; (>= (- (negate r) 1) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (- (negate ,(third pexpr)) 1) 0) '*.r.6
                     `((= |)X| ,(third pexpr)) (= |)Y| ,(second pexpr))) index)
                    ;; (if (>= (- (* l r) 1) 0)
                    ;;     (if (>= (negate l) 0)
                    ;;         (true)
                    ;;         (>= (- (negate r) 1) 0))
                    ;;     (>= (- (negate r) 1) 0))
                    (log-justify-gt prod ref (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (if (>= (negate r) 0) (true) (>= (- (negate l) 1) 0))
                    (log-justify-le (arg-1-node prod) left (if-test-index))
                    (push-proof-log 'if-true index)))
                 ((= i2 2)
                  (let ((sum (raw-expr-of-sum (sum-of-node right 2))))
                    (push-proof-log 'if-equal index `(= ,sum (- ,rexpr 1)) t)
                    (push-proof-log 'look-up (cons 1 (if-left-index))
                                    `(- ,rexpr 1))
                    ;; (if (= sum (- right 1)) (>= (- right 1) 0) (>= sum 0))
                    (log-collect-terms `(- ,rexpr 1) (cons 2 (if-test-index)))
                    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (- right 1) 0)
                    (log-node-equality
                     right (arg-2-node prod) (list* 1 1 index))
                    ;; (>= (- l 1) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (- ,(third pexpr) 1) 0) '*.r.7
                     `((= |)X| ,(third pexpr)) (= |)Y| ,(second pexpr))) index)
                    ;; (if (>= (- (* l r) 1) 0)
                    ;;     (if (>= (- l 1) 0) (true) (>= (- r 1) 0))
                    ;;     (>= (- r 1) 0))
                    (log-justify-gt prod ref (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (if (>= (- l 1) 0) (true) (>= (- r 1) 0))
                    (log-justify-gt (arg-1-node prod) left (if-test-index))
                    (push-proof-log 'if-true index)))
                 ((= i2 3)
                  (let ((sum (raw-expr-of-sum (sum-of-node right 3))))
                    (push-proof-log 'if-equal index
                                    `(= ,sum (- (negate ,rexpr) 1))
				    t)
                    (push-proof-log 'look-up (cons 1 (if-left-index))
                                    `(- (negate ,rexpr) 1))
                    ;; (if (= sum (- (negate right) 1))
                    ;;     (>= (- (negate right) 1) 0)
                    ;;     (>= sum 0))
                    (log-collect-terms `(- (negate ,rexpr) 1)
                                       (cons 2 (if-test-index)))
                    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (- (negate right) 1) 0)
                    (log-node-equality
                     right (arg-2-node prod) (list* 1 1 1 index))
                    ;; (>= (- (negate r) 1) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (- (negate ,(third pexpr)) 1) 0) '*.r.8
                     `((= |)X| ,(third pexpr)) (= |)Y| ,(second pexpr))) index)
                    ;; (if (>= (- (* l r) 1) 0)
                    ;;     (if (>= (- (negate l) 1) 0)
                    ;;         (true)
                    ;;         (>= (- (negate r) 1) 0))
                    ;;     (>= (- (negate r) 1) 0))
                    (log-justify-gt prod ref (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (if (>= (- (negate l) 1) 0)
                    ;;     (true)
                    ;;     (>= (- (negate r) 1) 0))
                    (log-justify-lt (arg-1-node prod) left (if-test-index))
                    (push-proof-log 'if-true index)))))
          ((= i1 3)
           (cond ((= i2 0)
                  (let ((sum (raw-expr-of-sum (sum-of-node right 3))))
                    (push-proof-log 'if-equal index
                                    `(= ,sum (- (negate ,rexpr) 1))
				    t)
                    (push-proof-log 'look-up (cons 1 (if-left-index))
                                    `(- (negate ,rexpr) 1))
                    ;; (if (= sum (- (negate right) 1))
                    ;;     (>= (- (negate right) 1) 0)
                    ;;     (>= sum 0))
                    (log-collect-terms `(- (negate ,rexpr) 1)
                                       (cons 2 (if-test-index)))
                    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (- (negate right) 1) 0)
                    (log-node-equality
                     right (arg-2-node prod) (list* 1 1 1 index))
                    ;; (>= (- (negate r) 1) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (- (negate ,(third pexpr)) 1) 0) '*.r.9
                     `((= |)X| ,(third pexpr)) (= |)Y| ,(second pexpr))) index)
                    ;; (if (>= (- (negate (* l r)) 1) 0)
                    ;;     (if (>= l 0) (true) (>= (- (negate r) 1) 0))
                    ;;     (>= (- (negate r) 1) 0))
                    (log-justify-lt prod ref (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (if (>= l 0) (true) (>= (- (negate r) 1) 0))
                    (log-justify-ge (arg-1-node prod) left (if-test-index))
                    (push-proof-log 'if-true index)))
                 ((= i2 1)
                  (let ((sum (raw-expr-of-sum (sum-of-node right 2))))
                    (push-proof-log 'if-equal index `(= ,sum (- ,rexpr 1)) t)
                    (push-proof-log 'look-up (cons 1 (if-left-index))
                                    `(- ,rexpr 1))
                    ;; (if (= sum (- right 1)) (>= (- right 1) 0) (>= sum 0))
                    (log-collect-terms `(- ,rexpr 1) (cons 2 (if-test-index)))
                    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (- right 1) 0)
                    (log-node-equality
                     right (arg-2-node prod) (list* 1 1 index))
                    ;; (>= (- r 1) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (- ,(third pexpr) 1) 0) '*.r.10
                     `((= |)X| ,(third pexpr)) (= |)Y| ,(second pexpr))) index)
                    ;; (if (>= (- (negate (* l r)) 1) 0)
                    ;;     (if (>= (negate l) 0) (true) (>= (- r 1) 0))
                    ;;     (>= (- r 1) 0))
                    (log-justify-lt prod ref (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (if (>= (negate l) 0) (true) (>= (- r 1) 0))
                    (log-justify-le (arg-1-node prod) left (if-test-index))
                    (push-proof-log 'if-true index)))
                 ((= i2 2)
                  (let ((sum (raw-expr-of-sum (sum-of-node right 3))))
                    (push-proof-log 'if-equal index
                                    `(= ,sum (- (negate ,rexpr) 1))
				    t)
                    (push-proof-log 'look-up (cons 1 (if-left-index))
                                    `(- (negate ,rexpr) 1))
                    ;; (if (= sum (- right 1)) (>= (- right 1) 0) (>= sum 0))
                    (log-collect-terms `(- (negate ,rexpr) 1)
                                       (cons 2 (if-test-index)))
                    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (- (negate right) 1) 0)
                    (log-node-equality
                     right (arg-2-node prod) (list* 1 1 1 index))
                    ;; (>= (- (negate r) 1) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (- (negate ,(third pexpr)) 1) 0) '*.r.11
                     `((= |)X| ,(third pexpr)) (= |)Y| ,(second pexpr))) index)
                    ;; (if (>= (- (negate (* l r)) 1) 0)
                    ;;     (if (>= (- l 1) 0) (true) (>= (- (negate r) 1) 0))
                    ;;     (>= (- (negate r) 1) 0))
                    (log-justify-lt prod ref (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (if (>= (- l 1) 0) (true) (>= (- (negate r) 1) 0))
                    (log-justify-gt (arg-1-node prod) left (if-test-index))
                    (push-proof-log 'if-true index)))
                 ((= i2 3)
                  (let ((sum (raw-expr-of-sum (sum-of-node right 2))))
                    (push-proof-log 'if-equal index `(= ,sum (- ,rexpr 1)) t)
                    (push-proof-log 'look-up (cons 1 (if-left-index))
                                    `(- ,rexpr 1))
                    ;; (if (= sum (- right 1)) (>= (- right 1) 0) (>= sum 0))
                    (log-collect-terms `(- ,rexpr 1) (cons 2 (if-test-index)))
                    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (- right 1) 0)
                    (log-node-equality
                     right (arg-2-node prod) (list* 1 1 index))
                    ;; (>= (- l 1) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (- ,(third pexpr) 1) 0) '*.r.12
                     `((= |)X| ,(third pexpr)) (= |)Y| ,(second pexpr))) index)
                    ;; (if (>= (- (negate (* l r)) 1) 0)
                    ;;     (if (>= (- (negate l) 1) 0) (true) (>= (- r 1) 0))
                    ;;     (>= (- r 1) 0))
                    (log-justify-lt prod ref (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (if (>= (- (negate l) 1) 0) (true) (>= (- r 1) 0))
                    (log-justify-lt (arg-1-node prod) left (if-test-index))
                    (push-proof-log 'if-true index))))))))



;;; Log transformation of (>= sum1 0) to (TRUE) based on the fact that
;;; (>= sum2 0) and (>= sum3 0),
;;; where sum3 is a (non-strict) restriction on right,
;;; sum1 is the strict version of sum2,
;;; sum2 is the sum of a node that is equivalent to a product
;;; that has a right argument equivalent to right.

(defun log-justify-*-rr (i1 i2 ref prod right index)
  (let ((pexpr (e-node-attribute prod))
        (rexpr (e-node-attribute right)))
    (cond ((= i1 2)
           (cond ((= i2 0)
                  (let ((sum1 (raw-expr-of-sum (sum-of-node right 2))))
                    (push-proof-log 'if-equal index `(= ,sum1 (- ,rexpr 1)) t)
                    (push-proof-log 'look-up (cons 1 (if-left-index))
                                    `(- ,rexpr 1))
                    ;; (if (= sum1 (- right 1)) (>= (- right 1) 0) (>= sum1 0))
                    (log-collect-terms `(- ,rexpr 1) (cons 2 (if-test-index)))
                    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (- right 1) 0)
                    (log-node-equality
                     right (arg-2-node prod) (list* 1 1 index))
                    ;; (>= (- r 1) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (- ,(third pexpr) 1) 0) '*.rr.1
                     `((= |)X| ,(third pexpr)) (= |)Y| ,(second pexpr))) index)
                    ;; (if (>= (- (* l r) 1) 0) (>= (ord r) 0) (>= (- r 1) 0))
                    (log-justify-gt prod ref (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (ord r) 0)
                    (log-node-equality
                     (arg-2-node prod) right (list* 1 1 index))
                    (log-collect-terms `(ord ,rexpr) (cons 1 index))
                    (log-justify-restriction right 0 index)))
                 ((= i2 1)
                  (let ((sum1 (raw-expr-of-sum (sum-of-node right 3))))
                    (push-proof-log 'if-equal index
                                    `(= ,sum1 (- (negate ,rexpr) 1))
				    t)
                    (push-proof-log 'look-up (cons 1 (if-left-index))
                                    `(- (negate ,rexpr) 1))
                    ;; (if (= sum1 (- (negate right) 1))
                    ;;     (>= (- (negate right) 1) 0)
                    ;;     (>= sum1 0))
                    (log-collect-terms `(- (negate ,rexpr) 1)
                                       (cons 2 (if-test-index)))
                    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (- (negate right) 1) 0)
                    (log-node-equality
                     right (arg-2-node prod) (list* 1 1 1 index))
                    ;; (>= (- (negate r) 1) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (- (negate ,(third pexpr)) 1) 0) '*.rr.2
                     `((= |)X| ,(third pexpr)) (= |)Y| ,(second pexpr))) index)
                    ;; (if (>= (- (* l r) 1) 0)
                    ;;     (>= (negate r) 0)
                    ;;     (>= (- (negate r) 1) 0))
                    (log-justify-gt prod ref (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (negate r) 0)
                    (log-node-equality
                     (arg-2-node prod) right (list* 1 1 index))
                    (log-collect-terms `(negate ,rexpr) (cons 1 index))
                    (log-justify-restriction right 1 index)))))
          ((= i1 3)
           (cond ((= i2 0)
                  (let ((sum1 (raw-expr-of-sum (sum-of-node right 2))))
                    (push-proof-log 'if-equal index `(= ,sum1 (- ,rexpr 1)) t)
                    (push-proof-log 'look-up (cons 1 (if-left-index))
                                    `(- ,rexpr 1))
                    ;; (if (= sum1 (- right 1)) (>= (- right 1) 0) (>= sum1 0))
                    (log-collect-terms `(- ,rexpr 1) (cons 2 (if-test-index)))
                    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (- right 1) 0)
                    (log-node-equality
                     right (arg-2-node prod) (list* 1 1 index))
                    ;; (>= (- r 1) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (- ,(third pexpr) 1) 0) '*.rr.3
                     `((= |)X| ,(third pexpr)) (= |)Y| ,(second pexpr))) index)
                    ;; (if (>= (- (negate (* l r)) 1) 0)
                    ;;     (>= (ord r) 0)
                    ;;     (>= (- r 1) 0))
                    (log-justify-lt prod ref (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (ord r) 0)
                    (log-node-equality
                     (arg-2-node prod) right (list* 1 1 index))
                    (log-collect-terms `(ord ,rexpr) (cons 1 index))
                    (log-justify-restriction right 0 index)))
                 ((= i2 1)
                  (let ((sum1 (raw-expr-of-sum (sum-of-node right 3))))
                    (push-proof-log 'if-equal index
                                    `(= ,sum1 (- (negate ,rexpr) 1))
				    t)
                    (push-proof-log 'look-up (cons 1 (if-left-index))
                                    `(- (negate ,rexpr) 1))
                    ;; (if (= sum1 (- (negate right) 1))
                    ;;     (>= (- (negate right) 1) 0)
                    ;;     (>= sum1 0))
                    (log-collect-terms `(- (negate ,rexpr) 1)
                                       (cons 2 (if-test-index)))
                    (push-proof-log 'compute (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (- (negate right) 1) 0)
                    (log-node-equality
                     right (arg-2-node prod) (list* 1 1 1 index))
                    ;; (>= (- (negate l) 1) 0)
                    (log-use-axiom-as-rewrite
                     `(>= (- (negate ,(third pexpr)) 1) 0) '*.rr.4
                     `((= |)X| ,(third pexpr)) (= |)Y| ,(second pexpr))) index)
                    ;; (if (>= (- (negate (* l r)) 1) 0)
                    ;;     (>= (negate r) 0)
                    ;;     (>= (- (negate r) 1) 0))
                    (log-justify-lt prod ref (if-test-index))
                    (push-proof-log 'if-true index)
                    ;; (>= (negate r) 0)
                    (log-node-equality
                     (arg-2-node prod) right (list* 1 1 index))
                    (log-collect-terms `(negate ,rexpr) (cons 1 index))
                    (log-justify-restriction right 1 index))))))))
