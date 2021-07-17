
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


;;; =============== Proof Logging for the Simplifier ===============


;;; Code to do proof logging of inferences performed by the the
;;; simplifier. The more mundane proof logging steps are delegated
;;; to functions in log-integers.

;;; The proof logs are "triggered" by "justifications". When performing
;;; a step that may have logical consequences, the simplifier records
;;; a "justification" for that step. Later on when the simplifier needs
;;; to justify a transformation of a subexpression, a sequence of these
;;; "justifications" may be invoked to form a chain of reasoning that
;;; is translated into a sequence of proof log entries.



;;; log-inconsistent logs the transformation of (false) to (true)
;;; based on inconsistent hypotheses.
(defun log-inconsistent (justification index)
  (cond ((atom justification) (print justification)
         )
        (t
           (case (car justification)
             (kill-one
              (log-kill-one (second justification) index))
             (inconsistent-restrictions
              (log-inconsistent-restrictions justification index))
             (non-integer
              (log-non-integer
               (second justification) (third justification)
               (fourth justification) (fifth justification) index))
             (forbid-merge
              ;; At this point we can derive both (= expr1 expr2)
              ;; and (not (= expr1 expr2))
              (let ((node1 (second justification))
                    (node2 (third justification)))
                (push-proof-log 'if-true index *true* t)
                (log-true-to-= (e-node-attribute node1) (if-test-index))
                ;; (if (= expr1 expr1) (false) (true))
                (log-node-equality node1 node2 (cons 2 (if-test-index)))
                ;; (if (= expr1 expr2) (false) (true))
                (log-forbid-aux node1 node2 (fourth justification) index)))
             (merge-forbid
              ;; At this point we can derive both (= expr1 expr2)
              ;; and (not (= expr1 expr2))
              (let ((node1 (second justification))
                    (node2 (third justification)))
                (push-proof-log 'if-true index *true* t)
                (log-true-to-= (e-node-attribute node1) (if-test-index))
                ;; (if (= expr1 expr1) (false) (true))
                (log-equality-step-aux
                 node1 node2 (fourth justification) (cons 2 (if-test-index)))
                ;; (if (= expr1 expr2) (false) (true))
                (log-forbid-aux node1 node2 (fifth justification) index))
              )))))

(defun log-true->=-from-restricted (node index)
  (log-sum-conversion-of->= node index)
  (log-tableau-entry-is-restricted node 0 index))

(defun log-false->=-from-restricted (node index)
  (log-sum-conversion-of->= node index)
  ;; (>= sum 0)
  (let ((expr (raw-expr-of-sum (sum-of-node node 0))))
    (log-convert-boolean-to-coerced
     `(>= ,expr 0) index)
    ;; (if (>= sum 0) (true) (false))
    (push-proof-log
     'if-equal (if-left-index) `(= (true) (>= (negate ,expr) 1)) t)
    (push-proof-log 'look-up (cons 2 (if-left-index))
                    `(>= (negate ,expr) 1))
    ;; (if (>= sum 0)
    ;;     (if (= (true) (>= (negate sum) 1)) (>= (negate sum) 1) (true))
    ;;     (false))
    (log-convert->=-to->=-zero `(negate ,expr) 1 (list* 2 1 (if-left-index)))
    (log-push-negate-into-sum expr (list* 1 1 2 1 (if-left-index)))
    ;; (if (>= sum 0)
    ;;     (if (= (true) (>= (- nsum 1) 0))
    ;;         (>= (negate sum) 1)
    ;;         (true))
    ;;     (false))
    (let ((expr2 (raw-expr-of-sum (negative-sum (sum-of-node node 0)))))
      (cond ((integerp expr2)
	     (push-proof-log 'compute (list* 1 2 1 (if-left-index))))
	    (t
	     (log-use-axiom-as-rewrite
	      `(- ,expr2 1) '-.+.left.to.+.-.left
	      `((= |)X| ,(second expr2)) (= |)Y| ,(third expr2)) (= |)Z| 1))
	      (list* 1 2 1 (if-left-index)))
	     (push-proof-log 'compute (list* 1 1 2 1 (if-left-index)))))
      ;; (if (>= sum 0)
      ;;     (if (= (true) (>= osum 0)) (>= (negate sum) 1) (true))
      ;;     (false))
      (log-justify-restriction node 1 (list* 2 1 (if-left-index)))
      (push-proof-log 'compute (cons 1 (if-left-index)))
      (push-proof-log 'if-true (if-left-index))
      ;; (if (>= sum 0) (>= (negate sum) 1) (false))
      (log-use-axiom-as-rewrite
       `(>= (negate ,expr) 1) 'inconsistent.restrictions `((= |)X| ,expr))
       (if-left-index))
      ;; (if (>= sum 0) (if (>= sum 0) (false) (>= (negate sum) 0)) (false))
      (push-proof-log 'look-up (cons 1 (if-left-index)) *true*)
      (push-proof-log 'if-true (if-left-index))
      (push-proof-log 'if-equal index))))

(defun log-tableau-entry-is-restricted (node i index)
  (let* ((header (aref (e-node-tableau-entry node) i))
	 (restriction (cond ((row-p header) (row-restriction header))
			    ((col-p header) (col-restriction header)))))
    (cond ((eq restriction 'restricted)
           (log-justify-restriction node i index))
          ((eq restriction 'dead)
           (let ((expr (raw-expr-of-sum (sum-of-node node i))))
             (push-proof-log 'if-equal index `(= ,expr 0) t)
             (push-proof-log 'look-up (cons 1 (if-left-index)) 0)
             ;; (if (= sum 0) (>= 0 0) (>= sum 0))
             (push-proof-log 'compute (if-left-index))
             (log-justify-killed node i (if-test-index))
             (push-proof-log 'if-true index)))
          (t (let* ((triples (collect-row-triples header))
                    (c (apply #'lcm
                              (mapcar #'(lambda (u) (denominator (car u)))
                                      triples)))
                    (sum (multiply-collected-terms-by-constant
                          (sum-of-node node i) c))
                    (ctriples
                     (mapcar #'(lambda (u) (cons (* c (car u)) (cdr u)))
                             triples)))
               (unless (= c 1)
                 (let ((expr (raw-expr-of-sum (sum-of-node node i))))
                   (log-multiply->=-zero c expr index)
                   (log-push-multiplier-in c expr (cons 1 index))))
               (log-justify-triples sum ctriples index))))))



(defun log-kill-one (justification index)
  ;; (false)
  (push-proof-log 'if-false index *true* t)
  ;; (if (false) (true) (false))
  (push-proof-log 'if-equal (if-test-index) `(= (false) (= 1 0)) t)
  (push-proof-log 'look-up (cons 2 (if-test-index)) '(= 1 0))
  ;; (if (if (= (false) (= 1 0)) (= 1 0)) (true) (false))
  (push-proof-log 'compute (list* 2 1 (if-test-index)))
  (push-proof-log 'compute (cons 1 (if-test-index)))
  (push-proof-log 'if-true (if-test-index))
  ;; (if (= 1 0) (true) (false))
  (log-justify-killed-aux justification (if-test-index))
  (push-proof-log 'if-true index))

;;; Log transformation of (false) to (true) based on unachievable
;;; restrictions.

(defun log-inconsistent-restrictions (justification index)
  (let ((just2 (fifth justification)))
    (cond ((and (consp just2) (eq (car just2) 'maximized))
           (log-inconsistent-restrictions-maximized justification index))
          ((and (consp just2) (eq (car just2) 'minimized))
           (log-inconsistent-restrictions-minimized justification index)))))

(defun k-times-sum-minus-n (k n sum)
  (cons (- (* k (car sum)) n)
        (mapcar #'(lambda (u) (cons (car u) (* k (cdr u))))
                (cdr sum))))



;;; Log transformation of (false) to (true) based on inconsistent
;;; restrictions where a sum which is being restricted or killed is
;;; manifestly maximized at a negative value.

(defun log-inconsistent-restrictions-maximized (justification index)
  (let ((owner (third justification))
        (just1 (fourth justification))
        (just2 (fifth justification)))
    ;; just2 is (maximized owner triples)
    (let* ((sum (sum-of-node (cdr owner) (car owner)))
           (expr (raw-expr-of-sum sum)))
      (push-proof-log 'if-equal index `(= (false) (>= (negate ,expr) 1)) t)
      (push-proof-log 'look-up (if-left-index) `(>= (negate ,expr) 1))
      ;; (if (= (false) (>= (negate sum) 1)) (>= (negate sum) 1) (false))
      (cond ((eq (second justification) 'restrict)
             (log-inconsistent-restrictions-restrict
              expr just1 (cons 2 (if-test-index))))
            ((eq (second justification) 'kill)
             (log-inconsistent-restrictions-kill
              expr just1 (cons 2 (if-test-index)))))
      (push-proof-log 'compute (if-test-index))
      (push-proof-log 'if-true index)
      ;; (>= (negate sum) 1)
      (log-convert->=-to->=-zero `(negate ,expr) 1 index)
      ;; (>= (- (negate sum) 1) 0)
      (let* ((k (apply #'lcm (mapcar #'(lambda (u) (denominator (car u)))
                                     (third just2))))
             (n (- (* k (car (car (last (third just2)))))))
             (triples (mapcar #'(lambda (u) (cons (* (- k) (car u)) (cdr u)))
                              (third just2)))
             (nexpr (raw-expr-of-sum (negative-sum sum)))
             (nkexpr (raw-expr-of-sum
                      (multiply-collected-terms-by-constant sum (- k)))))
        (cond
         ((= k 1)
          (log-push-negate-into-sum expr (list* 1 1 index))
	  (cond ((integerp nexpr)
		 (push-proof-log 'compute (cons 1 index)))
		(t
		 (log-use-axiom-as-rewrite
		  `(- ,nexpr 1) '-.+.left.to.+.-.left
		  `((= |)X| ,(second nexpr)) (= |)Y| ,(third nexpr)) (= |)Z| 1))
		  (cons 1 index))
		 (push-proof-log 'compute (list* 1 1 index))))
	  (log-justify-triples
           (opposite-sum sum) triples index))
         (t
          (log-multiply->=-zero k `(- (negate ,expr) 1) index)
          ;; (>= (* k (- (negate sum) 1)) 0)
          (cond ((>= n k)
                 (log-inconsistent-restrictions-n->=-k
                  k n `(negate ,expr) index)
                 ;; (if (>= (+ (* k (negate sum)) -n) 0)
                 ;;     (true)
                 ;;     (>= (* k (- (negate sum) 1)) 0))
                 (log-push-negate-into-sum expr (list* 2 1 1 (if-test-index)))
                 (log-push-multiplier-in k nexpr (list* 1 1 (if-test-index)))
                 ;; (if (>= (+ -ksum -n) 0)
                 ;;     (true)
                 ;;     (>= (* k (- (negate sum) 1)) 0))
                 (log-use-axiom-as-rewrite
                  `(+ ,nkexpr ,(- n)) '+.commutes
                  `((= |)X| ,nkexpr) (= |)Y| ,(- n))) (cons 1 (if-test-index)))
                 (log-use-axiom-as-rewrite
                  `(+ ,(- n) ,nkexpr) '+.associate.left
                  `((= |)X| ,(- n)) (= |)Y| ,(second nkexpr))
		    (= |)Z| ,(third nkexpr)))
                  (cons 1 (if-test-index)))
                 (push-proof-log 'compute (list* 1 1 (if-test-index)))
                 ;; (if (>= xsum 0) (true) (>= (* k (- (negate sum) 1)) 0))
                 (log-justify-triples
                  (k-times-sum-minus-n (- k) n sum) triples (if-test-index))
                 (push-proof-log 'if-true index))
                (t
                 (log-inconsistent-restrictions-n-<-k
                  k n `(negate ,expr) index)
                 ;; (>= (+ -n (* k (negate sum))) 0)
                 (log-push-negate-into-sum expr (list* 2 2 1 index))
                 (log-push-multiplier-in k nexpr (list* 2 1 index))
                 ;; (>= (+ -n -ksum) 0)
                 (log-use-axiom-as-rewrite
                  `(+ ,(- n) ,nkexpr) '+.associate.left
                  `((= |)X| ,(- n)) (= |)Y| ,(second nkexpr))
		    (= |)Z| ,(third nkexpr)))
		  (cons 1 index))
                 (push-proof-log 'compute (list* 1 1 index))
                 ;; (>= xsum 0)
                 (log-justify-triples
                  (k-times-sum-minus-n (- k) n sum) triples index)))))))))



;;; Log transformation of (>= (negate sum) 1) to (false) based on the
;;; fact that (>= sum 0) is equivalent to (true).

(defun log-inconsistent-restrictions-restrict (expr justification index)
  ;; (>= (negate sum) 1)
  (log-use-axiom-as-rewrite
   `(>= (negate ,expr) 1) 'inconsistent.restrictions `((= |)X| ,expr)) index)
  ;; (if (>= sum 0) (false) (>= (negate sum) 1))
  (log-justify-restriction-aux justification (if-test-index))
  (push-proof-log 'if-true index))

;;; Log transformation of (>= (negate sum) 1) to (false) based on the
;;; fact that (= sum 0) is equivalent to (true).

(defun log-inconsistent-restrictions-kill (expr justification index)
  ;; (>= (negate sum) 1)
  (push-proof-log 'if-equal (list* 1 1 index) `(= ,expr 0) t)
  ;; (>= (negate (if (= sum 0) sum sum)) 1)
  (push-proof-log 'look-up (list* 2 1 1 index) 0)
  (log-justify-killed-aux justification (list* 1 1 1 index))
  ;; (>= (negate (if (true) 0 sum)) 1)
  (push-proof-log 'if-true (list* 1 1 index))
  (push-proof-log 'compute (cons 1 index))
  (push-proof-log 'compute index))



;;; Log transformation of (>= (* k (- expr 1)) 0) to
;;; (if (>= (+ (* k expr) -n) 0) (true) (>= (* k (- expr 1)) 0))
;;; where n and k are integer literals and n >= k > 0.

(defun log-inconsistent-restrictions-n->=-k (k n expr index)
  ;; (>= (* k (- expr 1)) 0)
  (log-use-axiom index 'inequality.lemma)
  (let ((event (get-event 'inequality.lemma)))
    (log-rewrite (make-if (make-series-of-quantification
                           'all (axiom-args event) (axiom-formula event))
                          `(>= (* ,k (- ,expr 1)) 0)
                          *true*)
                 `((= ,(first (axiom-args event)) (* ,k (- ,expr 1)))
                   (= ,(second (axiom-args event)) ,(- n k)))
                 index)
    (push-proof-log 'use-axiom (if-test-index) 'inequality.lemma t)
    (push-proof-log 'if-true index)
    ;; (if (= (type-of (* k (- expr 1))) (int))
    ;;     (if (>= n-k 0)
    ;;         (if (>= (- (* k (- expr 1)) n-k) 0)
    ;;             (true)
    ;;             (>= (* k (- expr 1)) 0))
    ;;         (>= (* k (- expr 1)) 0))
    ;;     (>= (* k (- expr 1)) 0))
    (log-type-of-expr `(* ,k (- ,expr 1)) (cons 1 (if-test-index)))
    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)
    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)
    ;; (if (>= (- (* k (- expr 1)) n-k) 0)
    ;;     (true)
    ;;     (>= (* k (- expr 1)) 0))
    (log-use-axiom-as-rewrite
     `(- ,expr 1) '-.times.minus.1.right `((= |)X| ,expr) (= |)Y| 1))
     (list* 2 1 1 (if-test-index)))
    (push-proof-log 'compute (list* 2 2 1 1 (if-test-index)))
    ;; (if (>= (- (* k (+ expr -1)) n-k) 0)
    ;;     (true)
    ;;     (>= (* k (- expr 1)) 0))
    (log-use-axiom-as-rewrite
     `(* ,k (+ ,expr -1)) '*.distribute.+.right
     `((= |)X| ,k) (= |)Y| ,expr) (= |)Z| -1)) (list* 1 1 (if-test-index)))
    (push-proof-log 'compute (list* 2 1 1 (if-test-index)))
    ;; (if (>= (- (+ (* k expr) -k) n-k) 0)
    ;;     (true)
    ;;     (>= (* k (- expr 1)) 0))
    (log-use-axiom-as-rewrite
     `(- (+ (* ,k ,expr) ,(- k)) ,(- n k)) '-.times.minus.1.right
     `((= |)X| (+ (* ,k ,expr) ,(- k))) (= |)Y| ,(- n k)))
     (cons 1 (if-test-index)))
    ;; (if (>= (+ (+ (* k expr) -k) (* -1 n-k)) 0)
    ;;     (true)
    ;;     (>= (* k (- expr 1)) 0))
    (push-proof-log 'compute (list* 2 1 (if-test-index)))
    ;; (if (>= (+ (+ (* k expr) -k) k-n) 0)
    ;;     (true)
    ;;     (>= (* k (- expr 1)) 0))
    (log-use-axiom-as-rewrite
     `(+ (+ (* ,k ,expr) ,(- k)) ,(- k n)) '+.associate.right
     `((= |)X| (* ,k ,expr)) (= |)Y| ,(- k)) (= |)Z| ,(- k n)))
     (cons 1 (if-test-index)))
    (push-proof-log 'compute (list* 2 1 (if-test-index)))
    ;; (if (>= (+ (* k expr) -n) 0)
    ;;     (true)
    ;;     (>= (* k (- expr 1)) 0))
    ))



;;; Log conversion of (>= (* k (- expr 1)) 0) to (>= (+ -n (* k expr)) 0)
;;; where n and k are integer literals and 0 < n < k.

(defun log-inconsistent-restrictions-n-<-k (k n expr index)
  ;; (>= (* k (- expr 1)) 0)
  (push-proof-log 'if-equal index
		  `(= (>= (* ,k (- ,expr 1)) 0)
		      (>= (+ ,(- k n) (* ,k (- ,expr 1))) 0))
		  t)
  (push-proof-log 'look-up (if-left-index)
                  `(>= (+ ,(- k n) (* ,k (- ,expr 1))) 0))
  ;; (if (= (>= (* k (- expr 1)) 0) (>= (+ k-n (* k (- expr 1))) 0))
  ;;     (>= (+ k-n (* k (- expr 1))) 0)
  ;;     (>= (* k (- expr 1)) 0))
  (log-use-axiom-as-rewrite
   `(>= (+ ,(- k n) (* ,k (- ,expr 1))) 0) 'normalize.>=
   `((= |)X| ,(- k n)) (= |)Y| ,k) (= |)Z| (- ,expr 1)))
   (cons 2 (if-test-index)))
  ;; (if (= (>= (* k (- expr 1)) 0)
  ;;        (if (>= k-n 0)
  ;;            (if (>= k (+ k-n 1))
  ;;                (if (= (type-of (- expr 1)) (int))
  ;;                    (>= (- expr 1) 0)
  ;;                    (>= (+ k-n (* k (- expr 1))) 0))
  ;;                (>= (+ k-n (* k (- expr 1))) 0))
  ;;            (>= (+ k-n (* k (- expr 1))) 0)))
  ;;     (>= (+ k-n (* k (- expr 1))) 0)
  ;;     (>= (* k (- expr 1)) 0))
  (push-proof-log 'compute (list* 1 2 (if-test-index)))
  (push-proof-log 'if-true (cons 2 (if-test-index)))
  (push-proof-log 'compute (list* 2 1 2 (if-test-index)))
  (push-proof-log 'compute (list* 1 2 (if-test-index)))
  (push-proof-log 'if-true (cons 2 (if-test-index)))
  (log-type-of-expr `(- ,expr 1) (list* 1 1 2 (if-test-index)))
  (push-proof-log 'compute (list* 1 2 (if-test-index)))
  (push-proof-log 'if-true (cons 2 (if-test-index)))
  ;; (if (= (>= (* k (- expr 1)) 0)
  ;;        (>= (- expr 1) 0))
  ;;     (>= (+ k-n (* k (- expr 1))) 0)
  ;;     (>= (* k (- expr 1)) 0))
  (log-use-axiom-as-rewrite
   `(>= (* ,k (- ,expr 1)) 0) '*.>=.zero.>=.one.left
   `((= |)X| ,k) (= |)Y| (- ,expr 1))) (cons 1 (if-test-index)))
  (push-proof-log 'compute (list* 1 1 (if-test-index)))
  (push-proof-log 'if-true (cons 1 (if-test-index)))
  ;; (if (= (if (= (type-of (- expr 1)) (int))
  ;;            (>= (- expr 1) 0)
  ;;            (>= (* k (- expr 1)) 0))
  ;;        (>= (- expr 1) 0))
  ;;     (>= (+ k-n (* k (- expr 1))) 0)
  ;;     (>= (* k (- expr 1)) 0))
  (log-type-of-expr `(- ,expr 1) (list* 1 1 1 (if-test-index)))
  (push-proof-log 'compute (list* 1 1 (if-test-index)))
  (push-proof-log 'if-true (cons 1 (if-test-index)))
  ;; (if (= (>= (- expr 1) 0) (>= (- expr 1) 0))
  ;;     (>= (+ k-n (* k (- expr 1))) 0)
  ;;     (>= (* k (- expr 1)) 0))
  (push-proof-log 'compute (if-test-index))
  (push-proof-log 'if-true index)
  ;; (>= (+ k-n (* k (- expr 1))) 0)
  (log-use-axiom-as-rewrite
     `(- ,expr 1) '-.times.minus.1.right `((= |)X| ,expr) (= |)Y| 1))
     (list* 2 2 1 index))
  (push-proof-log 'compute (list* 2 2 2 1 index))
  ;; (>= (+ k-n (* k (+ expr -1))) 0)
  (log-use-axiom-as-rewrite
   `(* ,k (+ ,expr -1)) '*.distribute.+.right
   `((= |)X| ,k) (= |)Y| ,expr) (= |)Z| -1)) (list* 2 1 index))
  (push-proof-log 'compute (list* 2 2 1 index))
  ;; (>= (+ k-n (+ (* k expr) -k)) 0)
  (log-use-axiom-as-rewrite
   `(+ (* ,k ,expr) ,(- k)) '+.commutes
   `((= |)X| (* ,k ,expr)) (= |)Y| ,(- k))) (list* 2 1 index))
  (log-use-axiom-as-rewrite
   `(+ ,(- k n) (+ ,(- k) (* ,k ,expr))) '+.associate.left
   `((= |)X| ,(- k n)) (= |)Y| ,(- k)) (= |)Z| (* ,k ,expr))) (cons 1 index))
  (push-proof-log 'compute (list* 1 1 index))
  ;; (>= (+ -n (* k expr)) 0)
  )



;;; Log transformation of (false) to (true) based on inconsistent
;;; restrictions where a sum which is being killed is manifestly
;;; minimized at a positive value.

(defun log-inconsistent-restrictions-minimized (justification index)
  (let ((owner (third justification))
        (just1 (fourth justification))
        (just2 (fifth justification)))
    ;; just2 is (minimized owner triples)
    (let* ((sum (sum-of-node (cdr owner) (car owner)))
           (expr (raw-expr-of-sum sum)))
      (push-proof-log 'if-equal index `(= (false) (>= ,expr 1)) t)
      (push-proof-log 'look-up (if-left-index) `(>= ,expr 1))
      ;; (if (= (false) (>= sum 1)) (>= sum 1) (false))
      (push-proof-log 'if-equal (list* 1 2 (if-test-index)) `(= ,expr 0) t)
      ;; (if (= (false) (>= (if (= sum 0) sum sum) 1)) (>= sum 1) (false))
      (push-proof-log 'look-up (list* 2 1 2 (if-test-index))
                      0)
      (log-justify-killed-aux just1 (list* 1 1 2 (if-test-index)))
      ;; (if (= (false) (>= (if (true) 0 sum) 1)) (>= sum 1) (false))
      (push-proof-log 'if-true (list* 1 2 (if-test-index)))
      (push-proof-log 'compute (cons 2 (if-test-index)))
      (push-proof-log 'compute (if-test-index))
      (push-proof-log 'if-true index)
      (cond
       ((integerp expr)
        (push-proof-log 'compute index))
       (t
        ;; (>= sum 1)
        (log-convert->=-to->=-zero expr 1 index)
        ;; (>= (- sum 1) 0)
        (let* ((k (apply #'lcm (mapcar #'(lambda (u) (denominator (car u)))
                                       (third just2))))
               (n (* k (car (car (last (third just2))))))
               (triples (mapcar #'(lambda (u) (cons (* k (car u)) (cdr u)))
                                (third just2)))
               (kexpr (raw-expr-of-sum
                       (multiply-collected-terms-by-constant sum k))))
          (log-multiply->=-zero k `(- ,expr 1) index)
          ;; (>= (* k (- sum 1)) 0)
          (cond ((>= n k)
                 (log-inconsistent-restrictions-n->=-k k n expr index)
                 ;; (if (>= (+ (* k sum) -n) 0) (true) (>= (* k (- sum 1)) 0))
                 (log-push-multiplier-in k expr (list* 1 1 (if-test-index)))
                 ;; (if (>= (+ ksum -n) 0) (true) (>= (* k (- sum 1)) 0))
                 (log-use-axiom-as-rewrite
                  `(+ ,kexpr ,(- n)) '+.commutes
		  `((= |)X| ,kexpr) (= |)Y| ,(- n)))
                  (cons 1 (if-test-index)))
                 (log-use-axiom-as-rewrite
                  `(+ ,(- n) ,kexpr) '+.associate.left
                  `((= |)X| ,(- n)) (= |)Y| ,(second kexpr))
		    (= |)Z| ,(third kexpr)))
                  (cons 1 (if-test-index)))
                 (push-proof-log 'compute (list* 1 1 (if-test-index)))
                 ;; (if (>= xsum 0) (true) (>= (* k (- sum 1)) 0))
                 (log-justify-triples
                  (k-times-sum-minus-n k n sum) triples (if-test-index))
                 (push-proof-log 'if-true index))
                (t
                 (log-inconsistent-restrictions-n-<-k k n expr index)
                 ;; (>= (+ -n (* k sum)) 0)
                 (log-push-multiplier-in k expr (list* 2 1 index))
                 ;; (>= (+ -n ksum) 0)
                 (log-use-axiom-as-rewrite
                  `(+ ,(- n) ,kexpr) '+.associate.left
                  `((= |)X| ,(- n)) (= |)Y| ,(second kexpr))
		    (= |)Z| ,(third kexpr)))
		  (cons 1 index))
                 (push-proof-log 'compute (list* 1 1 index))
                 ;; (>= xsum 0)
                 (log-justify-triples
                  (k-times-sum-minus-n k n sum) triples index)))))))))



;;; Log transformation of (false) to (true) based on unsolvable sum.
;;; The sum belongs to an arithmetic expression and has a constant
;;; non-integer value.
;;; node is the node for the arithmetic expression
;;; i is the tableau index (0, 1, 2, or 3)
;;; value is the non-integer value
;;; justification is the constant justification of the form
;;;   (constant-sum owner triples)

(defun log-non-integer (node i value justification index)
  (let ((sum (sum-of-node node i))
        (triples (third justification)))
    (let* ((k (apply #'lcm (mapcar #'(lambda (u) (denominator (car u)))
                                   triples)))
           (ksum (multiply-collected-terms-by-constant sum k)))
      (let ((kexpr (raw-expr-of-sum ksum))
            (kv (* k value)))
        (push-proof-log 'if-equal index `(= (false) (= ,kexpr ,kv)) t)
        (push-proof-log 'look-up (if-left-index) `(= ,kexpr ,kv))
        ;; (if (= (false) (= ksum kv)) (= ksum kv) (false))
        (log-remove-dead-triples
         ksum
         (mapcar #'(lambda (u) (cons (* k (car u)) (cdr u))) triples)
         (cons 1 (if-left-index)))
        ;; (if (= (false) (= ksum kv)) (= kv kv) (false))
        (push-proof-log 'compute (if-left-index))
        (log-convert-=-to-=-zero kexpr kv (cons 2 (if-test-index)))
        ;; (if (= (false) (= (- ksum kv) 0)) (true) (false))
        (log-use-axiom-as-rewrite
         `(- ,kexpr ,kv) '-.+.left.to.+.-.left
         `((= |)X| ,(second kexpr)) (= |)Y| ,(third kexpr)) (= |)Z| ,kv))
	 (list* 1 2 (if-test-index)))
        (push-proof-log 'compute (list* 1 1 2 (if-test-index)))
        ;; (if (= (false) (= (+ cc rest) 0)) (true) (false))
        (log-non-integer-aux
         k (- (second kexpr) kv) (third kexpr)
         (cons (- (second kexpr) kv) (cdr ksum)) (cons 2 (if-test-index)))
        ;; (if (= (false) (false)) (true) (false))
        (push-proof-log 'compute (if-test-index))
        (push-proof-log 'if-true index)))))

(defun log-non-integer-aux (k cc rest sum index)
  ;; (= sum 0)
  (let ((expr `(+ ,cc ,rest)))
    (log-use-axiom-as-rewrite
     `(= ,expr 0) '=.to.>=.and.>=.negate `((= |)X| ,expr)) index)
    ;; (if (>= sum 0) (if (>= (negate sum) 0) (true) (false)) (false))
    (let* ((d (mod cc k))
           (rsum (cons (- cc d) (cdr sum))))
      (log-normalize-inequality k cc d rest rsum (if-test-index))
      ;; (if (>= qsum 0) (if (>= (negate sum) 0) (true) (false)) (false))
      (log-push-negate-into-sum expr (list* 1 1 (if-left-index)))
      ;; (if (>= qsum 0) (if (>= nsum 0) (true) (false)) (false))
      (let* ((cc2 (- cc))
             (d2 (mod cc2 k))
             (expr2 (raw-expr-of-sum (negative-sum sum)))
             (rsum2 (cons (- cc2 d2) (cdr (negative-sum sum)))))
        (log-normalize-inequality
         k cc2 d2 (third expr2) rsum2 (cons 1 (if-left-index)))
        ;; (if (>= qsum 0) (if (>= qsum2 0) (true) (false)) (false))
        (let ((qsum (raw-expr-of-sum
                     (cons (quotient (car rsum) k)
                           (mapcar #'(lambda (u) (cons (car u)
                                                       (quotient (cdr u) k)))
                                   (cdr rsum)))))
              (qsum2 (raw-expr-of-sum
                      (cons (quotient (car rsum2) k)
                            (mapcar #'(lambda (u) (cons (car u)
                                                        (quotient (cdr u) k)))
                                    (cdr rsum2))))))
          (push-proof-log 'if-equal (cons 1 (if-left-index))
                          `(= (>= ,qsum2 0) (>= (negate ,qsum) 1))
			  t)
          (push-proof-log 'look-up (list* 2 1 (if-left-index))
                          `(>= (negate ,qsum) 1))
          ;; (if (>= qsum 0)
          ;;     (if (if (= (>= qsum2 0) (>= (negate qsum) 1))
          ;;             (>= (negate qsum) 1)
          ;;             (>= qsum2 0))
          ;;         (true)
          ;;         (false))
          ;;     (false))
          (log-convert->=-negate-1 qsum (list* 2 1 1 (if-left-index)))
          (push-proof-log 'compute (list* 1 1 (if-left-index)))
          (push-proof-log 'if-true (cons 1 (if-left-index)))
          ;; (if (>= qsum 0) (if (>= (negate qsum) 1) (true) (false)) (false))
          (log-use-axiom-as-rewrite
           `(>= (negate ,qsum) 1) 'inconsistent.restrictions `((= |)X| ,qsum))
           (cons 1 (if-left-index)))
          ;; (if (>= qsum 0)
          ;;     (if (if (>= qsum 0) (false) (>= (negate qsum) 0))
          ;;         (true)
          ;;         (false))
          ;;     (false))
          (push-proof-log 'look-up (list* 1 1 (if-left-index)) *true*)
          (push-proof-log 'if-true (cons 1 (if-left-index)))
          (push-proof-log 'if-false (if-left-index))
          ;; (if (>= qsum 0) (false) (false))
          (push-proof-log 'if-equal index))))))



;;; Code to log conversion of (if (= x1 x2) (false) (true)) to (true).

(defun log-forbid (node1 node2 index)
  (log-forbid-aux
   node1 node2 (get-forbid-justification node1 node2) index))

;;; Given node1 and node2 that are forbidden against each other,
;;; get the justification for the forbid.

(defun get-forbid-justification (u v)
  (let ((v-root (e-node-root v))
        (p (e-node-forbid (e-node-root u))))
    (cond ((eq (e-node-root (fnode-enode p)) v-root)
           (fnode-justification p))
          (t
           (do ((plink (fnode-link p) (fnode-link plink)))
               ((eq (fnode-link plink) plink)
                (when (eq (e-node-root (fnode-enode plink)) v-root)
                  (fnode-justification plink)))
             (when (eq (e-node-root (fnode-enode plink)) v-root)
               (return (fnode-justification plink))))))))



;;; Dispatch to the cases of logging the justification of forbid.

(defun log-forbid-aux (node1 node2 justification index)
  (let ((u (first justification))
        (v (second justification))
        (justification (third justification)))
    (cond ((eq (e-node-root node1) (e-node-root u))
           (log-node-equality node1 u (cons 1 (if-test-index)))
           (log-node-equality node2 v (cons 2 (if-test-index)))
           (setq node1 u)
           (setq node2 v))
          (t
           (log-node-equality node1 v (cons 1 (if-test-index)))
           (log-node-equality node2 u (cons 2 (if-test-index)))
           (setq node1 v)
           (setq node2 u)))
    (cond ((atom justification)
           (case justification
             (bool-not-int
              (log-justify-forbid-bool-not-int node1 index))
             (true-not-false
              (log-justify-forbid-true-not-false node1 index)))
           )
          (t
           (case (car justification)
             (positive
              (log-justify-forbid-positive
               node1 node2 (second justification) index))
             (negative
              (log-justify-forbid-negative
               node1 node2 (second justification) index))
             (=-false
              (log-justify-forbid-=-false
               node1 node2 (second justification) index))
             (type-predicate
              (log-justify-forbid-type-predicate
               node1 node2 (second justification) index))
             (context
              (log-justify-forbid-context
               node1 node2 (second justification) index))
             (deny-if
              (cond ((eq node1 *true-node*)
                     (log-use-axiom-as-rewrite
                      `(= ,(e-node-attribute node1) ,(e-node-attribute node2))
                      '=-commutes
                      `((= |)X| ,(e-node-attribute node1))
			(= |)Y| ,(e-node-attribute node2)))
                      (if-test-index))
                     (log-justify-forbid-from-deny-if
                      node2 (second justification) (third justification)
                      index))
                    (t (log-justify-forbid-from-deny-if
                        node1 (second justification) (third justification)
                        index))))
             (grule
              (log-justify-forbid-grule
               node1 node2 justification index))
             (frule
              (log-justify-forbid-frule
               node1 node2 justification index))
             )
           ))))



;;; Log transformation of (if (= (bool) (int)) (false) (true)) to (true),
;;; or (if (= (int) (bool)) (false) (true)) to (true),
;;; based on the fact that (bool) is forbidden against (char).

(defun log-justify-forbid-bool-not-int (node index)
  (unless (eq node *bool-node*)
    (log-use-axiom-as-rewrite
     '(= (int) (bool)) '=.commutes '((= |)X| (int)) (= |)Y| (bool)))
     (if-test-index)))
  ;; (if (= (bool) (int)) (false) (true))
  (push-proof-log 'use-axiom index 'bool.not.int t))

;;; Log transformation of (if (= (true) (false)) (false) (true)) to (true),
;;; or (if (= (false) (true)) (false) (true)) to (true),
;;; based on the fact that (true) is forbidden against (false).

(defun log-justify-forbid-true-not-false (node index)
  (unless (eq node *true-node*)
    (log-use-axiom-as-rewrite
     '(= (false) (true)) '=.commutes '((= |)X| (false)) (= |)Y| (true)))
     (if-test-index)))
  ;; (if (= (true) (false)) (false) (true))
  (push-proof-log 'use-axiom index 'true.not.false t))



;;; Log transformation of (if (= expr1 expr2) (false) (true)) to (true),
;;; based on the fact that either
;;; expr1 is strictly positive and expr2 is 0 (case 1), or
;;; expr1 is 0 and expr2 is strictly positive (case 2).
;;; node1 is the node for expr1,
;;; node2 is the node for expr2,
;;; node3 is the reference node for the strictly positive expression.

(defun log-justify-forbid-positive (node1 node2 node3 index)
  (unless (eq node1 node3)
    (log-use-axiom-as-rewrite
     `(= ,(e-node-attribute node1) ,(e-node-attribute node2))
     '=.commutes
     `((= |)X| ,(e-node-attribute node1)) (= |)Y| ,(e-node-attribute node2)))
     (if-test-index)))
  ;; (if (= expr 0) (false) (true))
  (push-proof-log 'if-true (if-left-index) *true* t)
  ;; (if (= expr 0) (if (true) (false) (true)) (true))
  (log-justify-restriction-reverse node3 2 (cons 1 (if-left-index)))
  ;; (if (= expr 0) (if (>= sum2 0) (false) (true)) (true))
  (log-collect-terms-reverse
   `(- ,(e-node-attribute node3) 1)
   (raw-expr-of-sum (sum-of-node node3 2))
   (list* 1 1 (if-left-index)))
  ;; (if (= expr 0) (if (>= (- expr 1) 0) (false) (true)) (true))
  (push-proof-log 'look-up (list* 1 1 1 (if-left-index)) 0)
  (push-proof-log 'compute (list* 1 1 (if-left-index)))
  (push-proof-log 'compute (cons 1 (if-left-index)))
  (push-proof-log 'if-false (if-left-index))
  (push-proof-log 'if-equal index))



;;; Log transformation of (if (= expr1 expr2) (false) (true)) to (true),
;;; based on the fact that either
;;; expr1 is strictly negative and expr2 is 0 (case 1), or
;;; expr1 is 0 and expr2 is strictly positive (case 2).
;;; node1 is the node for expr1,
;;; node2 is the node for expr2,
;;; node3 is the reference node for the strictly negative expression.

(defun log-justify-forbid-negative (node1 node2 node3 index)
  (unless (eq node1 node3)
    (log-use-axiom-as-rewrite
     `(= ,(e-node-attribute node1) ,(e-node-attribute node2))
     '=.commutes
     `((= |)X| ,(e-node-attribute node1)) (= |)Y| ,(e-node-attribute node2)))
     (if-test-index)))
  ;; (if (= expr 0) (false) (true))
  (push-proof-log 'if-true (if-left-index) *true* t)
  ;; (if (= expr 0) (if (true) (false) (true)) (true))
  (log-justify-restriction-reverse node3 3 (cons 1 (if-left-index)))
  ;; (if (= expr 0) (if (>= sum3 0) (false) (true)) (true))
  (log-collect-terms-reverse
   `(- (negate ,(e-node-attribute node3)) 1)
   (raw-expr-of-sum (sum-of-node node3 3))
   (list* 1 1 (if-left-index)))
  ;; (if (= expr 0) (if (>= (- (negate expr) 1) 0) (false) (true)) (true))
  (push-proof-log 'look-up (list* 1 1 1 1 (if-left-index)) 0)
  (push-proof-log 'compute (list* 1 1 1 (if-left-index)))
  (push-proof-log 'compute (list* 1 1 (if-left-index)))
  (push-proof-log 'compute (cons 1 (if-left-index)))
  (push-proof-log 'if-false (if-left-index))
  (push-proof-log 'if-equal index))
           


;;; Log conversion of (if (= expr1 expr2) (false) (true)) to (true),
;;; based on the fact that expr1 is forbidden against expr2 because
;;; of a false equality.
;;; node1 is the node for expr1,
;;; node2 is the node for expr2,
;;; node3 is the node for the false equality.

(defun log-justify-forbid-=-false (node1 node2 node3 index)
  ;; (if (= expr1 expr2) (false) (true))
  (unless (eq node1 (arg-1-node node3))
    (log-use-axiom-as-rewrite
     `(= ,(e-node-attribute node1) ,(e-node-attribute node2))
     '=.commutes
     `((= |)X| ,(e-node-attribute node1)) (= |)Y| ,(e-node-attribute node2)))
     (if-test-index)))
  ;; (if (= left right) (false) (true))
  (log-node-equality node3 *false-node* (if-test-index))
  ;; (if (false) (false) (true))
  (push-proof-log 'if-false index)
  ;; (true)
  )
                


;;; Log conversion of (if (= expr1 expr2) (false) (true)) to (true),
;;; based on the fact that (type-of expr) is forbidden against type because
;;; of a false (in expr type), where expr1 is equivalent to (type-of expr)
;;; and expr2 is equivalent to type or expr1 is equivalent to type and
;;; expr2 is equivalent to (type-of expr).
;;; node1 is the node for expr1,
;;; node2 is the node for expr2,
;;; node3 is the node for (in expr type).

(defun log-justify-forbid-type-predicate (node1 node2 node3 index)
  (let ((type-of-expr (e-node-type (arg-1-node node3)))
        (type (arg-2-node node3)))
    ;; (if (= expr1 expr2) (false) (true))
    (unless (eq node1 type-of-expr)
      (log-use-axiom-as-rewrite
       `(= ,(e-node-attribute node1) ,(e-node-attribute node2))
       '=.commutes
       `((= |)X| ,(e-node-attribute node1)) (= |)Y| ,(e-node-attribute node2)))
       (if-test-index)))
    ;; (if (= (type-of expr) type) (false) (true))
    (push-proof-log 'if-equal (if-test-index)
                    `(= (= ,(e-node-attribute type-of-expr)
                           ,(e-node-attribute type))
                        (in ,(e-node-attribute (arg-1-node node3))
                            ,(e-node-attribute type)))
		    t)
    (push-proof-log 'look-up (cons 2 (if-test-index))
                    `(in ,(e-node-attribute (arg-1-node node3))
                         ,(e-node-attribute type)))
    ;; (if (if (= (= (type-of expr) type) (in expr type))
    ;;         (in expr type)
    ;;         (= (type-of expr) type))
    ;;     (false)
    ;;     (true))
    (log-type-of-to-in
     (e-node-attribute (arg-1-node node3))
     (e-node-attribute type) (list* 1 1 (if-test-index)))
    (push-proof-log 'compute (cons 1 (if-test-index)))
    (push-proof-log 'if-true (if-test-index))
    ;; (if (in expr type) (false) (true))
    (log-node-equality node3 *false-node* (if-test-index))
    (push-proof-log 'if-false index)
    ;; (true)
    ))



;;; Log transformation of (= (type-of expr) type) to (in expr type).

(defun log-type-of-to-in (expr type index)
  (push-proof-log
   'if-equal index `(= (= (type-of ,expr) ,type) (in ,expr ,type)) t)
  (push-proof-log 'look-up (if-left-index) `(in ,expr ,type))
  ;; (if (= (= (type-of expr) type) (in expr type))
  ;;     (in expr type)
  ;;     (= (type-of expr) type))
  (log-in-to-type-of expr type (cons 2 (if-test-index)))
  ;; (if (= (= (type-of expr) type) (= (type-of expr) type))
  ;;     (in expr type)
  ;;     (= (type-of expr) type))
  (push-proof-log 'compute (if-test-index))
  (push-proof-log 'if-true index)
  ;; (in expr type)
  )

;;; Log transformation of (in expr type) to (= (type-of expr) type).

(defun log-in-to-type-of (expr type index)
  (log-use-axiom-as-rewrite
   `(in ,expr ,type) 'type-of.definition.internal
   `((= |)X| ,expr) (= |)Y| ,type)) index)
  ;; (if (if (= type (bool)) (true) (if (= type (int)) (true) (false)))
  ;;     (= (type-of expr) type)
  ;;     (in expr type))
  (cond ((equal type '(bool))
	 (push-proof-log 'compute (cons 1 (if-test-index)))
	 (push-proof-log 'if-true (if-test-index)))
        ((equal type '(int))
         (push-proof-log 'compute (list* 1 3 (if-test-index)))
	 (push-proof-log 'if-true (cons 3 (if-test-index)))
	 (push-proof-log 'if-equal (if-test-index))))
  (push-proof-log 'if-true index))



;;; Log conversion of (if (= expr1 expr2) (false) (true)) to (true),
;;; based on the fact that expr is forbidden against (true) because
;;; of context (i.e., (if expr (false) (true)) is in the context),
;;; where expr1 is equivalent to expr and expr2 is equivalent to (true)
;;; or expr1 is equivalent to (true) and expr2 is equivalent to expr.
;;; node1 is the node for expr1,
;;; node2 is the node for expr2,
;;; node3 is the node for expr.

(defun log-justify-forbid-context (node1 node2 node3 index)
  (when (eq node1 *true-node*)
    (log-use-axiom-as-rewrite
     `(= ,(e-node-attribute node1) ,(e-node-attribute node2))
     '=.commutes
     `((= |)X| ,(e-node-attribute node1)) (= |)Y| ,(e-node-attribute node2)))
     (if-test-index)))
  ;; (if (= expr (true)) (false) (true))
  (push-proof-log 'if-test index t)
  ;; (log-convert-test-from-equal-true
  ;;  (e-node-attribute node3) *false* *true* index)
  ;; (if expr (false) (true))
  (push-proof-log 'look-up index *true*)
  )



;;; Log conversion of (if (= expr1 expr2) (false) (true)) to (true),
;;; based on the fact that expr is forbidden against (true) as a
;;; result of an application of a grule (i.e., (if expr (false) (true))
;;; is the grule conclusion).
;;; expr1 is equivalent to expr and expr2 is equivalent to (true)
;;; or expr1 is equivalent to (true) and expr2 is equivalent to expr.
;;; node1 is the node for expr1,
;;; node2 is the node for expr2.

(defun log-justify-forbid-grule (node1 node2 justification index)
  (let ((node3 (second justification))
        (grule (third justification))
        (subst (fourth justification))
        (results (fifth justification)))
    (unless (eq node2 *true-node*)
      (log-use-axiom-as-rewrite
       `(= ,(e-node-attribute node1) ,(e-node-attribute node2))
       '=.commutes
       `((= |)X| ,(e-node-attribute node1)) (= |)Y| ,(e-node-attribute node2)))
       (if-test-index)))
    ;; (if (= expr (true)) (false) (true))
    (push-proof-log 'if-test index t)
    ;; (log-convert-test-from-equal-true
    ;;  (e-node-attribute node3) *false* *true* index)
    ;; (if expr (false) (true))
    (let ((axiom-name (intern (string-append (event-name grule) ".INTERNAL")
			      *zk-package*))
          (renames (grule-renames grule)))
      (log-use-axiom index axiom-name)
      ;; (if axiom (if expr (false) (true)) (true))
      (log-renames renames (if-test-index))
      (linearize-and-log-universal-instantiations
       (mapcar #'(lambda (u) (make-= (cdr u) (binding-of (cdr u) subst)))
               renames)
       (if-test-index))
      ;; (if (if axiom-inst renamed-axiom (false))
      ;;     (if expr (false) (true))
      ;;     (true))
      (log-renames (mapcar #'(lambda (u) (cons (cdr u) (car u))) renames)
                   (cons 2 (if-test-index)))
      (cond ((null renames)
	     (when (grule-subgoals grule)
	       (log-discharge-grule-subgoals
		(grule-subgoals grule) subst results (list* 1 (if-test-index)))
	       (push-proof-log 'if-true (if-test-index)))
	     ;; (if expr expr (true))
	     (push-proof-log 'look-up (if-left-index) *true*)
	     ;; (if expr (true) (true))
	     (push-proof-log 'if-equal index))
	    (t
	     (push-proof-log 'use-axiom
			     (cons 2 (if-test-index)) axiom-name t)
	     (when (grule-subgoals grule)
	       (log-discharge-grule-subgoals
		(grule-subgoals grule) subst results
                (list* 1 1 (if-test-index)))
	       (push-proof-log 'if-true (cons 1 (if-test-index))))
	     ;; (if (if expr (true) (false)) expr (true))
	     (push-proof-log 'case-analysis index 1)
	     ;; (if expr
	     ;;     (if (true) expr (true))
	     ;;     (if (false) expr (true)))
	     (push-proof-log 'if-true (if-left-index))
	     (push-proof-log 'look-up (if-left-index) *true*)
	     (push-proof-log 'if-false (if-right-index))
	     ;; (if expr (true) (true))
	     (push-proof-log 'if-equal index)))))
  )



;;; Log discharging of grule subgoals.
;;; The conjunction of subgoals is of the form:
;;; (if goal1 (if goal2 ... (if goaln (true) (false)) ... (false)) (false))
;;; Each goal is either expr or (if expr (false) (true)) depending on
;;; whether it is negated or not.
;;; The formula is transformed to (true).

(defun log-discharge-grule-subgoals (subgoals subst results index)
  (cond ((= (length subgoals) 1)
         (let* ((subgoal (car subgoals))
                (expr (sublis-eq subst (first subgoal)))
                (node (intern-subexpression expr))
                (result (car results)))
           (cond ((second subgoal)
                  ;; (if expr (false) (true))
                  (cond ((eq result 'false-var)
                         (push-proof-log 'if-false index))
                        (t
			 (push-proof-log 'if-test index)
                         ;; (log-convert-test-to-equal-true expr index)
                         ;; (if (= expr (true)) (false) (true))
                         (log-forbid-aux node *true-node* (third result)
                                         index))))
                 (t
                  ;; expr
                  (log-node-equality node *true-node* index)))))
        (t
         (loop for subgoal in subgoals
               for result in results
               do (let* ((expr (sublis-eq subst (first subgoal)))
                         (node (intern-subexpression expr)))
                    (cond ((second subgoal)
                           ;; (if (if expr (false) (true)) rest (false))
                           (cond ((eq result 'false-var)
                                  (push-proof-log 'if-false (if-test-index)))
                                 (t
				  (push-proof-log 'if-test (if-test-index))
                                  ;; (log-convert-test-to-equal-true
                                  ;;  expr (if-test-index))
                                  ;; (if (if (= expr (true)) (false) (true))
                                  ;;     rest
                                  ;;     (false))
                                  (log-forbid-aux
                                   node *true-node* (third result)
                                   (if-test-index))))
                           (push-proof-log 'if-true index)
                           ;; rest
                           )
                          (t
                           ;; (if expr rest (false))
                           (log-node-equality node *true-node* (if-test-index))
                           (push-proof-log 'if-true index)
                           ;; rest
                           ))))))
  ;; (true)
  )



;;; Log conversion of (if (= expr1 expr2) (false) (true)) to (true),
;;; based on the fact that expr is forbidden against (true) as a
;;; result of an application of a frule (i.e., (if expr (false) (true))
;;; is the frule conclusion).
;;; expr1 is equivalent to expr and expr2 is equivalent to (true)
;;; or expr1 is equivalent to (true) and expr2 is equivalent to expr.
;;; node1 is the node for expr1,
;;; node2 is the node for expr2.

(defun log-justify-forbid-frule (node1 node2 justification index)
  (let ((cond-node (second justification))
        (node3 (third justification))
        (frule (fourth justification))
        (i (fifth justification))
        (subst (sixth justification))
        (just (seventh justification)))
    (unless (eq node2 *true-node*)
      (log-use-axiom-as-rewrite
       `(= ,(e-node-attribute node1) ,(e-node-attribute node2))
       '=.commutes
       `((= |)X| ,(e-node-attribute node1)) (= |)Y| ,(e-node-attribute node2)))
       (if-test-index)))
    ;; (if (= expr (true)) (false) (true))
    (push-proof-log 'if-test index t)
    ;; (log-convert-test-from-equal-true
    ;;  (e-node-attribute node3) *false* *true* index)
    ;; (if expr (false) (true))
    (let ((axiom-name (intern (string-append (event-name frule) ".INTERNAL")
			      *zk-package*))
          (renames (frule-renames frule)))
      (log-use-axiom index axiom-name)
      ;; (if axiom (if expr (false) (true)))
      (log-renames renames (if-test-index))
      (linearize-and-log-universal-instantiations
       (mapcar #'(lambda (u) (make-= (cdr u) (binding-of (cdr u) subst)))
               renames)
       (if-test-index))
      ;; (if (if axiom-inst renamed-axiom (false))
      ;;     (if expr (false) (true))
      ;;     (true))
      (log-renames (mapcar #'(lambda (u) (cons (cdr u) (car u))) renames)
                   (cons 2 (if-test-index)))
      (cond
       ((null renames)
        ;; (if axiom (if expr (false) (true)) (true))
        (log-discharge-frule-condition
         cond-node (frule-negate frule) just (list* 1 (if-test-index)))
        (push-proof-log 'if-true (if-test-index))
        ;; (if concl (if expr (false) (true)) (true))
        (cond ((= (length (frule-values frule)) 1)
               ;; (if (if expr (false) (true)) (if expr (false) (true)) (true))
               (push-proof-log 'look-up (if-left-index) *true*)
               (push-proof-log 'if-equal index))
              (t (log-justify-forbid-frule-aux-aux i (if-test-index))
                 ;; (if (false) (if expr (false) (true)) (true))
                 (push-proof-log 'if-false index)))
        )
       (t
        (push-proof-log 'use-axiom (cons 2 (if-test-index)) axiom-name t)
        ;; (if (if (if cond concl (true)) (true) (false))
        ;;     (if expr (false) (true))
        ;;     (true))
        (log-discharge-frule-condition
         cond-node (frule-negate frule) just (list* 1 1 (if-test-index)))
        (push-proof-log 'if-true (cons 1 (if-test-index)))
        ;; (if (if concl (true) (false)) (if expr (false) (true)) (true))
        (cond ((= (length (frule-values frule)) 1)
               ;; (if (if (if expr (false) (true)) (true) (false))
               ;;     (if expr (false) (true))
               ;;     (true))
               (push-proof-log 'case-analysis index 1)
               ;; (if (if expr (false) (true))
               ;;     (if (true) (if expr (false) (true)) (true))
               ;;     (if (false) (if expr (false) (true)) (true)))
               (push-proof-log 'if-true (if-left-index))
               (push-proof-log 'if-false (if-right-index))
               ;; (if (if expr (false) (true))
               ;;     (if expr (false) (true))
               ;;     (true))
               (push-proof-log 'look-up (if-left-index) *true*)
               (push-proof-log 'if-equal index))
              (t (log-justify-forbid-frule-aux
                  (e-node-attribute node3) i index)))))))
  )



;;; Log transformation-of cond to (true), where cond is either
;;; (if expr (false) (true)) or expr depending on whether or not
;;; negate is non-nil, node is the node for expr.

(defun log-discharge-frule-condition (node negate just index)
  (cond (negate
         ;; (if expr (false) (true))
	 (push-proof-log 'if-test index)
         ;; (log-convert-test-to-equal-true (e-node-attribute node) index)
         ;; (if (= expr (true)) (false) (true))
         (log-forbid-aux node *true-node* just index))
        (t
         ;; expr
         (log-node-equality node *true-node* index))))

;;; concl is of the form:
;;; (if c1 (if c2 .... (if cn (true) (false)) ... (false)) (false))

(defun log-justify-forbid-frule-aux (expr i index)
  ;; (if (if concl (true) (false)) (if expr (false) (true)) (true))
  (push-proof-log 'if-equal index expr t)
  (push-proof-log 'look-up (cons 2 (if-right-index)) *true*)
  (push-proof-log 'if-equal (if-right-index))
  ;; (if expr
  ;;     (if (if concl (true) (false)) (if expr (false) (true)) (true))
  ;;     (true))
  (log-justify-forbid-frule-aux-aux i (list* 1 1 (if-left-index)))
  ;; (if expr
  ;;     (if (if (false) (true) (false)) (if expr (false) (true)) (true))
  ;;     (true))
  (push-proof-log 'if-false (cons 1 (if-left-index)))
  (push-proof-log 'if-false (if-left-index))
  ;; (if expr (true) (true))
  (push-proof-log 'if-equal index))

(defun log-justify-forbid-frule-aux-aux (i index)
  (cond ((= i 0)
         ;; (if (if expr (false) (true)) rest (false))
         (push-proof-log 'look-up (cons 1 (if-test-index)) *true*)
         (push-proof-log 'if-true (if-test-index))
         (push-proof-log 'if-false index)
         ;; (false)
         )
        (t
         ;; (if ci rest (false))
         (log-justify-forbid-frule-aux-aux (- i 1) (if-left-index))
         ;; (if ci (false) (false))
         (push-proof-log 'if-equal index)
         ;; (false)
         )))



;;; log-node-equality logs the transformation of the expression of
;;; the first node to the expression of the second node based on the
;;; fact that the nodes are in the same equivalence class.

(defun log-node-equality (node1 node2 index)
  (let ((common (lowest-common-ancestor node2 (witness-chain-to-root node1))))
    (log-chain node1 common index)
    (log-chain-reverse node2 common index)))

(defun witness-chain-to-root (node)
  (cond ((null (e-node-witness-link node)) (list node))
        ((eq node (e-node-root node)) (list node))
        (t (cons node (witness-chain-to-root (e-node-witness-link node))))))

(defun lowest-common-ancestor (node chain)
  (cond ((member-eq node chain) node)
        (t (lowest-common-ancestor (e-node-witness-link node) chain))))

(defun log-chain (node1 node2 index)
  (loop for next = node1 then (e-node-witness-link next)
        while (not (eq next node2))
        do (log-equality-step next index)))

(defun log-chain-reverse (node1 node2 index)
  (let ((collected nil))
    (loop for next = node1 then (e-node-witness-link next)
          while (not (eq next node2))
          do (push next collected))
    (dolist (next collected) (log-equality-step-reverse next index))))



(defun log-equality-step (node index)
  (log-equality-step-aux
   node (e-node-witness-link node) (e-node-witness-info node) index))

(defun log-equality-step-reverse (node index)
  (log-equality-step-aux
   (e-node-witness-link node) node (e-node-witness-info node) index))

(defun log-equality-step-aux (node1 node2 justification index)
  (cond ((atom justification)
         (case justification
           (context
            (cond ((eq node1 *true-node*)
                   (push-proof-log
                    'if-equal index (make-= (e-node-attribute node2) *true*) t)
                   ;; (if (= expr (true)) (true) (true))
                   (push-proof-log 'look-up (if-left-index)
                                   (e-node-attribute node2))
                   (push-proof-log 'look-up (cons 1 (if-test-index)) *true*)
                   (push-proof-log 'compute (if-test-index))
                   (push-proof-log 'if-true index))
                  (t (push-proof-log 'look-up index *true*))))
           (contradict
            (cond ((or (eq node1 *false-node*) (eq node1 *true-node*))
                   (push-proof-log 'look-up index
                                   (e-node-attribute node2)))
                  ((eq node2 *false-node*)
                   (push-proof-log 'look-up index *false*))
                  ((eq node2 *true-node*)
                   (push-proof-log 'look-up index *true*))))
           (congruence
            (loop for node11 in (arg-nodes node1)
                  for node12 in (arg-nodes node2)
                  for i = 1 then (+ i 1)
                  do (log-node-equality node11 node12 (cons i index))))
           (debruijn (log-debruijn-form (e-node-attribute node1)
                                        (e-node-attribute node2)
                                        index))
           (anti-symmetric (log-justify-anti-symmetric node1 node2 index))
           (type-of (log-type-of node1 node2 index))
           (ord-int (log-justify-ord-int node1 node2 index))
           (true-is-bool (log-justify-true-is-bool node1 node2 index))
           (false-is-bool (log-justify-false-is-bool node1 node2 index))
           (zero-is-int (log-justify-zero-is-int node1 node2 index))
           (one-is-int (log-justify-one-is-int node1 node2 index))
           (=-equal-arguments
            (log-justify-=-equal-arguments node1 node2 index))
           (times-zero-left (log-justify-times-zero-left node1 node2 index))
           (times-zero-right (log-justify-times-zero-right node1 node2 index))
           (same-sum (log-justify-same-sum node1 node2 index))
           (restrict (log-justify-restrict node1 node2 index))
           (>=-reflexive (log-justify->=-reflexive node1 node2 index))
           
         )
         )
        (t
         (case (car justification)
           (assume-if
            (cond ((eq node1 *true-node*)
                   (push-proof-log
                    'if-equal index (make-= (e-node-attribute node2) *true*) t)
                   ;; (if (= expr (true)) (true) (true))
                   (push-proof-log 'look-up (if-left-index)
                                   (e-node-attribute node2))
                   (log-justify-from-assume-if
                    node2 (second justification) (third justification)
                    (cons 1 (if-test-index)))
                   ;; (if (= (true) (true)) expr (true))
                   (push-proof-log 'compute (if-test-index))
                   (push-proof-log 'if-true index))
                  (t (log-justify-from-assume-if
                      node1 (second justification) (third justification)
                      index))))
           (=-true (log-justify-equal-from-=-true
                    node1 node2 (second justification) index))
           (zero (log-justify-zero node1 node2 (second justification) index))
           (square-zero
            (log-justify-square-zero node1 node2 (second justification) index))
           (zero-sum
            (log-justify-zero-sum node1 node2 (second justification) index))
           (=-sums
            (log-justify-equal-from-=-sums node1 node2 justification index))
           (grule
            (log-justify-equal-from-grule node1 node2 justification index))
           (frule
            (log-justify-equal-from-frule node1 node2 justification index))
           (in-=-type-of (log-justify-in-=-type-of
                          node1 node2 (second justification) index))
           (forbid-true (log-justify-forbid-true
                         node1 node2 (second justification) index))
           (forbid-false (log-justify-forbid-false
                          node1 node2 (second justification) index))
           (=-forbid-arguments
            (log-justify-=-forbid-arguments
             node1 node2 (second justification) index))
           (forbid-zero
            (log-justify-forbid-zero node1 node2 (second justification) index))
           (product-zero-left
            (log-justify-product-zero-left
             node1 node2 (second justification) (third justification) index))
           (product-zero-right
            (log-justify-product-zero-right
             node1 node2 (second justification) (third justification) index))
           (strict
            (log-justify-strict node1 node2 (second justification) index))
           (=-constant (log-justify-=-constant
                        node1 node2 (second justification)
                        (third justification) index))
           (>=-constant (log-justify->=-constant
                         node1 node2 (second justification)
                         (third justification) index))
           (integer
            (log-justify-integer node1 node2 (second justification) index))
           (=-no-integer-solution
            (log-justify-no-integer-solution
             node1 node2 (second justification) index))
           (if-true
            (log-justify-if-true node1 node2 (second justification) index))
           (if-false
            (log-justify-if-false node1 node2 (second justification) index))
           (if-equal
            (log-justify-if-equal node1 node2 (second justification) index))

           )
        )))



;;; Log transformation of expr to (false) or (false) to expr,
;;; where expr is forbidden against (true) and is boolean.

(defun log-justify-forbid-true (node1 node2 justification index)
  (cond ((eq node1 *false-node*)
         ;; (false) -> expr1
         (let ((expr (e-node-attribute node2)))
           (push-proof-log 'if-equal index `(= (false) ,expr) t)
           (push-proof-log 'look-up (if-left-index) expr)
           (log-use-axiom-as-rewrite
            `(= (false) ,expr) '=.commutes
	    `((= |)X| (false)) (= |)Y| ,expr)) (if-test-index))
           ;; (if (= expr (false)) expr (false))
           (push-proof-log 'if-false (if-test-index) *true* t)
           ;; (if (if (false) (true) (= expr (false))) expr (false))
           (log-justify-forbid-true-aux
            node2 justification (cons 1 (if-test-index)))
           ;; (if (if (= expr (true)) (true) (= expr (false))) expr (false))
           (log-use-bool-definition expr (if-test-index) t)
           ;; (if (= (type-of expr) (bool)) expr (false))
           (log-node-equality (e-node-type node2) *bool-node*
                              (cons 1 (if-test-index)))
           (push-proof-log 'compute (if-test-index))
           (push-proof-log 'if-true index)))
        (t
         ;; expr -> (false)
         (let ((expr (e-node-attribute node1)))
           (push-proof-log 'if-equal index `(= ,expr (false)) t)
           (push-proof-log 'look-up (if-left-index) *false*)
           ;; (if (= expr (false)) (false) expr)
           (push-proof-log 'if-false (if-test-index) *true* t)
           ;; (if (if (false) (true) (= expr (false))) (false) expr)
           (log-justify-forbid-true-aux
            node1 justification (cons 1 (if-test-index)))
           ;; (if (if (= expr (true)) (true) (= expr (false))) (false) expr)
           (log-use-bool-definition expr (if-test-index) t)
           ;; (if (= (type-of expr) (bool)) (false) expr)
           (log-node-equality (e-node-type node1) *bool-node*
                              (cons 1 (if-test-index)))
           (push-proof-log 'compute (if-test-index))
           (push-proof-log 'if-true index)))))

;;; Log transformation of (false) to (= expr (true)) where expr
;;; is forbidden against (true).
;;; node is for expr.

(defun log-justify-forbid-true-aux (node justification index)
  ;; (false)
  (let ((expr (e-node-attribute node)))
    (push-proof-log 'if-equal index `(= (false) (= ,expr (true))) t)
    (push-proof-log 'look-up (if-left-index) `(= ,expr (true)))
    ;; (if (= (false) (= expr (true))) (= expr (true)) (false))
    (log-convert-boolean-to-coerced
     `(= ,expr (true)) (cons 2 (if-test-index)))
    ;; (if (= (false) (if (= expr (true)) (true) (false)))
    ;;     (= expr (true))
    ;;     (false))
    (push-proof-log 'if-false (list* 2 2 (if-test-index)) *false* t)
    (push-proof-log 'if-true (list* 3 2 (if-test-index)) *true* t)
    ;; (if (= (false)
    ;;        (if (= expr (true))
    ;;            (if (false) (false) (true))
    ;;            (if (true) (false) (true))))
    ;;     (= expr (true))
    ;;     (false))
    (push-proof-log 'case-analysis (cons 2 (if-test-index)) 1 t)
    ;; (if (= (false) (if (if (= expr (true)) (false) (true)) (false) (true)))
    ;;     (= expr (true))
    ;;     (false))
    (log-forbid-aux node *true-node* justification (list* 1 2 (if-test-index)))
    ;; (if (= (false) (if (true) (false) (true))) (= expr (true)) (false))
    (push-proof-log 'if-true (cons 2 (if-test-index)))
    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)))



;;; Log transformation of expr to (true) or (true) to expr,
;;; where expr is forbidden against (false) and is boolean.

(defun log-justify-forbid-false (node1 node2 justification index)
  (cond ((eq node1 *true-node*)
         ;; (true) -> expr1
         (let ((expr (e-node-attribute node2)))
           (push-proof-log 'if-equal index `(= (true) ,expr) t)
           (push-proof-log 'look-up (if-left-index) expr)
           (log-use-axiom-as-rewrite
            `(= (true) ,expr) '=.commutes
	    `((= |)X| (true)) (= |)Y| ,expr)) (if-test-index))
           ;; (if (= expr (true)) expr (true))
           (log-convert-boolean-to-coerced `(= ,expr (true)) (if-test-index))
           ;; (if (if (= expr (true)) (true) (false)) expr (true))
           (log-justify-forbid-false-aux
            node2 justification (cons 3 (if-test-index)))
           ;; (if (if (= expr (true)) (true) (= expr (false))) expr (true))
           (log-use-bool-definition expr (if-test-index) t)
           ;; (if (= (type-of expr) (bool)) expr (true))
           (log-node-equality (e-node-type node2) *bool-node*
                              (cons 1 (if-test-index)))
           (push-proof-log 'compute (if-test-index))
           (push-proof-log 'if-true index)))
        (t
         ;; expr -> (true)
         (let ((expr (e-node-attribute node1)))
           (push-proof-log 'if-equal index `(= ,expr (true)) t)
           (push-proof-log 'look-up (if-left-index) *true*)
           ;; (if (= expr (true)) (true) expr)
           (log-convert-boolean-to-coerced `(= ,expr (true)) (if-test-index))
           ;; (if (if (= expr (true)) (true) (false)) expr (true))
           (log-justify-forbid-false-aux
            node1 justification (cons 3 (if-test-index)))
           ;; (if (if (= expr (true)) (true) (= expr (false))) (true) expr)
           (log-use-bool-definition expr (if-test-index) t)
           ;; (if (= (type-of expr) (bool)) (true) expr)
           (log-node-equality (e-node-type node1) *bool-node*
                              (cons 1 (if-test-index)))
           (push-proof-log 'compute (if-test-index))
           (push-proof-log 'if-true index)))))

;;; Log transformation of (false) to (= expr (false)) where expr
;;; is forbidden against (false).
;;; node is for expr.

(defun log-justify-forbid-false-aux (node justification index)
  ;; (false)
  (let ((expr (e-node-attribute node)))
    (push-proof-log 'if-equal index `(= (false) (= ,expr (false))) t)
    (push-proof-log 'look-up (if-left-index) `(= ,expr (false)))
    ;; (if (= (false) (= expr (false))) (= expr (false)) (false))
    (log-convert-boolean-to-coerced
     `(= ,expr (false)) (cons 2 (if-test-index)))
    ;; (if (= (false) (if (= expr (false)) (true) (false)))
    ;;     (= expr (false))
    ;;     (false))
    (push-proof-log 'if-false (list* 2 2 (if-test-index)) *false* t)
    (push-proof-log 'if-true (list* 3 2 (if-test-index)) *true* t)
    ;; (if (= (false)
    ;;        (if (= expr (false))
    ;;            (if (false) (false) (true))
    ;;            (if (true) (false) (true))))
    ;;     (= expr (false))
    ;;     (false))
    (push-proof-log 'case-analysis (cons 2 (if-test-index)) 1 t)
    ;; (if (= (false) (if (if (= expr (false)) (false) (true)) (false) (true)))
    ;;     (= expr (false))
    ;;     (false))
    (log-forbid-aux
     node *false-node* justification (list* 1 2 (if-test-index)))
    ;; (if (= (false) (if (true) (false) (true))) (= expr (false)) (false))
    (push-proof-log 'if-true (cons 2 (if-test-index)))
    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)))



;;; Log transformation of (= x y) to (true) or (true) to (= x y)
;;; based on the node equality between x and y.

(defun log-justify-=-equal-arguments (node1 node2 index)
  (cond ((eq node1 *true-node*)
         ;; (true) -> (= x y)
         (let ((expr (e-node-attribute node2)))
           (push-proof-log 'if-equal index `(= (true) ,expr) t)
           (push-proof-log 'look-up (if-left-index) expr)
           ;; (if (= (true) (= x y)) (= x y) (true))
           (log-node-equality (arg-1-node node2) (arg-2-node node2)
                              (list* 1 2 (if-test-index)))
           (push-proof-log 'compute (cons 2 (if-test-index)))
           (push-proof-log 'compute (if-test-index))
           (push-proof-log 'if-true index)))
        (t
         ;; (= x y) -> (true)
         (let ((expr (e-node-attribute node1)))
           (push-proof-log 'if-equal index `(= ,expr (true)) t)
           (push-proof-log 'look-up (if-left-index) *true*)
           ;; (if (= (= x y) (true)) (true) (= x y))
           (log-node-equality (arg-1-node node1) (arg-2-node node1)
                              (list* 1 1 (if-test-index)))
           (push-proof-log 'compute (cons 1 (if-test-index)))
           (push-proof-log 'compute (if-test-index))
           (push-proof-log 'if-true index)))))



;;; Log transformation of (= x y) to (false) or (false) to (= x y)
;;; based on the node forbid between x and y.

(defun log-justify-=-forbid-arguments (node1 node2 justification index)
  (cond ((eq node1 *false-node*)
         ;; (false) -> (= x y)
         (let ((expr (e-node-attribute node2)))
           (push-proof-log 'if-equal index `(= (false) ,expr) t)
           (push-proof-log 'look-up (if-left-index) expr)
           ;; (if (= (false) (= x y)) (= x y) (false))
           (log-convert-boolean-to-coerced expr (cons 2 (if-test-index)))
           (log-convert-coerced-to-double-negate (cons 2 (if-test-index)))
           ;; (if (= (false) (if (if (= x y) (false) (true)) (false) (true)))
           ;;     (= x y)
           ;;     (false))
           (log-forbid-aux (arg-1-node node2) (arg-2-node node2) justification
                           (list* 1 2 (if-test-index)))
           (push-proof-log 'if-true (cons 2 (if-test-index)))
           (push-proof-log 'compute (if-test-index))
           (push-proof-log 'if-true index)))
        (t
         ;; (= x y) -> (false)
         (let ((expr (e-node-attribute node1)))
           (push-proof-log 'if-equal index `(= ,expr (false)) t)
           (push-proof-log 'look-up (if-left-index) *false*)
           ;; (if (= (= x y) (false)) (false) (= x y))
           (log-convert-boolean-to-coerced expr (cons 1 (if-test-index)))
           (log-convert-coerced-to-double-negate (cons 1 (if-test-index)))
           ;; (if (= (if (if (= x y) (false) (true)) (false) (true)) (false))
           ;;     (false)
           ;;     (= x y))
           (log-forbid-aux (arg-1-node node1) (arg-2-node node1) justification
                           (list* 1 1 (if-test-index)))
           (push-proof-log 'if-true (cons 1 (if-test-index)))
           (push-proof-log 'compute (if-test-index))
           (push-proof-log 'if-true index)))))



;;; Log transformatiom of expr1 to expr2 based on the fact that
;;; (= expr1 expr2) or (= expr2 expr1) is (true).

(defun log-justify-equal-from-=-true (node1 node2 node3 index)
  (cond ((eq (arg-1-node node3) node1)
         (push-proof-log 'if-equal index (e-node-attribute node3) t)
         ;; (if (= expr1 expr2) expr1 expr1)
         (push-proof-log
          'look-up (if-left-index) (e-node-attribute node2))
         (log-node-equality node3 *true-node* (if-test-index))
         (push-proof-log 'if-true index)
         ;; expr2
         )
        (t
         (let ((expr1 (e-node-attribute node1))
               (expr2 (e-node-attribute node2)))
           (push-proof-log 'if-equal index `(= ,expr1 ,expr2) t)
           (push-proof-log 'look-up (if-left-index) expr2)
           ;; (if (= expr1 expr2) expr2 expr1)
           (log-use-axiom-as-rewrite
            `(= ,expr1 ,expr2) '=.commutes
	    `((= |)X| ,expr1) (= |)Y| ,expr2)) (if-test-index))
         (log-node-equality node3 *true-node* (if-test-index))
         (push-proof-log 'if-true index)
         ;; expr2
         ))))



;;; Log transformation of expr1 to expr2 where they have equal sums.

(defun log-justify-equal-from-=-sums (node other-node justification index)
  (let ((ref-node (second justification))
        (expr1 (e-node-attribute node))
        (expr2 (e-node-attribute other-node)))
    (push-proof-log 'if-equal index `(= ,expr1 ,expr2) t)
    (push-proof-log 'look-up (if-left-index) expr2)
    ;; (if (= expr1 expr2) expr2 expr1)
    (cond ((eq ref-node node)
           (log-collect-terms expr1 (cons 1 (if-test-index)))
           (log-collect-terms expr2 (cons 2 (if-test-index)))
           ;; (if (= sum1 sum2) expr2 expr1)
           (log-justify-=-sums (third justification) (if-test-index))
           (push-proof-log 'if-true index))
          (t
           (log-use-axiom-as-rewrite
            `(= ,expr1 ,expr2) '=.commutes
	    `((= |)X| ,expr1) (= |)Y| ,expr2)) (if-test-index))
           (log-collect-terms expr2 (cons 1 (if-test-index)))
           (log-collect-terms expr1 (cons 2 (if-test-index)))
           ;; (if (= sum2 sum1) expr2 expr1)
           (log-justify-=-sums (third justification) (if-test-index))
           (push-proof-log 'if-true index)))))



;;; Log transformation of (ord expr) to expr or expr to (ord expr).

(defun log-justify-ord-int (node1 node2 index)
  (cond ((ord-p (e-node-attribute node1))
         ;; (ord x) -> x
         (let ((expr (e-node-attribute node2)))
           (log-use-axiom-as-rewrite
            `(ord ,expr) 'ord.int.internal `((= |)X| ,expr)) index)
           ;; (if (= (type-of expr) (int)) expr (ord expr))
           (log-node-equality
            (e-node-type node2) *int-node* (cons 1 (if-test-index)))
           (push-proof-log 'compute (if-test-index))
           (push-proof-log 'if-true index)))
        (t
         ;; x -> (ord x)
         (let ((expr (e-node-attribute node1)))
           (push-proof-log 'if-equal index `(= ,expr (ord ,expr)) t)
           (push-proof-log 'look-up (if-left-index) `(ord ,expr))
           ;; (if (= expr (ord expr)) (ord expr) expr)
           (log-use-axiom-as-rewrite
            `(ord ,expr) 'ord.int.internal `((= |)X| ,expr))
	    (cons 2 (if-test-index)))
           ;; (if (= expr (if (= (type-of expr) (int)) expr (ord expr)))
           ;;     (ord expr)
           ;;     expr)
           (log-node-equality
            (e-node-type node1) *int-node* (list* 1 1 2 (if-test-index)))
           (push-proof-log 'compute (list* 1 2 (if-test-index)))
           (push-proof-log 'if-true (cons 2 (if-test-index)))
           (push-proof-log 'compute (if-test-index))
           (push-proof-log 'if-true index)))))




(defun log-justify-true-is-bool (node1 node2 index)
  (cond ((eq node1 *bool-node*)
         (let ((expr (e-node-attribute node2)))
           (push-proof-log 'if-equal index `(= (bool) ,expr) t)
           (push-proof-log 'look-up (if-left-index) expr)
           ;; (if (= (bool) (type-of (true))) (type-of (true)) (bool))
           (log-use-axiom-as-rewrite
            expr 'true.type-of-axiom nil (cons 2 (if-test-index)))
           (push-proof-log 'compute (if-test-index))
           (push-proof-log 'if-true index)))
        (t (log-use-axiom-as-rewrite
            (e-node-attribute node1) 'true.type-of-axiom nil index))))

(defun log-justify-false-is-bool (node1 node2 index)
  (cond ((eq node1 *bool-node*)
         (let ((expr (e-node-attribute node2)))
           (push-proof-log 'if-equal index `(= (bool) ,expr) t)
           (push-proof-log 'look-up (if-left-index) expr)
           ;; (if (= (bool) (type-of (false))) (type-of (true)) (bool))
           (log-use-axiom-as-rewrite
            expr 'false.type-of-axiom nil (cons 2 (if-test-index)))
           (push-proof-log 'compute (if-test-index))
           (push-proof-log 'if-true index)))
        (t (log-use-axiom-as-rewrite
            (e-node-attribute node1) 'false.type-of-axiom nil index))))

(defun log-justify-zero-is-int (node1 node2 index)
  (cond ((eq node1 *int-node*)
         (let ((expr (e-node-attribute node2)))
           (push-proof-log 'if-equal index `(= (int) ,expr) t)
           (push-proof-log 'look-up (if-left-index) expr)
           ;; (if (= (int) (type-of 0)) (type-of 0) (int))
           (log-use-axiom-as-rewrite
            expr '0.type-of-axiom nil (cons 2 (if-test-index)))
           (push-proof-log 'compute (if-test-index))
           (push-proof-log 'if-true index)))
        (t (log-use-axiom-as-rewrite
            (e-node-attribute node1) '0.type-of-axiom nil index))))

(defun log-justify-one-is-int (node1 node2 index)
  (cond ((eq node1 *int-node*)
         (let ((expr (e-node-attribute node2)))
           (push-proof-log 'if-equal index `(= (int) ,expr) t)
           (push-proof-log 'look-up (if-left-index) expr)
           ;; (if (= (int) (type-of 1)) (type-of 1) (int))
           (log-use-axiom-as-rewrite
            expr '1.type-of-axiom nil (cons 2 (if-test-index)))
           (push-proof-log 'compute (if-test-index))
           (push-proof-log 'if-true index)))
        (t (log-use-axiom-as-rewrite
            (e-node-attribute node1) '1.type-of-axiom nil index))))



;;; Log transformation of expr1 to expr2 based on the fact that
;;; the sum for (>= expr1 expr2) or (>= expr2 expr1) is dead.

(defun log-justify-zero-sum (node1 node2 node3 index)
  (let ((expr1 (e-node-attribute node1))
        (expr2 (e-node-attribute node2)))
    (push-proof-log 'if-equal index `(= ,expr1 ,expr2) t)
    (push-proof-log 'look-up (if-left-index) expr2)
    ;; (if (= expr1 expr2) expr2 expr1)
    (cond ((eq node1 (arg-1-node node3))
           ;; node3 is (>= expr1 expr2)
           (log-convert-=-to-=-zero expr1 expr2 (if-test-index))
           ;; (if (= (- expr1 expr2) 0) expr2 expr1)
           (log-collect-terms `(- ,expr1 ,expr2) (cons 1 (if-test-index))))
          (t
           ;; node3 is (>= expr2 expr1)
           (log-use-axiom-as-rewrite
            `(= ,expr1 ,expr2) '=.commutes `((= |)X| ,expr1) (= |)Y| ,expr2))
	    (if-test-index))
           (log-convert-=-to-=-zero expr2 expr1 (if-test-index))
           ;; (if (= (- expr2 expr1) 0) expr2 expr1)
           (log-collect-terms `(- ,expr2 ,expr1) (cons 1 (if-test-index)))))
    (log-justify-killed node3 0 (if-test-index))
    ;; (if (true) expr2 expr1)
    (push-proof-log 'if-true index)))

;;; Log transformation of expr to 0 or 0 to expr based on the fact that
;;; (* a b) is 0 and both a and b are equal to expr.

(defun log-justify-square-zero (node1 node2 node3 index)
  (cond ((eq node1 *zero-node*)
         ;; 0 -> expr
         (let ((expr (e-node-attribute node2)))
           (push-proof-log 'if-equal index `(= 0 ,expr) t)
           (push-proof-log 'look-up (if-left-index) expr)
           ;; (if (= 0 expr) expr 0)
           (log-use-axiom-as-rewrite
            `(= 0 ,expr) '=.commutes `((= |)X| 0) (= |)Y| ,expr))
	    (if-test-index))
           ;; (if (= expr 0) expr 0)
           (log-justify-square-zero-aux node2 node3 (if-test-index))))
        (t
         ;; expr -> 0
         (push-proof-log 'if-equal index `(= ,(e-node-attribute node1) 0) t)
         (push-proof-log 'look-up (if-left-index) 0)
         ;; (if (= expr 0) 0 expr)
         (log-justify-square-zero-aux node1 node3 (if-test-index))))
  (push-proof-log 'if-true index))

(defun log-justify-square-zero-aux (node1 node2 index)
  ;; (= expr 0)
  (let ((expr (e-node-attribute node1)))
    (push-proof-log 'if-equal index `(= (= ,expr 0) (= (* ,expr ,expr) 0)) t)
    (push-proof-log 'look-up (if-left-index) `(= (* ,expr ,expr) 0))
    ;; (if (= (= expr 0) (= (* expr expr) 0)) (= (* expr expr) 0) (= expr 0))
    (log-use-axiom-as-rewrite
     `(= (* ,expr ,expr) 0) 'square.zero `((= |)X| ,expr))
     (cons 2 (if-test-index)))
    ;; (if (= (= expr 0)
    ;;        (if (= (type-of expr) (int)) (= expr 0) (= (* expr expr) 0)))
    ;;     (= (* expr expr) 0)
    ;;     (= expr 0))
    (log-type-of-expr expr (list* 1 1 2 (if-test-index)))
    (push-proof-log 'compute (list* 1 2 (if-test-index)))
    (push-proof-log 'if-true (cons 2 (if-test-index)))
    ;; (if (= (= expr 0) (= expr 0)) (= (* expr expr) 0) (= expr 0))
    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)
    ;; (= (* expr expr) 0)
    (log-node-equality node1 (arg-1-node node2) (list* 1 1 index))
    (log-node-equality node1 (arg-2-node node2) (list* 1 2 index))
    ;; (= (* a b) 0)
    (log-node-equality node2 *zero-node* (cons 1 index))
    (push-proof-log 'compute index)))



;;; Generate log for the 'zero justification.

(defun log-justify-zero (node node2 i index)
  (let ((expr2 (e-node-attribute node2)))
    (cond ((eq node *true-node*)
           ;; (true) -> (= x y) or (true) -> (>= x y)
           (push-proof-log 'if-equal index `(= (true) ,expr2) t)
           (push-proof-log 'look-up (if-left-index) expr2)
           (cond ((=-p expr2)
                  ;; (if (= (true) (= x y)) (= x y) (true))
                  (log-justify-equality-from-killed
                   node2 i (cons 2 (if-test-index))))
                 (t
                  (log-justify-inequality-from-killed
                   node2 (cons 2 (if-test-index)))))
           (push-proof-log 'compute (if-test-index))
           (push-proof-log 'if-true index))
          ((eq node *false-node*)
           ;; (false) -> (= x y) or (false) -> (>= x y)
           (push-proof-log 'if-equal index `(= (false) ,expr2) t)
           (push-proof-log 'look-up (if-left-index) expr2)
           (cond ((=-p expr2)
                  ;; (if (= (false) (= x y)) (= x y) (false))
                  (log-justify-false-equality-from-killed
                   node2 i (cons 2 (if-test-index))))
                 (t
                  (log-justify-false-inequality-from-killed
                   node2 (cons 2 (if-test-index)))))
           (push-proof-log 'compute (if-test-index))
           (push-proof-log 'if-true index))
          ((eq node *zero-node*)
           ;; 0 -> x2
           (push-proof-log 'if-equal index `(= 0 ,expr2) t)
           (push-proof-log 'look-up (if-left-index) expr2)
           ;; (if (= 0 x2) x2 0)
           (log-use-axiom-as-rewrite
            `(= 0 ,expr2) '=.commutes `((= |)X| 0) (= |)Y| ,expr2))
	    (if-test-index))
           ;; (if (= x2 0) x2 0)
           (log-equal-zero node2 expr2 i (if-test-index))
           (push-proof-log 'if-true index))
          (t (let ((expr (e-node-attribute node)))
               (cond ((=-p expr)
                      (cond ((eq node2 *true-node*)
                             ;; (= x y) -> (true)
                             (log-justify-equality-from-killed node i index))
                            (t
                             ;; (= x y) -> (false)
                             (log-justify-false-equality-from-killed
                              node i index))))
                     ((>=-p expr)
                      (cond ((eq node2 *true-node*)
                             ;; (>= x y) -> (true)
                             (log-justify-inequality-from-killed node index))
                            (t
                             ;; (>= x y) -> (false)
                             (log-justify-false-inequality-from-killed
                              node index))))
                     (t
                      ;; expr -> 0
                      (push-proof-log 'if-equal index `(= ,expr 0) t)
                      (push-proof-log 'look-up (if-left-index) 0)
                      ;; (if (= expr 0) 0 expr)
                      (log-equal-zero node expr i (if-test-index))
                      (push-proof-log 'if-true index))))))))



;;; Log transformation of (= expr 0) to (true) based on killed entry for expr.

(defun log-equal-zero (node expr i index)
  (when (= i 1)
    (log-use-axiom-as-rewrite
     `(= ,expr 0) 'negate.=.zero `((= |)X| ,expr)) index)
    ;; (if (= (type-of expr) (int)) (= (negate expr) 0) (= expr 0))
    (log-node-equality (e-node-type node) *int-node* (cons 1 (if-test-index)))
    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)
    ;; (= (negate x2) 0)
    )
  (log-collect-terms
   (if (= i 1) `(negate ,expr) expr) (cons 1 index))
  ;; (= sum 0)
  (log-justify-killed node i index)
  ;; (true)
  )

;;; Log transformation of (= x y) to (true) based on killed entry for (= x y).
;;; node is the node for (= x y) and i is 0 or 1.

(defun log-justify-equality-from-killed (node i index)
  ;; (= x y)
  (log-sum-conversion-of-= node index)
  ;; (= sum 0)
  (when (= i 1)
    (let ((expr (raw-expr-of-sum (sum-of-node node 0))))
      (log-use-axiom-as-rewrite
       `(= ,expr 0) 'negate.=.zero `((= |)X| ,expr)) index)
      ;; (if (= (type-of sum) (int)) (= (negate sum) 0) (= sum 0))
      (log-type-of-expr expr (cons 1 (if-test-index)))
      (push-proof-log 'compute (if-test-index))
      (push-proof-log 'if-true index)
      ;; (= (negate sum) 0)
      (log-push-negate-into-sum expr (cons 1 index))))
  (log-justify-killed node i index))



;;; Log transformation of (= x y) to (false) based on killed entry for (= x y).
;;; node is the node for (= x y) and i is 2 or 3.

(defun log-justify-false-equality-from-killed (node i index)
  ;; (= x y)
  (log-sum-conversion-of-= node index)
  ;; (= sum 0)
  (let ((expr (raw-expr-of-sum (sum-of-node node 0))))
    (cond ((integerp expr)
           (cond ((= i 2)
                  (push-proof-log 'if-equal (cons 1 index)
                                  `(= ,expr (+ ,(- expr 1) 1))
				  t)
                  (push-proof-log 'look-up (list* 2 1 index)
                                  `(+ ,(- expr 1) 1))
                  ;; (= (if (= x (+ x-1 1)) (+ x-1 1) x) 0)
                  (push-proof-log 'compute (list* 2 1 1 index))
                  (push-proof-log 'compute (list* 1 1 index))
                  (push-proof-log 'if-true (cons 1 index))
                  ;; (= (+ x-1 1) 0)
                  (push-proof-log 'if-equal index `(= ,(- expr 1) 0) t)
                  (push-proof-log 'look-up (list* 1 1 (if-left-index)) 0)
                  ;; (if (= x-1 0) (= (+ 0 1) 0) (= (+ x-1 1) 0))
                  (push-proof-log 'compute (cons 1 (if-left-index)))
                  (push-proof-log 'compute (if-left-index))
                  (log-justify-killed node i (if-test-index))
                  (push-proof-log 'if-true index))
                 (t
                  (push-proof-log 'if-equal (cons 1 index) t
                                  `(= ,expr (- (negate ,(- (+ expr 1))) 1)))
                  (push-proof-log 'look-up (list* 2 1 index)
                                  `(- (negate ,(- (+ expr 1))) 1))
                  ;; (= (if (= x (- (negate -x-1) 1)) (- (negate -x-1) 1) x) 0)
                  (push-proof-log 'compute (list* 1 2 1 1 index))
                  (push-proof-log 'compute (list* 2 1 1 index))
                  (push-proof-log 'compute (list* 1 1 index))
                  (push-proof-log 'if-true (cons 1 index))
                  ;; (= (- (negate -x-1) 1) 0)
                  (push-proof-log 'if-equal index `(= ,(- (+ expr 1)) 0) t)
                  (push-proof-log 'look-up (list* 1 1 1 (if-left-index))
                                  0)
                  ;; (if (= x-1 0)
                  ;;     (= (- (negate 0) 1) 0)
                  ;;     (= (- (negate -x-1) 1) 0))
                  (push-proof-log 'compute (list* 1 1 (if-left-index)))
                  (push-proof-log 'compute (cons 1 (if-left-index)))
                  (push-proof-log 'compute (if-left-index))
                  (log-justify-killed node i (if-test-index))
                  (push-proof-log 'if-true index))))
          ((= i 2)
           ;; case where (- sum 1) is 0
           (push-proof-log 'if-equal index `(= ,expr 1) t)
           (push-proof-log 'look-up (cons 1 (if-left-index)) 1)
           ;; (if (= sum 1) (= 1 0) (= sum 0))
           (push-proof-log 'compute (if-left-index))
           (log-convert-=-to-=-zero expr 1 (if-test-index))
           ;; (if (= (- sum 1) 0) (false) (= sum 0))
	   (cond ((integerp expr)
		  (push-proof-log 'compute (cons 1 (if-test-index))))
		 (t
		  (log-use-axiom-as-rewrite
		   `(- ,expr 1) '-.+.left.to.+.-.left
		   `((= |)X| ,(second expr)) (= |)Y| ,(third expr)) (= |)Z| 1))
		   (cons 1 (if-test-index)))
		  (push-proof-log 'compute (list* 1 1 (if-test-index)))))
           ;; (if (= ssum 0) (false) (= sum 0))
           (log-justify-killed node i (if-test-index))
           (push-proof-log 'if-true index))
          (t
           ;; case where (+ -sum -1) is 0
           (push-proof-log 'if-equal index `(= ,expr -1) t)
           (push-proof-log 'look-up (cons 1 (if-left-index)) 1)
           ;; (if (= sum -1) (= -1 0) (= sum 0))
           (push-proof-log 'compute (if-left-index))
           (log-use-axiom-as-rewrite
            `(= ,expr -1) '=.commutes `((= |)X| ,expr) (= |)Y| -1))
	    (if-test-index))
           ;; (if (= -1 sum) (false) (= sum 0))
           (log-convert-=-to-=-zero -1 expr (if-test-index))
           ;; (if (= (- -1 sum) 0) (false) (= sum 0))
	   (cond ((integerp expr)
		  (push-proof-log 'compute (cons 1 (if-test-index))))
		 (t
		  (log-use-axiom-as-rewrite
		   `(- -1 ,expr) '-.+.right.to.-.-.left
		   `((= |)X| -1) (= |)Y| ,(second expr)) (= |)Z| ,(third expr)))
		   (cons 1 (if-test-index)))
		  ;; (if (= (- (- -1 c) rest) 0) (false) (= sum 0))
		  (push-proof-log 'compute (list* 1 1 (if-test-index)))
		  (let ((c (- -1 (second expr))))
		    (push-proof-log 'if-equal index
				    `(= (- ,c ,(third expr))
					(+ ,c (negate ,(third expr))))
				    t)
		    (push-proof-log 'look-up (list* 1 1 (if-left-index))
				    `(+ ,c (negate ,(third expr))))
		    (log-use-axiom-as-rewrite
		     `(+ ,c (negate ,(third expr))) '+.negate
		     `((= |)X| ,c) (= |)Y| ,(third expr)))
		     (cons 2 (if-test-index)))
		    (push-proof-log 'compute (if-test-index))
		    (push-proof-log 'if-true index)
		    ;; (if (= (+ c (negate rest)) 0) (false) (= sum 0))
		    (log-push-negate-into-sum-aux
		     (third expr) (list* 2 1 (if-test-index))))))
	   ;; (if (= opp-sum 0) (false) (= sum 0))
	   (log-justify-killed node i (if-test-index))
	   ;; (if (true) (false) (= sum 0))
	   (push-proof-log 'if-true index)))))



;;; Log transformation of (>= x y) to (true) based on killed entry for
;;; (>= x y).
;;; node is the node for (>= x y).

(defun log-justify-inequality-from-killed (node index)
  ;; (>= x y)
  (log-sum-conversion-of->= node index)
  ;; (>= sum 0)
  (push-proof-log
   'if-equal index `(= ,(raw-expr-of-sum (sum-of-node node 0)) 0) t)
  (push-proof-log 'look-up (cons 1 (if-left-index)) 0)
  ;; (if (= sum 0) (>= 0 0) (>= sum 0))
  (push-proof-log 'compute (if-left-index))
  (log-justify-killed node 0 (if-test-index))
  ;; (if (true) (true) (>= sum 0))
  (push-proof-log 'if-true index))

;;; Log transformation of (>= x y) to (false) based on killed entry for
;;; (>= x y).
;;; node is the node for (>= x y).

(defun log-justify-false-inequality-from-killed (node index)
  ;; (>= x y)
  (log-sum-conversion-of->= node index)
  ;; (>= sum 0)
  (let ((expr (raw-expr-of-sum (sum-of-node node 0))))
    (cond ((integerp expr)
           (push-proof-log 'compute index))
          (t
           (push-proof-log 'if-equal index `(= ,expr -1) t)
           (push-proof-log 'look-up (cons 1 (if-left-index)) -1)
           ;; (if (= sum -1) (>= -1 0) (>= sum 0))
           (push-proof-log 'compute (if-left-index))
           ;; (if (= sum -1) (false) (>= sum 0))
           (log-use-axiom-as-rewrite
            `(= ,expr -1) '=.commutes `((= |)X| ,expr) (= |)Y| -1))
	    (if-test-index))
           ;; (if (= -1 sum) (false) (>= sum 0))
           (log-convert-=-to-=-zero -1 expr (if-test-index))
           ;; (if (= (- -1 sum) 0) (false) (>= sum 0))
	   (cond ((integerp expr)
		  (push-proof-log 'compute (cons 1 (if-test-index))))
		 (t
		  (log-use-axiom-as-rewrite
		   `(- -1 ,expr) '-.+.right.to.-.-.left
		   `((= |)X| -1) (= |)Y| ,(second expr)) (= |)Z| ,(third expr)))
		   (cons 1 (if-test-index)))
		  ;; (if (= (- (- -1 c) rest) 0) (false) (>= sum 0))
		  (push-proof-log 'compute (list* 1 1 (if-test-index)))
		  (let ((c (- -1 (second expr))))
		    (push-proof-log 'if-equal index
				    `(= (- ,c ,(third expr))
					(+ ,c (negate ,(third expr))))
				    t)
		    (push-proof-log 'look-up (list* 1 1 (if-left-index))
				    `(+ ,c (negate ,(third expr))))
		    (log-use-axiom-as-rewrite
		     `(+ ,c (negate ,(third expr))) '+.negate
		     `((= |)X| ,c) (= |)Y| ,(third expr)))
		     (cons 2 (if-test-index)))
		    (push-proof-log 'compute (if-test-index))
		    (push-proof-log 'if-true index)
		    ;; (if (= (+ c (negate rest)) 0) (false) (>= sum 0))
		    (log-push-negate-into-sum-aux
		     (third expr) (list* 2 1 (if-test-index))))))
	   ;; (if (= opp-sum 0) (false) (>= sum 0))
	   (log-justify-killed node 1 (if-test-index))
	   ;; (if (true) (false) (>= sum 0))
	   (push-proof-log 'if-true index)))))



;;; Log transformation of expr to (true) or (true) to expr based on the
;;; fact that expr is asserted by a grule.

(defun log-justify-equal-from-grule (node1 node2 justification index)
  (cond ((eq node1 *true-node*)
         ;; (true)
         (push-proof-log
	  'if-equal index `(= (true) ,(e-node-attribute node2)) t)
         (push-proof-log 'look-up (if-left-index)
                         (e-node-attribute node2))
         ;; (if (= (true) expr) expr (true))
         (log-justify-equal-from-grule-aux
          justification (cons 2 (if-test-index)))
         (push-proof-log 'compute (if-test-index))
         (push-proof-log 'if-true index)
         ;; expr
         )
        (t (log-justify-equal-from-grule-aux justification index)))
  )
         
(defun log-justify-equal-from-grule-aux (justification index)
  (let ((grule (third justification))
        (subst (fourth justification))
        (results (fifth justification)))
    ;; expr
    (let ((axiom-name (intern (string-append (event-name grule) ".INTERNAL")
			      *zk-package*))
          (renames (grule-renames grule)))
      (log-use-axiom index axiom-name)
      ;; (if axiom expr (true))
      (log-renames renames (if-test-index))
      (linearize-and-log-universal-instantiations
       (mapcar #'(lambda (u) (make-= (cdr u) (binding-of (cdr u) subst)))
               renames)
       (if-test-index))
      ;; (if (if axiom-inst renamed-axiom (false)) expr (true))
      (log-renames (mapcar #'(lambda (u) (cons (cdr u) (car u))) renames)
                   (cons 2 (if-test-index)))
      (cond ((null renames)
	     ;; (if axiom-inst expr (true))
	     (when (grule-subgoals grule)
	       (log-discharge-grule-subgoals
		(grule-subgoals grule) subst results (list* 1 (if-test-index)))
	       (push-proof-log 'if-true (if-test-index))
               ;; (if (if expr (true) (false)) expr (true))
               (push-proof-log 'case-analysis index 1)
               (push-proof-log 'if-true (if-left-index))
               (push-proof-log 'if-false (if-right-index)))
	     (push-proof-log 'look-up (if-left-index) *true*)
	     ;; (if expr (true) (true))
	     (push-proof-log 'if-equal index))
	    (t
	     (push-proof-log 'use-axiom
			     (cons 2 (if-test-index)) axiom-name t)
	     (when (grule-subgoals grule)
	       (log-discharge-grule-subgoals
		(grule-subgoals grule) subst results
                (list* 1 1 (if-test-index)))
	       (push-proof-log 'if-true (cons 1 (if-test-index)))
               (push-proof-log 'case-analysis (if-test-index) 1)
               (push-proof-log 'if-true (cons 2 (if-test-index)))
               (push-proof-log 'if-false (cons 3 (if-test-index))))
	     (push-proof-log 'case-analysis index 1)
	     ;; (if expr
	     ;;     (if (true) expr (true))
	     ;;     (if (false) expr (true)))
	     (push-proof-log 'if-true (if-left-index))
	     (push-proof-log 'look-up (if-left-index) *true*)
	     (push-proof-log 'if-false (if-right-index))
	     ;; (if expr (true) (true))
	     (push-proof-log 'if-equal index))))))




;;; Log transformation of expr to (true) or (true) to expr based on the
;;; fact that expr is asserted by a frule.

(defun log-justify-equal-from-frule (node1 node2 justification index)
  (cond ((eq node1 *true-node*)
         ;; (true)
         (push-proof-log
	  'if-equal index `(= (true) ,(e-node-attribute node2)) t)
         (push-proof-log 'look-up (if-left-index)
                         (e-node-attribute node2))
         ;; (if (= (true) expr) expr (true))
         (log-justify-equal-from-frule-aux justification
                                           (cons 2 (if-test-index)))
         (push-proof-log 'compute (if-test-index))
         (push-proof-log 'if-true index)
         ;; expr
         )
        (t (log-justify-equal-from-frule-aux justification index)))
  )

(defun log-justify-equal-from-frule-aux (justification index)
  (let ((cond-node (second justification))
        (node2 (third justification))
        (frule (fourth justification))
        (i (fifth justification))
        (subst (sixth justification))
        (just (seventh justification)))
    ;; expr
    (let ((axiom-name (intern (string-append (event-name frule) ".INTERNAL")
			      *zk-package*))
          (renames (frule-renames frule)))
      (log-use-axiom index axiom-name)
      ;; (if axiom expr (true))
      (log-renames renames (if-test-index))
      (linearize-and-log-universal-instantiations
       (mapcar #'(lambda (u) (make-= (cdr u) (binding-of (cdr u) subst)))
               renames)
       (if-test-index))
      ;; (if (if axiom-inst renamed-axiom (false)) expr (true))
      (log-renames (mapcar #'(lambda (u) (cons (cdr u) (car u))) renames)
                   (cons 2 (if-test-index)))
      (cond
       ((null renames)
        ;; (if (if cond concl (true)) expr (true))
        (log-discharge-frule-condition
         cond-node (frule-negate frule) just (cons 1 (if-test-index)))
        (push-proof-log 'if-true (if-test-index))
        ;; (if concl expr (true))
        (cond ((= (length (frule-values frule)) 1)
               ;; (if expr expr (true))
               (push-proof-log 'look-up (if-left-index) *true*)
               (push-proof-log 'if-equal index))
              (t
               (log-justify-equal-from-frule-aux-aux-aux
                i (if-left (make-frule-internal-axiom frule)) (if-test-index))
               ;; (if (false) expr (true))
               (push-proof-log 'if-false index))))
       (t
        (push-proof-log 'use-axiom (cons 2 (if-test-index)) axiom-name t)
        ;; (if (if (if cond concl (true)) (true) (false)) expr (true))
        (log-discharge-frule-condition
         cond-node (frule-negate frule) just (list* 1 1 (if-test-index)))
        (push-proof-log 'if-true (cons 1 (if-test-index)))
        ;; (if (if concl (true) (false)) expr (true))
        (cond ((= (length (frule-values frule)) 1)
               ;; (if (if (if expr (true) (false)) (true) (false)) expr (true))
               (push-proof-log 'case-analysis (if-test-index) 1)
               (push-proof-log 'if-true (cons 2 (if-test-index)))
               (push-proof-log 'if-false (cons 3 (if-test-index)))
               (push-proof-log 'case-analysis index 1)
               (push-proof-log 'if-true (if-left-index))
               (push-proof-log 'if-false (if-right-index))
               (push-proof-log 'look-up (if-left-index) *true*)
               (push-proof-log 'if-equal index))
              (t (let* ((axiom (make-frule-internal-axiom frule))
                        (renamed-axiom (sublis-eq renames axiom)))
                   (log-justify-equal-from-frule-aux-aux
                    (e-node-attribute node2)
                    (sublis-eq subst (if-left renamed-axiom))
                    i index)))))))))



(defun log-justify-equal-from-frule-aux-aux (expr concl i index)
  ;; (if (if concl (true) (false)) expr (true))
  (push-proof-log 'if-equal index expr t)
  (push-proof-log 'look-up (cons 2 (if-left-index)) *true*)
  (push-proof-log 'if-equal (if-left-index))
  ;; (if expr
  ;;     (true)
  ;;     (if (if concl (true) (false)) expr (true)))
  (log-justify-equal-from-frule-aux-aux-aux
   i concl (list* 1 1 (if-right-index)))
  ;; (if expr
  ;;     (true)
  ;;     (if (if (false) (true) (false)) expr (true)))
  (push-proof-log 'if-false (cons 1 (if-right-index)))
  (push-proof-log 'if-false (if-right-index))
  ;; (if expr (true) (true))
  (push-proof-log 'if-equal index))

(defun log-justify-equal-from-frule-aux-aux-aux (i concl index)
  (cond ((= i 0)
         ;; (if expr rest (false))
         (push-proof-log 'if-false (if-left-index) *false* t)
         (push-proof-log 'if-true (if-right-index) (if-left concl) t)
         ;; (if expr
         ;;     (if (false) (false) rest)
         ;;     (if (true) (false) rest))
         (push-proof-log 'case-analysis index 1 t)
         ;; (if (if expr (false) (true)) (false) rest)
         (push-proof-log 'look-up (if-test-index) *true*)
         (push-proof-log 'if-true index)
         ;; (false)
         )
        (t
         ;; (if ci rest (false))
         (log-justify-equal-from-frule-aux-aux-aux
          (- i 1) (if-left concl) (if-left-index))
         ;; (if ci (false) (false))
         (push-proof-log 'if-equal index)
         ;; (false)
         )))



;;; Log transformation of (type-of expr) to type or type to (type-of expr)
;;; based on node equality between (in expr type) and (true).

(defun log-justify-in-=-type-of (node1 node2 node3 index)
  (cond ((or (eq node1 *bool-node*) (eq node1 *int-node*))
         ;; type -> (type-of expr)
         (let ((type (e-node-attribute node1))
               (expr (e-node-attribute (arg-1-node node2))))
           (push-proof-log 'if-equal index `(= ,type (type-of ,expr)) t)
           (push-proof-log 'look-up (if-left-index) `(type-of ,expr))
           ;; (if (= type (type-of expr)) (type-of expr) type)
           (log-use-axiom-as-rewrite
            `(= ,type (type-of ,expr)) '=.commutes
	    `((= |)X| ,type) (= |)Y| (type-of ,expr)))
            (if-test-index))
           (log-justify-in-=-type-of-aux  node2 node1 node3 (if-test-index))
           ;; (if (true) (type-of expr) type)
           (push-proof-log 'if-true index)))
        (t
         ;; (type-of expr) -> type
         (let ((type (e-node-attribute node2))
               (expr (e-node-attribute (arg-1-node node1))))
           (push-proof-log 'if-equal index `(= (type-of ,expr) ,type) t)
           (push-proof-log 'look-up (if-left-index) type)
           ;; (if (= (type-of expr) type) type (type-of expr))
           (log-justify-in-=-type-of-aux  node1 node2 node3 (if-test-index))
           ;; (if (true) (type-of expr) type)
           (push-proof-log 'if-true index)))))

;;; Log transformation of (= (type-of expr) type) to (true).
;;; node1 is node for (type-of expr)
;;; node2 is node for type ((bool), (int), or (char))
;;; node3 is node for (in expr type)

(defun log-justify-in-=-type-of-aux (node1 node2 node3 index)
  ;; (= (type-of expr) type)
  (let ((expr (e-node-attribute (arg-1-node node1)))
        (type (e-node-attribute node2)))
    (push-proof-log 'if-equal index
                    `(= (= (type-of ,expr) ,type) (in ,expr ,type))
		    t)
    (push-proof-log 'look-up (if-left-index)
                    `(in ,expr ,type))
    ;; (if (= (= (type-of expr) type) (in expr type))
    ;;     (in expr type)
    ;;     (= (type-of expr) type))
    (log-node-equality node3 *true-node* (if-left-index))
    ;; (if (= (= (type-of expr) type) (in expr type))
    ;;     (true)
    ;;     (= (type-of expr) type))
    (log-in-to-type-of expr type (cons 2 (if-test-index)))
    ;; (if (= (= (type-of expr) type) (= (type-of expr) type))
    ;;     (true)
    ;;     (= (type-of expr) type))
    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)))



;;; Log transformation of x to 0 or 0 to x based on (= (* x y) 0)
;;; and not (= y 0).

(defun log-justify-product-zero-left (node1 node2 node3 justification index)
  (let ((expr1 (e-node-attribute node1)) ; x or 0
        (expr2 (e-node-attribute node2))) ; 0 or x
    (push-proof-log 'if-equal index `(= ,expr1 ,expr2) t)
    (push-proof-log 'look-up (if-left-index) expr2)
    ;; (if (= expr1 expr2) expr2 expr1)
    (cond ((eq node1 *zero-node*)
           (log-use-axiom-as-rewrite
            `(= ,expr1 ,expr2) '=.commutes
	    `((= |)X| ,expr1) (= |)Y| ,expr2)) (if-test-index))
           (log-justify-product-zero-left-aux
            node2 node3 justification (if-test-index)))
          (t
           (log-justify-product-zero-left-aux
            node1 node3 justification (if-test-index))))
    ;; (if (true) expr2 expr1)
    (push-proof-log 'if-true index)))

(defun log-justify-product-zero-left-aux (node1 node2 justification index)
  ;; (= x 0)
  (let ((expr (e-node-attribute node1))
        (prod (e-node-attribute node2)))
    (push-proof-log 'if-equal index `(= (= ,expr 0) (= ,prod 0)) t)
    (push-proof-log 'look-up (if-left-index) `(= ,prod 0))
    ;; (if (= (= x 0) (= (* x y) 0)) (= (* x y) 0) (= x 0))
    (log-node-equality node2 *zero-node* (cons 1 (if-left-index)))
    (push-proof-log 'compute (if-left-index))
    ;; (if (= (= x 0) (= (* x y) 0)) (true) (= x 0))
    (log-use-axiom-as-rewrite
     `(= ,prod 0) 'product.zero.left
     `((= |)X| ,(second prod)) (= |)Y| ,(third prod)))
     (cons 2 (if-test-index)))
    ;; (if (= (= x 0)
    ;;        (if (= (type-of x) (int))
    ;;            (if (= (type-of y) (int))
    ;;                (if (if (= y 0) (false) (true)) (= x 0) (= (* x y) 0))
    ;;                (= (* x y) 0))
    ;;            (= (* x y) 0)))
    ;;     (true)
    ;;     (= x 0))
    (log-node-equality (e-node-type node1) *int-node*
                       (list* 1 1 2 (if-test-index)))
    (push-proof-log 'compute (list* 1 2 (if-test-index)))
    (push-proof-log 'if-true (cons 2 (if-test-index)))
    (log-node-equality (e-node-type (arg-2-node node2)) *int-type*
                       (list* 1 1 2 (if-test-index)))
    (push-proof-log 'compute (list* 1 2 (if-test-index)))
    (push-proof-log 'if-true (cons 2 (if-test-index)))
    ;; (if (= (= x 0) (if (if (= y 0) (false) (true)) (= x 0) (= (* x y) 0)))
    ;;     (true)
    ;;     (= x 0))
    (log-forbid-aux (arg-2-node node2) *zero-node*
                    justification (list* 1 2 (if-test-index)))
    (push-proof-log 'if-true (cons 2 (if-test-index)))
    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)))



;;; Log transformation of y to 0 or 0 to y based on (= (* x y) 0)
;;; and not (= x 0).

(defun log-justify-product-zero-right (node1 node2 node3 justification index)
  (let ((expr1 (e-node-attribute node1)) ; y or 0
        (expr2 (e-node-attribute node2))) ; 0 or y
    (push-proof-log 'if-equal index `(= ,expr1 ,expr2) t)
    (push-proof-log 'look-up (if-left-index) expr2)
    ;; (if (= expr1 expr2) expr2 expr1)
    (cond ((eq node1 *zero-node*)
           (log-use-axiom-as-rewrite
            `(= ,expr1 ,expr2) '=.commutes
	    `((= |)X| ,expr1) (= |)Y| ,expr2)) (if-test-index))
           (log-justify-product-zero-right-aux
            node2 node3 justification (if-test-index)))
          (t
           (log-justify-product-zero-right-aux
            node1 node3 justification (if-test-index))))
    ;; (if (true) expr2 expr1)
    (push-proof-log 'if-true index)))

(defun log-justify-product-zero-right-aux (node1 node2 justification index)
  ;; (= y 0)
  (let ((expr (e-node-attribute node1))
        (prod (e-node-attribute node2)))
    (push-proof-log 'if-equal index `(= (= ,expr 0) (= ,prod 0)) t)
    (push-proof-log 'look-up (if-left-index) `(= ,prod 0))
    ;; (if (= (= y 0) (= (* x y) 0)) (= (* x y) 0) (= y 0))
    (log-node-equality node2 *zero-node* (cons 1 (if-left-index)))
    (push-proof-log 'compute (if-left-index))
    ;; (if (= (= y 0) (= (* x y) 0)) (true) (= y 0))
    (log-use-axiom-as-rewrite
     `(= ,prod 0) 'product.zero.right
     `((= |)X| ,(second prod)) (= |)Y| ,(third prod)))
     (cons 2 (if-test-index)))
    ;; (if (= (= y 0)
    ;;        (if (= (type-of x) (int))
    ;;            (if (= (type-of y) (int))
    ;;                (if (if (= x 0) (false) (true)) (= y 0) (= (* x y) 0))
    ;;                (= (* x y) 0))
    ;;            (= (* x y) 0)))
    ;;     (true)
    ;;     (= y 0))
    (log-node-equality (e-node-type (arg-1-node node2)) *int-node*
                       (list* 1 1 2 (if-test-index)))
    (push-proof-log 'compute (list* 1 2 (if-test-index)))
    (push-proof-log 'if-true (cons 2 (if-test-index)))
    (log-node-equality (e-node-type node1) *int-node*
                       (list* 1 1 2 (if-test-index)))
    (push-proof-log 'compute (list* 1 2 (if-test-index)))
    (push-proof-log 'if-true (cons 2 (if-test-index)))
    ;; (if (= (= y 0) (if (if (= x 0) (false) (true)) (= y 0) (= (* x y) 0)))
    ;;     (true)
    ;;     (= y 0))
    (log-forbid-aux (arg-1-node node2) *zero-node*
                    justification (list* 1 2 (if-test-index)))
    (push-proof-log 'if-true (cons 2 (if-test-index)))
    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)))



;;; Log transformation of (* x y) to 0 or 0 to (* x y) based
;;; on node equality between x and 0.

(defun log-justify-times-zero-left (node1 node2 index)
  (cond ((eq node1 *zero-node*)
         ;; 0 -> (* x y)
         (let ((prod (e-node-attribute node2)))
           (push-proof-log 'if-equal index `(= 0 ,prod) t)
           (push-proof-log 'look-up (if-left-index) prod)
           ;; (if (= 0 (* x y)) (* x y) 0)
           (log-node-equality
            (arg-1-node node2) *zero-node* (list* 1 2 (if-test-index)))
           (log-use-axiom-as-rewrite
            `(* 0 ,(third prod)) '*.zero.left `((= |)X| ,(third prod)))
            (cons 2 (if-test-index)))
           ;; (if (= 0 0) (* x y) 0)
           ))
        (t
         ;; (* x y) -> 0
         (let ((prod (e-node-attribute node1)))
           (push-proof-log 'if-equal index `(= ,prod 0) t)
           (push-proof-log 'look-up (if-left-index) 0)
           ;; (if (= (* x y) 0) 0 (* x y))
           (log-node-equality
            (arg-1-node node1) *zero-node* (list* 1 1 (if-test-index)))
           (log-use-axiom-as-rewrite
            `(* 0 ,(third prod)) '*.zero.left `((= |)X| ,(third prod)))
            (cons 1 (if-test-index)))
           ;; (if (= 0 0) 0 (* x y))
           )))
  (push-proof-log 'compute (if-test-index))
  (push-proof-log 'if-true index))



;;; Log transformation of (* x y) to 0 or 0 to (* x y) based
;;; on node equality between y and 0.

(defun log-justify-times-zero-right (node1 node2 index)
  (cond ((eq node1 *zero-node*)
         ;; 0 -> (* x y)
         (let ((prod (e-node-attribute node2)))
           (push-proof-log 'if-equal index `(= 0 ,prod) t)
           (push-proof-log 'look-up (if-left-index) prod)
           ;; (if (= 0 (* x y)) (* x y) 0)
           (log-node-equality
            (arg-2-node node2) *zero-node* (list* 2 2 (if-test-index)))
           (log-use-axiom-as-rewrite
            `(* ,(second prod) 0) '*.zero.right `((= |)X| ,(second prod)))
            (cons 2 (if-test-index)))
           ;; (if (= 0 0) (* x y) 0)
           ))
        (t
         ;; (* x y) -> 0
         (let ((prod (e-node-attribute node1)))
           (push-proof-log 'if-equal index `(= ,prod 0) t)
           (push-proof-log 'look-up (if-left-index) 0)
           ;; (if (= (* x y) 0) 0 (* x y))
           (log-node-equality
            (arg-2-node node1) *zero-node* (list* 2 1 (if-test-index)))
           (log-use-axiom-as-rewrite
            `(* ,(second prod) 0) '*.zero.right `((= |)X| ,(second prod)))
            (cons 1 (if-test-index)))
           ;; (if (= 0 0) 0 (* x y))
           )))
  (push-proof-log 'compute (if-test-index))
  (push-proof-log 'if-true index))



;;; Log transformation of (= x y) to (false) or (false) to (= x y)
;;; based on strict inequality between x and y (i is 2 or 3).

(defun log-justify-strict (node1 node2 i index)
  (cond ((eq node1 *false-node*)
         (push-proof-log
	  'if-equal index `(= (false) ,(e-node-attribute node2)) t)
         (push-proof-log 'look-up (if-left-index)
                         (e-node-attribute node2))
         ;; (if (= (false) (= x y)) (= x y) (false))
         (log-justify-strict-aux node2 i (cons 2 (if-test-index)))
         (push-proof-log 'compute (if-test-index))
         (push-proof-log 'if-true index))
        (t (log-justify-strict-aux node1 i index))))

(defun log-justify-strict-aux (node i index)
  ;; (= x y)
  (log-sum-conversion-of-= node index)
  (let ((expr (raw-expr-of-sum (sum-of-node node 0))))
    (log-convert-boolean-to-coerced `(= ,expr 0) index)
    ;; (if (= sum 0) (true) (false))
    (cond ((= i 2)
           (push-proof-log 'if-equal (if-left-index)
                           `(= (true) (>= (+ -1 ,expr) 0))
			   t)
           (push-proof-log 'look-up (cons 2 (if-left-index))
                           `(>= (+ -1 ,expr) 0))
           ;; (if (= sum 0)
           ;;     (if (= (true) (>= (+ -1 sum) 0)) (>= (+ -1 sum) 0) (true))
           ;;     (false))
           (push-proof-log 'look-up (list* 2 1 2 (if-left-index)) 0)
           (push-proof-log 'compute (list* 1 2 (if-left-index)))
           (push-proof-log 'compute (cons 2 (if-left-index)))
           ;; (if (= sum 0)
           ;;     (if (= (true) (>= (+ -1 sum) 0)) (false) (true))
           ;;     (false))
	   (cond ((integerp expr)
		  (push-proof-log 'compute (list* 1 2 1 (if-left-index))))
		 (t
		  (log-use-axiom-as-rewrite
		   `(+ -1 ,expr) '+.associate.left
		   `((= |)X| -1) (= |)Y| ,(second expr)) (= |)Z| ,(third expr)))
		   (list* 1 2 1 (if-left-index)))
		  (push-proof-log 'compute (list* 1 1 2 1 (if-left-index)))))
           ;; (if (= sum 0) (if (= (true) (>= sum2 0)) (false) (true)) (false))
           )
          (t
           (push-proof-log 'if-equal (if-left-index)
                           `(= (true) (>= (+ -1 (negate ,expr)) 0))
			   t)
           (push-proof-log 'look-up (cons 2 (if-left-index))
                           `(>= (+ -1 (negate ,expr)) 0))
           ;; (if (= sum 0)
           ;;     (if (= (true) (>= (+ -1 (negate sum)) 0))
           ;;         (>= (+ -1 (negate sum)) 0)
           ;;         (true))
           ;;     (false))
           (push-proof-log 'look-up (list* 1 2 1 2 (if-left-index)) 0)
           (push-proof-log 'compute (list* 2 1 2 (if-left-index)))
           (push-proof-log 'compute (list* 1 2 (if-left-index)))
           (push-proof-log 'compute (cons 2 (if-left-index)))
           ;; (if (= sum 0)
           ;;     (if (= (true) (>= (+ -1 (negate sum)) 0)) (false) (true))
           ;;     (false))
           (log-push-negate-into-sum expr (list* 2 1 2 1 (if-left-index)))
           (let ((expr2 (raw-expr-of-sum (sum-of-node node 1)))) ;-sum
	     (cond ((integerp expr2)
		    (push-proof-log 'compute (list* 1 2 1 (if-left-index))))
		   (t
		    (log-use-axiom-as-rewrite
		     `(+ -1 ,expr2) '+.associate.left
		     `((= |)X| -1) (= |)Y| ,(second expr2))
		       (= |)Z| ,(third expr2)))
		     (list* 1 2 1 (if-left-index)))
		    (push-proof-log 'compute (list* 1 1 2 1 (if-left-index)))))
             ;; (if (= sum 0)
             ;;     (if (= (true) (>= sum3 0)) (false) (true))
             ;;     (false))
             )))
    (log-justify-restriction node i (list* 2 1 (if-left-index)))
    (push-proof-log 'compute (cons 1 (if-left-index)))
    (push-proof-log 'if-true (if-left-index))
    ;; (if (= sum 0) (false) (false))
    (push-proof-log 'if-equal index)))



;;; Log transformation of (>= x y) to (true) or (false), or
;;; (true) or (false) to (>= x y)

(defun log-justify-restrict (node1 node2 index)
  (cond ((eq node1 *true-node*)
         (push-proof-log
	  'if-equal index `(= (true) ,(e-node-attribute node2)) t)
         (push-proof-log 'look-up (if-left-index)
                         (e-node-attribute node2))
         ;; (if (= (true) (>= x y)) (>= x y) (true))
         (log-sum-conversion-of->= node2 (cons 2 (if-test-index)))
         (log-justify-restriction node2 0 (cons 2 (if-test-index)))
         (push-proof-log 'compute (if-test-index))
         (push-proof-log 'if-true index))
        ((eq node2 *true-node*)
         (log-sum-conversion-of->= node1 index)
         (log-justify-restriction node1 0 index))
        ((eq node1 *false-node*)
         (push-proof-log
	  'if-equal index `(= (false) ,(e-node-attribute node2)) t)
         (push-proof-log 'look-up (if-left-index)
                         (e-node-attribute node2))
         ;; (if (= (false) (>= x y)) (>= x y) (false))
         (log-justify-restrict-aux node2 (cons 2 (if-test-index)))
         (push-proof-log 'compute (if-test-index))
         (push-proof-log 'if-true index))
        (t (log-justify-restrict-aux node1 index))))

(defun log-justify-restrict-aux (node index)
  (log-sum-conversion-of->= node index)
  (let ((expr (raw-expr-of-sum (sum-of-node node 0))))
    (log-convert-boolean-to-coerced `(>= ,expr 0) index)
    ;; (if (>= sum 0) (true) (false))
    (push-proof-log
     'if-equal (if-left-index) `(= (true) (>= (negate ,expr) 1)) t)
    (push-proof-log 'look-up (cons 2 (if-left-index))
                    `(>= (negate ,expr) 1))
    ;; (if (>= sum 0)
    ;;     (if (= (true) (>= (negate sum) 1)) (>= (negate sum) 1) (true))
    ;;     (false))
    (log-use-axiom-as-rewrite
     `(>= (negate ,expr) 1) 'inconsistent.restrictions `((= |)X| ,expr))
     (cons 2 (if-left-index)))
    (push-proof-log 'look-up (list* 1 2 (if-left-index)) *true*)
    (push-proof-log 'if-true (cons 2 (if-left-index)))
    ;; (if (>= sum 0)
    ;;     (if (= (true) (>= (negate sum) 1)) (false) (true))
    ;;     (false))
    (log-push-negate-into-sum expr (list* 1 2 1 (if-left-index)))
    (let ((expr2 (raw-expr-of-sum (negative-sum (sum-of-node node 0)))))
      (log-convert->=-to->=-zero expr2 1 (list* 2 1 (if-left-index)))
      ;; (if (>= sum 0)
      ;;     (if (= (true) (>= (- nsum 1) 0)) (false) (true))
      ;;     (false))
      (cond ((integerp expr2)
	     (push-proof-log 'compute (list* 1 2 1 (if-left-index))))
	    (t
	     (log-use-axiom-as-rewrite
	      `(- ,expr2 1) '-.+.left.to.+.-.left
	      `((= |)X| ,(second expr2)) (= |)Y| ,(third expr2)) (= |)Z| 1))
	      (list* 1 2 1 (if-left-index)))
	     (push-proof-log 'compute (list* 1 1 2 1 (if-left-index)))))
      (log-justify-restriction node 1 (list* 2 1 (if-left-index)))
      ;; (if (>= sum 0) (if (= (true) (true)) (false) (true)) (false))
      (push-proof-log 'compute (cons 1 (if-left-index)))
      (push-proof-log 'if-true (if-left-index))
      (push-proof-log 'if-equal index))))



;;; Log transformation of (= x y) to (false) or (false) to (= x y)
;;; based on constant sum.

(defun log-justify-=-constant (node1 node2 i justification index)
  (cond ((eq node1 *false-node*)
         (push-proof-log
	  'if-equal index `(= (false) ,(e-node-attribute node2)) t)
         (push-proof-log 'look-up (if-left-index)
                         (e-node-attribute node2))
         ;; (if (= (false) (= x y)) (= x y) (false))
         (log-justify-=-constant-aux
          node2 i justification (cons 2 (if-test-index)))
         (push-proof-log 'compute (if-test-index))
         (push-proof-log 'if-true index))
        (t (log-justify-=-constant-aux node1 i justification index))))

(defun log-justify-=-constant-aux (node i justification index)
  (log-sum-conversion-of-= node index)
  ;; (= sum 0)
  (cond
   ((eq justification 'sum-is-one) ; sum is 1 or -1
    (push-proof-log 'compute index))
   (t (let* ((triples (third justification))
             (lcm (apply #'lcm (mapcar #'(lambda (u) (denominator (car u)))
                                       triples))))
        (let ((c (if (= i 0) lcm (- lcm)))
              (expr (raw-expr-of-sum (sum-of-node node 0))))
          (unless (= c 1)
            (push-proof-log 'if-equal index
                            `(= (= ,expr 0) (= (* ,c ,expr) (* ,c 0)))
			    t)
            (push-proof-log 'look-up (if-left-index)
                            `(= (* ,c ,expr) (* ,c 0)))
            (push-proof-log 'compute (cons 2 (if-left-index)))
            ;; (if (= (= sum 0) (= (* c sum) (* c 0)))
            ;;     (= (* c sum) 0)
            ;;     (= sum 0))
            (log-remove-common-multiplier c expr 0 (cons 2 (if-test-index)))
            ;; (if (= (= sum 0) (= sum 0)) (= (* c sum) 0) (= sum 0))
            (push-proof-log 'compute (if-test-index))
            (push-proof-log 'if-true index)
            ;; (= (* c sum) 0)
            (log-push-multiplier-in c expr (cons 1 index))
            )
          (log-remove-dead-triples
           (cons (* c (car (sum-of-node node 0)))
                 (mapcar #'(lambda (u) (cons (car u) (* c (cdr u))))
                         (cdr (sum-of-node node 0))))
           (mapcar #'(lambda (u) (cons (* c (car u)) (cdr u))) triples)
           (cons 1 index))
          ;; (= k 0)
          (push-proof-log 'compute index))))))



;;; Log transformation of (>= x y) to (true) or (false) or
;;; (true) or (false) to (>= x y) because of a constant sum.

(defun log-justify->=-constant (node1 node2 i justification index)
  (cond ((or (eq node1 *false-node*) (eq node1 *true-node*))
         (let ((expr1 (e-node-attribute node1))
               (expr2 (e-node-attribute node2)))
           (push-proof-log 'if-equal index `(= ,expr1 ,expr2) t)
           (push-proof-log 'look-up (if-left-index) expr2)
           ;; (if (= t-or-f (>= x y)) (>= x y) t-or-f)
           (log-justify->=-constant-aux
            node2 i justification (cons 2 (if-test-index)))
           (push-proof-log 'compute (if-test-index))
           (push-proof-log 'if-true index)))
        (t (log-justify->=-constant-aux node1 i justification index))))

(defun log-justify->=-constant-aux (node i justification index)
  (log-sum-conversion-of->= node index)
  ;; (>= sum 0)
  (cond
   ((eq justification 'sum-is-one) ; sum is 1 or -2
    (push-proof-log 'compute index))
   ((= i 0) (log-justify->=-constant-true node (third justification) index))
   (t (log-justify->=-constant-false node (third justification) index))))

(defun log-justify->=-constant-true (node triples index)
 (let ((c (apply #'lcm (mapcar #'(lambda (u) (denominator (car u))) triples)))
       (expr (raw-expr-of-sum (sum-of-node node 0))))
   (unless (= c 1)
    (push-proof-log 'if-equal index `(= (>= ,expr 0) (>= (* ,c ,expr) 0)) t)
    (push-proof-log 'look-up (if-left-index) `(>= (* ,c ,expr) 0))
    ;; (if (= (>= sum 0) (>= (* c sum) 0)) (>= (* c sum) 0) (>= sum 0))
    (log-use-axiom-as-rewrite
     `(>= (* ,c ,expr) 0) '*.>=.zero.>=.one.left `((= |)X| ,c) (= |)Y| ,expr))
     (cons 2 (if-test-index)))
    (push-proof-log 'compute (list* 1 2 (if-test-index)))
    (push-proof-log 'if-true (cons 2 (if-test-index)))
    ;; (if (= (>= sum 0)
    ;;        (if (= (type-of sum) (int)) (>= sum 0) (>= (* c sum) 0)))
    ;;     (>= (* c sum) 0)
    ;;     (>= sum 0))
    (log-type-of-expr expr (list* 1 1 2 (if-test-index)))
    (push-proof-log 'compute (list* 1 2 (if-test-index)))
    (push-proof-log 'if-true (cons 2 (if-test-index)))
    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)
    ;; (>= (* c sum) 0)
    (log-push-multiplier-in c expr (cons 1 index))
    )
   (log-remove-dead-triples
    (cons (* c (car (sum-of-node node 0)))
          (mapcar #'(lambda (u) (cons (car u) (* c (cdr u))))
                  (cdr (sum-of-node node 0))))
    (mapcar #'(lambda (u) (cons (* c (car u)) (cdr u))) triples)
    (cons 1 index))
   (push-proof-log 'compute index)))



(defun log-justify->=-constant-false (node triples index)
 (let ((expr (raw-expr-of-sum (sum-of-node node 0))))
   (log-convert-boolean-to-coerced `(>= ,expr 0) index)
   ;; (if (>= sum 0) (true) (false))
   (push-proof-log
    'if-equal (if-left-index) `(= (true) (>= (negate ,expr) 1)) t)
   (push-proof-log 'look-up (cons 2 (if-left-index))
                   `(>= (negate ,expr) 1))
   ;; (if (>= sum 0)
   ;;     (if (= (true) (>= (negate sum) 1)) (>= (negate sum) 1) (true))
   ;;     (false))
   (log-use-axiom-as-rewrite
    `(>= (negate ,expr) 1) 'inconsistent.restrictions `((= |)X| ,expr))
    (cons 2 (if-left-index)))
   (push-proof-log 'look-up (list* 1 2 (if-left-index)) *true*)
   (push-proof-log 'if-true (cons 2 (if-left-index)))
   ;; (if (>= sum 0)
   ;;     (if (= (true) (>= (negate sum) 1)) (false) (true))
   ;;     (false))
   (log-push-negate-into-sum expr (list* 1 2 1 (if-left-index)))
   (let ((expr2 (raw-expr-of-sum (negative-sum (sum-of-node node 0)))))
     (log-convert->=-to->=-zero expr2 1 (list* 2 1 (if-left-index)))
     ;; (if (>= sum 0)
     ;;     (if (= (true) (>= (- nsum 1) 0)) (false) (true))
     ;;     (false))
     (cond ((integerp expr2)
	    (push-proof-log 'compute (list* 1 2 1 (if-left-index))))
	   (t
	    (log-use-axiom-as-rewrite
	     `(- ,expr2 1) '-.+.left.to.+.-.left
	     `((= |)X| ,(second expr2)) (= |)Y| ,(third expr2)) (= |)Z| 1))
	     (list* 1 2 1 (if-left-index)))
	    (push-proof-log 'compute (list* 1 1 2 1 (if-left-index)))))
     ;; (if (>= sum 0)
     ;;     (if (= (true) (>= sum1 0)) (false) (true))
     ;;     (false))
     (log-justify->=-constant-false-aux
      node triples (list* 2 1 (if-left-index)))
     (push-proof-log 'compute (cons 1 (if-left-index)))
     (push-proof-log 'if-true (if-left-index))
     ;; (if (>= sum 0) (false) (false))
     (push-proof-log 'if-equal index))))

;;; (>= sum 0) where sum is the opposite sum.

(defun log-justify->=-constant-false-aux (node triples index)
  (let ((c (apply #'lcm (mapcar #'(lambda (u) (denominator (car u))) triples)))
        (expr (raw-expr-of-sum (sum-of-node node 1))))
   (unless (= c 1)
    (push-proof-log 'if-equal index `(= (>= ,expr 0) (>= (* ,c ,expr) 0)) t)
    (push-proof-log 'look-up (if-left-index) `(>= (* ,c ,expr) 0))
    ;; (if (= (>= sum 0) (>= (* c sum) 0)) (>= (* c sum) 0) (>= sum 0))
    (log-use-axiom-as-rewrite
     `(>= (* ,c ,expr) 0) '*.>=.zero.>=.one.left `((= |)X| ,c) (= |)Y| ,expr))
     (cons 2 (if-test-index)))
    (push-proof-log 'compute (list* 1 2 (if-test-index)))
    (push-proof-log 'if-true (cons 2 (if-test-index)))
    ;; (if (= (>= sum 0)
    ;;        (if (= (type-of sum) (int)) (>= sum 0) (>= (* c sum) 0)))
    ;;     (>= (* c sum) 0)
    ;;     (>= sum 0))
    (log-type-of-expr expr (list* 1 1 2 (if-test-index)))
    (push-proof-log 'compute (list* 1 2 (if-test-index)))
    (push-proof-log 'if-true (cons 2 (if-test-index)))
    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)
    ;; (>= (* c sum) 0)
    (log-push-multiplier-in c expr (cons 1 index))
    )
   (log-remove-dead-triples
    (cons (* c (car (sum-of-node node 1)))
          (mapcar #'(lambda (u) (cons (car u) (* c (cdr u))))
                  (cdr (sum-of-node node 1))))
    (mapcar #'(lambda (u) (cons (* c (car u)) (cdr u))) triples)
    (cons 1 index))
   (push-proof-log 'compute index)))



;;; Log transformation of expr to i or i to expr based on constant sum.

(defun log-justify-integer (node1 node2 justification index)
  (cond ((integerp (e-node-attribute node1))
         (push-proof-log 'if-equal index `(= ,(e-node-attribute node1)
					     ,(e-node-attribute node2))
			 t)
         (push-proof-log 'look-up (if-left-index)
                         (e-node-attribute node2))
         ;; (if (= i expr) expr i)
         (log-justify-integer-aux
          node2 (e-node-attribute node1) justification
          (cons 2 (if-test-index)))
         (push-proof-log 'compute (if-test-index))
         (push-proof-log 'if-true index))
        (t (log-justify-integer-aux
            node1 (e-node-attribute node2) justification index))))

(defun log-justify-integer-aux (node n justification index)
  (let ((expr (e-node-attribute node)))
    (log-collect-terms (e-node-attribute node) index)
    ;; sum
    (unless (eq justification 'sum-is-one)
      (let* ((triples (third justification))
             (c (apply #'lcm (mapcar #'(lambda (u) (denominator (car u)))
                                       triples))))
        (cond ((= c 1) 
               (log-remove-dead-triples (sum-of-node node 0) triples index))
              (t
               (push-proof-log 'if-equal index `(= ,expr ,n) t)
               (push-proof-log 'look-up (if-left-index) n)
               ;; (if (= sum n) n sum)
               (log-convert-=-to-=-zero expr n (if-left-index))
               ;; (if (= (- sum n) 0) n sum)
               (log-use-axiom-as-rewrite
                `(- ,expr ,n) '-.+.left.to.+.-.left
                `((= |)X| ,(second expr)) (= |)Y| ,(third expr)) (= |)Z| ,n))
                (cons 1 (if-test-index)))
               (push-proof-log 'compute (list* 1 1 (if-test-index)))
               ;; (if (= zum 0) n sum)
               (let ((expr2 (raw-expr-of-sum
                             (cons (- (car (sum-of-node node 0)) n)
                                   (cdr (sum-of-node node 0))))))
                 (push-proof-log 'if-equal (if-test-index)
                                 `(= (= ,expr2 0) (= (* ,c ,expr2) (* ,c 0)))
				 t)
                 (push-proof-log 'look-up (cons 2 (if-test-index))
                                 `(= (* ,c ,expr2) (* ,c 0)))
                 (push-proof-log 'compute (list* 2 2 (if-test-index)))
                 ;; (if (if (= (= zsum 0) (= (* c zsum) (* c 0)))
                 ;;         (= (* c zsum) 0)
                 ;;         (= zsum 0))
                 ;;     n
                 ;;     sum)
                 (log-remove-common-multiplier
                  c expr2 0 (list* 2 1 (if-test-index)))
                 ;; (if (if (= (= zsum 0) (= zsum 0))
                 ;;         (= (* c zsum) 0)
                 ;;         (= zsum 0))
                 ;;     n
                 ;;     sum)
                 (push-proof-log 'compute (cons 1 (if-test-index)))
                 (push-proof-log 'if-true (if-test-index))
                 ;; (if (= (* c zsum) 0) n sum)
                 (log-push-multiplier-in c expr2 (cons 1 (if-test-index)))
                 (log-remove-dead-triples
                  (cons (* c (- (car (sum-of-node node 0)) n))
                        (mapcar #'(lambda (u) (cons (car u) (* c (cdr u))))
                                (cdr (sum-of-node node 0))))
                  (mapcar #'(lambda (u) (cons (* c (car u)) (cdr u))) triples)
                  (cons 1 (if-test-index)))
                 ;; (if (= 0 0) n sum)
                 (push-proof-log 'compute (if-test-index))
                 (push-proof-log 'if-true index))))))))



;;; Log transformation of (>= x y) to (true) or (true) to (>= x y)
;;; based on node equality between x and y.

(defun log-justify->=-reflexive (node1 node2 index)
  (cond ((eq node1 *true-node*)
         (let ((expr (e-node-attribute node2)))
           (push-proof-log 'if-equal index `(= (true) ,expr) t)
           (push-proof-log 'look-up (if-left-index) expr)
           ;; (if (= (true) (>= x y)) (>= x y) (true))
           (log-node-equality (arg-1-node node2) (arg-2-node node2)
                              (list* 1 2 (if-test-index)))
           (log-use-axiom-as-rewrite
            `(>= ,(third expr) ,(third expr)) '>=.reflexive
            `((= |)X| ,(third expr))) (cons 2 (if-test-index)))
           (push-proof-log 'compute (if-test-index))
           (push-proof-log 'if-true index)))
        (t
         (let ((y (third (e-node-attribute node1))))
           (log-node-equality (arg-1-node node1) (arg-2-node node1)
                              (cons 1 index))
           (log-use-axiom-as-rewrite
            `(>= ,y ,y) '>=.reflexive `((= |)X| ,y)) index)))))



;;; Log transformation of (= x y) to (false) or (false) to (= x y)
;;; based on unsolvability of equation on linear sum.

(defun log-justify-no-integer-solution (node1 node2 sum index)
  (cond ((eq node1 *false-node*)
         (push-proof-log
	  'if-equal index `(= (false) ,(e-node-attribute node2)) t)
         (push-proof-log 'look-up (if-left-index)
                         (e-node-attribute node2))
         ;; (if (= (false) (= x y)) (= x y) (false))
	 (log-justify-no-integer-solution-aux
	  node2 sum (cons 2 (if-test-index)))
	 (push-proof-log 'compute (if-test-index))
	 (push-proof-log 'if-true index))
        (t (log-justify-no-integer-solution-aux node1 sum index))))

(defun log-justify-no-integer-solution-aux (node sum index)
  (log-sum-conversion-of-= node index)
  ;; (= sum 0)
  (cond ((null (cdr sum))
	 (push-proof-log 'compute index))
	(t
	 (let ((c (apply #'gcd (mapcar #'cdr (cdr sum))))
	       (k (car sum))
	       (expr (raw-expr-of-sum sum)))
	   (log-use-axiom-as-rewrite
	    `(= ,expr 0) '=.to.>=.and.>=.negate `((= |)X| ,expr)) index)
	   ;; (if (>= sum 0) (if (>= (negate sum) 0) (true) (false)) (false))
	   (let* ((d (mod k c))
		  (rsum (cons (- k d) (cdr sum))))
	     (log-normalize-inequality c k d (third expr) rsum (if-test-index))
	     ;; (if (>= qsum 0)
	     ;;     (if (>= (negate sum) 0) (true) (false))
	     ;;     (false))
	     (log-push-negate-into-sum expr (list* 1 1 (if-left-index)))
	     ;; (if (>= qsum 0) (if (>= nsum 0) (true) (false)) (false))
	     (let* ((k2 (- k))
		    (d2 (mod k2 c))
		    (expr2 (raw-expr-of-sum (sum-of-node node 1)))
		    (rsum2 (cons (- k2 d2) (cdr (sum-of-node node 1)))))
	       (log-normalize-inequality
		c k2 d2 (third expr2) rsum2 (cons 1 (if-left-index)))
	       ;; (if (>= qsum 0) (if (>= qsum2 0) (true) (false)) (false))
	       (let ((qsum (raw-expr-of-sum
			    (cons (quotient (car rsum) c)
				  (mapcar #'(lambda (u)
					      (cons (car u)
						    (quotient (cdr u) c)))
					  (cdr rsum)))))
		     (qsum2 (raw-expr-of-sum
			     (cons (quotient (car rsum2) c)
				   (mapcar #'(lambda (u)
					       (cons (car u)
						     (quotient (cdr u) c)))
					   (cdr rsum2))))))
		 (push-proof-log 'if-equal (cons 1 (if-left-index))
				 `(= (>= ,qsum2 0) (>= (negate ,qsum) 1))
				 t)
		 (push-proof-log 'look-up (list* 2 1 (if-left-index))
				 `(>= (negate ,qsum) 1))
		 ;; (if (>= qsum 0)
		 ;;     (if (if (= (>= qsum2 0) (>= (negate qsum) 1))
		 ;;             (>= (negate qsum) 1)
		 ;;             (>= qsum2 0))
		 ;;         (true)
		 ;;         (false))
		 ;;     (false))
		 (log-convert->=-negate-1 qsum (list* 2 1 1 (if-left-index)))
		 (push-proof-log 'compute (list* 1 1 (if-left-index)))
		 (push-proof-log 'if-true (cons 1 (if-left-index)))
		 ;; (if (>= qsum 0)
		 ;;     (if (>= (negate qsum) 1) (true) (false))
		 ;;     (false))
		 (log-use-axiom-as-rewrite
		  `(>= (negate ,qsum) 1) 'inconsistent.restrictions
		  `((= |)X| ,qsum)) (cons 1 (if-left-index)))
		 ;; (if (>= qsum 0)
		 ;;     (if (if (>= qsum 0) (false) (>= (negate qsum) 0))
		 ;;         (true)
		 ;;         (false))
		 ;;     (false))
		 (push-proof-log 'look-up (list* 1 1 (if-left-index)) *true*)
		 (push-proof-log 'if-true (cons 1 (if-left-index)))
		 (push-proof-log 'if-false (if-left-index))
		 ;; (if (>= qsum 0) (false) (false))
		 (push-proof-log 'if-equal index))))))))

(defun log-convert->=-negate-1 (sum index)
  (log-convert->=-to->=-zero `(negate ,sum) 1 index)
  ;; (>= (- (negate sum) 1) 0)
  (cond ((integerp sum)
	 (push-proof-log 'compute (list* 1 1 index))
	 (push-proof-log 'compute (cons 1 index)))
	(t
	 (log-use-axiom-as-rewrite
	  `(negate ,sum) 'negate.distribute.+
	  `((= |)X| ,(second sum)) (= |)Y| ,(third sum)))
	  (list* 1 1 index))
	 ;; (>= (- (+ (negate c) (negate rest)) 1) 0)
	 (push-proof-log 'compute (list* 1 1 1 index))
	 (log-use-axiom-as-rewrite
	  `(- (+ ,(- (second sum)) (negate ,(third sum))) 1)
	  '-.+.left.to.+.-.left
	  `((= |)X| ,(- (second sum))) (= |)Y| (negate ,(third sum)))
	    (= |)Z| 1))
	  (cons 1 index))
	 ;; (>= (+ (- -c 1) (negate rest)) 0)
	 (push-proof-log 'compute (list* 1 1 index))
	 (log-push-negate-into-sum-aux (third sum) (list* 2 1 index)))))

(defun log-normalize-inequality (c k d rest rsum index)
  (let ((k-d (- k d)))
    (push-proof-log 'if-equal (list* 1 1 index) `(= ,k (+ ,d ,k-d)) t)
    (push-proof-log 'look-up (list* 2 1 1 index) `(+ ,d ,k-d))
    ;; (>= (+ (if (= k (+ d k-d)) (+ d k-d) k) rest) 0)
    (push-proof-log 'compute (list* 2 1 1 1 index))
    (push-proof-log 'compute (list* 1 1 1 index))
    (push-proof-log 'if-true (list* 1 1 index))
    ;; (>= (+ (+ d k-d) rest) 0)
    (log-use-axiom-as-rewrite
     `(+ (+ ,d ,k-d) ,rest) '+.associate.right
     `((= |)X| ,d) (= |)Y| ,k-d) (= |)Z| ,rest)) (cons 1 index))
    ;; (>= (+ d rsum) 0)
    (log-shift-and-normalize d c rsum index)
    ;; (>= qsum 0)
    ))



;;; Log transformation of (if (true) left right) to left or
;;; left to (if (true) left right)

(defun log-justify-if-true (node1 node2 if-node index)
  (cond ((eq node1 if-node)
         (push-proof-log 'if-true index))
        (t
         (let ((if-expr (e-node-attribute if-node))
               (expr (e-node-attribute node1)))
           (push-proof-log 'if-equal index `(= ,expr ,if-expr) t)
           ;; (if (= left (if (true) left right)) left right)
           (push-proof-log 'look-up (if-left-index) if-expr)
           (push-proof-log 'if-true (cons 2 (if-test-index)))
           (push-proof-log 'compute (if-test-index))
           (push-proof-log 'if-true index)))))

;;; Log transformation of (if (false) left right) to right or
;;; right to (if (false) left right)

(defun log-justify-if-false (node1 node2 if-node index)
  (cond ((eq node1 if-node)
         (push-proof-log 'if-false index))
        (t
         (let ((if-expr (e-node-attribute if-node))
               (expr (e-node-attribute node1)))
           (push-proof-log 'if-equal index `(= ,expr ,if-expr) t)
           ;; (if (= right (if (false) left right)) right right)
           (push-proof-log 'look-up (if-left-index) if-expr)
           (push-proof-log 'if-false (cons 2 (if-test-index)))
           (push-proof-log 'compute (if-test-index))
           (push-proof-log 'if-true index)))))

;;; Log transformation of (if test left right) to left or
;;; left to (if test) left left)

(defun log-justify-if-equal (node1 node2 if-node index)
  (cond ((eq node1 if-node)
         (push-proof-log 'if-equal index))
        (t
         (let ((if-expr (e-node-attribute if-node))
               (expr (e-node-attribute node1)))
           (push-proof-log 'if-equal index `(= ,expr ,if-expr) t)
           ;; (if (= left (if test left left)) left left)
           (push-proof-log 'look-up (if-left-index) if-expr)
           (push-proof-log 'if-equal (cons 2 (if-test-index)))
           (push-proof-log 'compute (if-test-index))
           (push-proof-log 'if-true index)))))



;;; Log transformation of (= x 0) to (false) or (false) to (= x 0)
;;; based on not (= x 0).

(defun log-justify-forbid-zero (node1 node2 justification index)
  (cond ((eq node1 *false-node*)
         ;; (false) -> (= x 0)
         (let ((expr (e-node-attribute node2))) ; (= x 0)
           (push-proof-log 'if-equal index `(= (false) ,expr) t)
           (push-proof-log 'look-up (if-left-index) expr)
           ;; (if (= (false) (= x 0)) (= x 0) (false))
           (log-convert-boolean-to-coerced expr (cons 2 (if-test-index)))
           (log-convert-coerced-to-double-negate (cons 2 (if-test-index)))
           ;; (if (= (false) (if (if (= x 0) (false) (true)) (false) (true)))
           ;;     (= x 0)
           ;;     (false))
           (log-forbid-aux (arg-1-node node2) *zero-node* justification
                           (list* 1 2 (if-test-index)))
           (push-proof-log 'if-true (cons 2 (if-test-index)))
           (push-proof-log 'compute (if-test-index))
           (push-proof-log 'if-true index)))
        (t
         ;; (= x 0) -> (false)
         (let ((expr (e-node-attribute node1))) ; (= x 0)
           (push-proof-log 'if-equal index `(= ,expr (false)) t)
           (push-proof-log 'look-up (if-left-index) *false*)
           ;; (if (= (= x 0) (false)) (false) (= x 0))
           (log-convert-boolean-to-coerced expr (cons 1 (if-test-index)))
           (log-convert-coerced-to-double-negate (cons 1 (if-test-index)))
           ;; (if (= (if (if (= x 0) (false) (true)) (false) (true)) (false))
           ;;     (false)
           ;;     (= x 0))
           (log-forbid-aux (arg-1-node node1) *zero-node* justification
                           (list* 1 1 (if-test-index)))
           (push-proof-log 'if-true (cons 1 (if-test-index)))
           (push-proof-log 'compute (if-test-index))
           (push-proof-log 'if-true index)))))



;;; Log transformations of expr1 to expr2 based on the fact that
;;; they have the same sum.

(defun log-justify-same-sum (node1 node2 index)
  (let ((expr1 (e-node-attribute node1))
        (expr2 (e-node-attribute node2)))
    (push-proof-log 'if-equal index `(= ,expr1 ,expr2) t)
    (push-proof-log 'look-up (if-left-index) expr2)
    ;; (if (= expr1 expr2) expr2 expr1)
    (log-collect-terms expr1 (cons 1 (if-test-index)))
    (log-collect-terms expr2 (cons 2 (if-test-index)))
    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)))

;;; Code to log proof by contradiction.  Given P that is known to be
;;; boolean, first split using (= P (false)).  The idea is that
;;; asserting (= P (false)) causes a contradiction, which allows us
;;; to transform the left branch to (true).  The result is basically
;;; (or (= P (false)) P) which reduces to (true).

(defun log-proof-by-contradiction (node index)
  (let ((expr (e-node-attribute node)))
    ;; Start with P
    (push-proof-log 'if-equal index (make-= expr *false*) t)
    ;; We have (if (= P (false)) P P)
    (is-inconsistent *true* (if-left-index))
    ;; (if (= P (false)) (true) P)
    (push-proof-log 'if-equal index (make-= expr *true*) t)
    ;; (if (= P (true))
    ;;     (if (= P (false)) (true) P)
    ;;     (if (= P (false)) (true) P))
    (push-proof-log 'look-up (cons 3 (if-left-index)) *true*)
    (push-proof-log 'if-equal (if-left-index))
    ;; (if (= P (true)) (true) (if (= P (false)) (true) P))
    (push-proof-log 'if-true (if-left-index) expr t)
    ;; (if (= P (true))
    ;;     (if (true) (true) P)
    ;;     (if (= P (false)) (true) P))
    (push-proof-log 'case-analysis index 1 t)
    ;; (if (if (= P (true)) (true) (= P (false))) (true) P)
    (log-use-bool-definition expr (if-test-index) t)
    ;; (if (= (type-of P) (bool)) (true) P)
    (cond ((eq node *false-node*)
           (log-justify-false-is-bool
            (e-node-type node) *bool-node* (cons 1 (if-test-index))))
          ;; node is never *true-node*
          (t (log-node-equality
              (e-node-type node) *bool-node* (cons 1 (if-test-index)))))
    ;; (if (= (bool) (bool)) (true) P)
    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)
    ;; (true)
    ))



;;; Code to log refute by contradiction.  Given P that is known to be
;;; boolean, first split using (= P (true)).  The idea is that
;;; asserting (= P (true)) causes a contradiction, which allows us
;;; to transform the left branch to (false).  The result is basically
;;; (and (not (= P (true))) P) which reduces to (false).

(defun log-refute-by-contradiction (node index &optional (bool-context-p nil))
  (let ((expr (e-node-attribute node)))
    ;; Start with P
    (push-proof-log 'if-equal index (make-= expr *true*) t)
    ;; We have (if (= P (true)) P P)
    (is-inconsistent *false* (if-left-index))
    ;; (if (= P (true)) (false) P)
    (cond
     ((bool-p expr)
      (log-=-true-right-to-if (if-test-index))
      ;; (if (if P (true) (false)) (false) P)
      (log-remove-bool-coercion-from-if-test index)
      ;; (if P (false) P)
      (log-look-up-false (if-right-index))
      ;; (if P (false) (false))
      (push-proof-log 'if-equal index)
      ;; (false)
      )
     (bool-context-p
      (log-=-true-right-to-if (if-test-index))
      ;; (if (if P (true) (false)) (false) P)
      (log-remove-bool-coercion-from-if-test index)
      ;; (if P (false) P)
      (log-look-up-false-in-boolean-context bool-context-p (if-right-index))
      ;; (if P (false) (false))
      (push-proof-log 'if-equal index)
      ;; (false)
      )
     (t
      (push-proof-log 'if-equal (if-right-index) (make-= expr *false*) t)
      (push-proof-log 'look-up (cons 2 (if-right-index)) *false*)
      ;; (if (= P (true))
      ;;     (false)
      ;;     (if (= P (false)) (false) P))
      (push-proof-log 'if-true (if-left-index) expr t)
      ;; (if (= P (true))
      ;;     (if (true) (false) P)
      ;;     (if (= P (false)) (false) P))
      (push-proof-log 'case-analysis index 1 t)
      ;; (if (if (= P (true)) (true) (= P (false))) (false) P)
      (log-use-bool-definition expr (if-test-index) t)
      ;; (if (= (type-of P) (bool)) (false) P)
      (cond ((eq node *true-node*)
	     (log-justify-true-is-bool
	      (e-node-type node) *bool-node* (cons 1 (if-test-index))))
	    ;; node is never *false-node*
	    (t (log-node-equality
		(e-node-type node) *bool-node* (cons 1 (if-test-index)))))
      ;; (if (= (bool) (bool)) (false) P)
      (push-proof-log 'compute (if-test-index))
      (push-proof-log 'if-true index)
      ;; (false)
      ))))



;;; Code to log the conversion of (= (type-of P) (bool)) to
;;; (if (= P (true)) (true) (= P (false))) or vice-versa (if reverse).

(defun log-use-bool-definition (expr index reverse)
  (log-use-simple-axiom 'bool.definition.2 expr index reverse))


;;; Code to log the use of a simple axiom as a rewrite.
;;; The simple axiom must have the form of an unconditional
;;; rewrite rule with only one parameter and no quantification.
;;; If reverse is non-nil, it rewrites backwards.

(defun log-use-simple-axiom (axiom-name expr index reverse)
  (let* ((event (get-event axiom-name))
         (oldvar (car (axiom-args event)))
         (newvar (genvar oldvar))
         (result (if reverse
                     (subst-eq expr oldvar (=-left (axiom-formula event)))
                   (subst-eq expr oldvar (=-right (axiom-formula event))))))
    ;; Start with (L expr) or (R expr)
    (log-use-axiom index axiom-name)
    ;; (if (all (x) (= (L x) (R x))) (L expr) (true))
    (push-proof-log 'rename-universal (if-test-index) oldvar newvar)
    (push-proof-log 'instantiate-universal (if-test-index)
                    (make-= newvar expr))
    ;; (if (if (= (L expr) (R expr))
    ;;         (all (n) (= (L n) (R n)))
    ;;         (false))
    ;;     (L expr)
    ;;     (true))
    (push-proof-log 'case-analysis index 1)
    ;; (if (= (L expr) (R expr))
    ;;     (if (all (n) (= (L n) (R n))) (L expr) (true))
    ;;     (if (false) (L expr) (true)))
    (push-proof-log 'if-false (if-right-index))
    ;; (if (= (L expr) (R expr))
    ;;     (if (all (n) (= (L n) (R n))) (L expr) (true))
    ;;     (true))
    (push-proof-log 'look-up (cons 2 (if-left-index)) result)
    ;; (if (= (L expr) (R expr))
    ;;     (if (all (n) (= (L n) (R n))) (R expr) (true))
    ;;     (true))
    (push-proof-log 'if-false (if-right-index) result t)
    (push-proof-log 'case-analysis index 1 t)
    ;; (if (if (= (L expr) (R expr))
    ;;         (all (n) (= (L n) (R n)))
    ;;         (false))
    ;;     (R expr)
    ;;     (true))
    (push-proof-log 'instantiate-universal (if-test-index)
		    (make-= newvar expr) t)
    ;; (if (all (n) (= (L n) (R n)))
    ;;     (R expr)
    ;;     (true))
    (push-proof-log 'rename-universal (if-test-index) newvar oldvar)
    (push-proof-log 'use-axiom (if-test-index) axiom-name t)
    (push-proof-log 'if-true index)
    ;; (R expr) or (L expr)
    ))



;;; Transformation of (type-of expr) to (char), (bool) or (int) or
;;; (char), (bool) or (int) to (type-of expr).

(defun log-type-of (node1 node2 index)
  (cond ((type-of-p (e-node-attribute node1))
         (log-type-of-expr (second (e-node-attribute node1)) index))
        (t
         (let ((expr1 (e-node-attribute node1))
               (expr2 (e-node-attribute node2)))
           (push-proof-log 'if-equal index `(= ,expr1 ,expr2) t)
           (push-proof-log 'look-up (if-left-index) expr2)
           ;; (if (= type (type-of expr)) (type-of expr) type)
           (log-type-of-expr
            (second (e-node-attribute node2)) (cons 2 (if-test-index)))
           (push-proof-log 'compute (if-test-index))
           (push-proof-log 'if-true index)
           ;; (type-of expr)
           ))))

;;; Log transformation of (type-of expr) to (int), (bool), or (char).

(defun log-type-of-expr (expr index)
  (cond ((or (integerp expr) (true-p expr) (false-p expr) (characterp expr)
             (stringp expr))
         (push-proof-log 'compute index))
        ((or (all-p expr) (some-p expr))
         (push-proof-log 'is-boolean (cons 1 index))
         ;; (type-of (if expr (true) (false)))
         (push-proof-log 'case-analysis index 1)
         ;; (if expr (type-of (true)) (type-of (false)))
         (push-proof-log 'compute (if-left-index))
         (push-proof-log 'compute (if-right-index))
         (push-proof-log 'if-equal index))
        ((and-p expr)
         (cond ((null (cdr expr))
                (log-and-0 (cons 1 index))
                (push-proof-log 'compute index))
               ((null (cddr expr))
                (log-and-1 (cons 1 index))
                (log-type-of-expr `(if ,(second expr) ,*true* ,*false*) index))
               ((null (cdddr expr))
                (log-type-of-expr-aux expr index))
               (t (push-proof-log 'syntax (cons 1 index))
                  (log-type-of-expr-aux
                   `(and ,(second expr) ,(cons 'and (cddr expr))) index))))
        ((or-p expr)
         (cond ((null (cdr expr))
                (log-or-0 (cons 1 index))
                (push-proof-log 'compute index))
               ((null (cddr expr))
                (log-or-1 (cons 1 index))
                (log-type-of-expr `(if ,(second expr) ,*true* ,*false*) index))
               ((null (cdddr expr))
                (log-type-of-expr-aux expr index))
               (t (push-proof-log 'syntax (cons 1 index))
                  (log-type-of-expr-aux
                   `(or ,(second expr) ,(cons 'or (cddr expr))) index))))
        ((+-p expr)
         (cond ((null (cdr expr))
                (push-proof-log 'syntax (cons 1 index))
                (push-proof-log 'compute (cons 1 index))
                (push-proof-log 'compute index))
               ((null (cddr expr))
                (push-proof-log 'syntax (cons 1 index))
                (log-type-of-expr-aux `(+ ,(second expr) 0) index))
               ((null (cdddr expr))
                (log-type-of-expr-aux expr index))
               (t (push-proof-log 'syntax (cons 1 index))
                  (log-type-of-expr-aux
                   `(+ ,(second expr) ,(cons '+ (cddr expr))) index))))
        ((*-p expr)
         (cond ((null (cdr expr))
                (push-proof-log 'syntax (cons 1 index))
                (push-proof-log 'compute (cons 1 index))
                (push-proof-log 'compute index))
               ((null (cddr expr))
                (push-proof-log 'syntax (cons 1 index))
                (log-type-of-expr `(* ,(second expr) 1) index))
               ((null (cdddr expr))
                (log-type-of-expr-aux expr index))
               (t (push-proof-log 'syntax (cons 1 index))
                  (log-type-of-expr-aux
                   `(* ,(second expr) ,(cons '* (cddr expr))) index))))
        ((and (and-p expr) (null (cddr expr)))
         (log-and-0 (cons 1 index)))
        ((if-p expr)
         (push-proof-log 'case-analysis index 1)
         ;; (if test (type-of left) (type-of right))
         (log-type-of-expr (if-left expr) (if-left-index))
         (log-type-of-expr (if-right expr) (if-right-index))
         (push-proof-log 'if-equal index))
        (t (log-type-of-expr-aux expr index))))

(defun log-type-of-expr-aux (expr index)
  (let* ((axiom-name (intern (string-append (car expr) ".TYPE-OF-AXIOM")
			     *zk-package*))
	 (axiom (get-axiom axiom-name))
	 (vars (list-of-leading-universals axiom)))
    (log-use-axiom-as-rewrite
     `(type-of ,expr) axiom-name
     (mapcar #'make-= vars (cdr expr))
     index)))



(defun log-commute-= (left right index)
  ;; Start with (= L R)
  (let* ((axiom (get-event '=.commutes))
         (pattern (=-left (axiom-formula axiom)))
         (value (=-right (axiom-formula axiom))))
     (multiple-value-bind (substitutions match-success)
       (match-pattern-formula pattern (make-= left right))
      (cond ((not match-success) (format t "~%Problem Here!~%"))
            (t (log-use-axiom index '=.commutes)
               (log-rewrite
                (make-if (make-series-of-quantification
                          'all (axiom-args axiom) (make-= pattern value))
                         (axiom-formula axiom)
                         *true*)
                        (mapcar #'(lambda (u) (make-= (car u) (cdr u)))
                                substitutions)
                        index)
               (push-proof-log 'use-axiom (if-test-index) '=.commutes t)
               (push-proof-log 'if-true index))))))



;;; log-if-not-true logs the transformation of (if test left right) to
;;; right if (if (= test (true)) (false) (true)) is in the context.

(defun log-if-not-true (test left right index)
  ;; Start with (if test left right)
  (push-proof-log 'if-true (if-left-index) right t)
  ;; We now have (if test (if (true) left right) right)
  (log-true-to-= test (cons 1 (if-left-index)))
  ;; (if test (if (= test test) left right) right)
  (push-proof-log 'look-up (list* 2 1 (if-left-index)) *true*)
  ;; (if test (if (= test (true)) left right) right)
  (push-proof-log 'if-false (cons 2 (if-left-index)) right t)
  (push-proof-log 'if-true (cons 3 (if-left-index)) left t)
  ;; (if test
  ;;     (if (= test (true))
  ;;         (if (false) right left)
  ;;         (if (true) right left))
  ;;     right)
  (push-proof-log 'case-analysis (if-left-index) 1 t)
  ;; (if test
  ;;     (if (if (= test (true)) (false) (true))
  ;;         right
  ;;         left)
  ;;     right)
  (push-proof-log 'look-up (cons 1 (if-left-index)) *true*)
  ;; (if test (if (true) right left) right)
  (push-proof-log 'if-true (if-left-index))
  ;; (if test right right)
  (push-proof-log 'if-equal index)
  ;; right
  )

;;; log-convert-test-from-equal-true logs the conversion from
;;; (if (= test (true)) left right) to (if test left right)



;;; Code to log the conversion of (if (= expr (true)) (true) (false)) to
;;; (if (= (type-of expr) (bool)) expr (false))

(defun log-convert-coerced-=-true (expr index)
  ;; Start with (if (= expr (true)) (true) (false))
  (push-proof-log 'look-up (if-left-index) expr)
  ;; (if (= expr (true)) expr (false))
  (push-proof-log 'if-true (if-left-index) *false* t)
  (push-proof-log 'if-equal (if-right-index) (make-= expr *false*) t)
  ;; (if (= expr (true))
  ;;     (if (true) expr (false))
  ;;     (if (= expr (false)) (false) (false)))
  (push-proof-log 'look-up (cons 2 (if-right-index)) expr)
  (push-proof-log 'case-analysis index 1 t)
  ;; (if (if (= expr (true)) (true) (= expr (false)))
  ;;     expr
  ;;     (false))
  (log-use-bool-definition expr (if-test-index) t)
  ;; (if (= (type-of expr) bool) expr (false))
  )



;;; Code to log the conversion of (if (= expr (false)) (true) (false)) to
;;; (if (= (type-of expr) (bool)) (if expr (false) (true)) (false))

(defun log-convert-coerced-=-false (expr index)
  ;; Start with (if (= expr (false)) (true) (false))
  (push-proof-log 'if-equal index (make-= expr *true*) t)
  ;; (if (= expr (true))
  ;;     (if (= expr (false)) (true) (false))
  ;;     (if (= expr (false)) (true) (false)))
  (push-proof-log 'look-up (cons 2 (if-left-index)) expr)
  (push-proof-log 'look-up (cons 2 (if-left-index)) *false*)
  (push-proof-log 'if-equal (if-left-index))
  ;; (if (= expr (true))
  ;;     (false)
  ;;     (if (= expr (false)) (true) (false)))
  (push-proof-log 'if-equal (cons 2 (if-right-index)) (make-= expr *true*) t)
  ;; (if (= expr (true))
  ;;     (false)
  ;;     (if (= expr (false))
  ;;         (if (= expr (true)) (true) (true))
  ;;         (false)))
  (push-proof-log 'look-up (list* 2 2 (if-right-index)) expr)
  (push-proof-log 'look-up (list* 2 2 (if-right-index)) *false*)
  (push-proof-log 'if-test (cons 2 (if-right-index)) t)
  ;; (log-convert-test-from-equal-true
  ;;  expr *false* *true* (cons 2 (if-right-index)))
  ;; (if (= expr (true))
  ;;     (false)
  ;;     (if (= expr (false))
  ;;         (if expr (false) (true))
  ;;         (false)))
  (push-proof-log 'if-true (if-left-index) *true* t)
  (push-proof-log 'look-up (cons 1 (if-left-index)) expr)
  ;; (if (= expr (true))
  ;;     (if expr (false) (true))
  ;;     (if (= expr (false))
  ;;         (if expr (false) (true))
  ;;         (false)))
  (push-proof-log 'if-true (if-left-index) *false* t)
  (push-proof-log 'case-analysis index 1 t)
  ;; (if (if (= expr (true)) (true) (= expr (false)))
  ;;     (if expr (false) (true))
  ;;     (false))
  (log-use-bool-definition expr (if-test-index) t)
  ;; (if (= (type-of expr) bool) (if expr (false) (true)) (false))
  )



;;; Log conversion of expr to (if expr (true) (false)),
;;; where expr can be shown to be boolean using log-type-of-expr.

(defun log-convert-boolean-to-coerced (expr index)
  ;; expr
  (push-proof-log 'if-equal index `(= ,expr (true)) t)
  ;; (if (= expr (true)) expr expr)
  (push-proof-log 'if-equal (if-right-index) `(= ,expr (false)) t)
  ;; (if (= expr (true)) expr (if (= expr (false)) expr expr))
  (push-proof-log 'if-true (if-left-index) *false* t)
  ;; (if (= expr (true))
  ;;     (if (true) expr (false))
  ;;     (if (= expr (false)) expr expr))
  (push-proof-log 'look-up (cons 1 (if-left-index)) expr)
  (push-proof-log 'look-up (cons 2 (if-left-index)) *true*)
  (push-proof-log 'if-true (if-left-index) expr t)
  ;; (if (= expr (true))
  ;;     (if (true) (if expr (true) (false)) expr)
  ;;     (if (= expr (false)) expr expr))
  (push-proof-log 'if-equal (cons 2 (if-right-index)) expr t)
  ;; (if (= expr (true))
  ;;     (if (true) (if expr (true) (false)) expr)
  ;;     (if (= expr (false)) (if expr expr expr) expr))
  (push-proof-log 'look-up (list* 2 2 (if-right-index)) *true*)
  (push-proof-log 'look-up (list* 3 2 (if-right-index)) *false*)
  ;; (if (= expr (true))
  ;;     (if (true) (if expr (true) (false)) expr)
  ;;     (if (= expr (false)) (if expr (true) (false)) expr))
  (push-proof-log 'case-analysis index 1 t)
  ;; (if (if (= expr (true)) (true) (= expr (false)))
  ;;     (if expr (true) (false))
  ;;     expr)
  (log-use-bool-definition expr (if-test-index) t)
  ;; (if (= (type-of expr) (bool)) (if expr (true) (false)) expr)
  (log-type-of-expr expr (cons 1 (if-test-index)))
  (push-proof-log 'compute (if-test-index))
  (push-proof-log 'if-true index)
  ;; (if expr (true) (false))
  )



;;; Log transformation of (if expr (true) (false)) to
;;; (if (if expr (false) (true)) (false) (true))

(defun log-convert-coerced-to-double-negate (index)
  ;; (if expr (true) (false))
  (push-proof-log 'if-false (if-left-index) *false* t)
  (push-proof-log 'if-true (if-right-index) *true* t)
  ;; (if expr (if (false) (false) (true)) (if (true) (false) (true)))
  (push-proof-log 'case-analysis index 1 t)
  ;; (if (if expr (false) (true)) (false) (true))
  )

(defun log-coerce-test (left right index)
  (push-proof-log 'if-true (if-left-index) right t)
  (push-proof-log 'if-false (if-right-index) left t)
  ;; (if test (if (true) left right) (if (false) left right))
  (push-proof-log 'case-analysis index 1 t))

(defun log-double-negate-test (left right index)
  (push-proof-log 'if-false (if-left-index) right t)
  (push-proof-log 'if-true (if-right-index) left t)
  ;; (if test (if (false) right left) (if (true) right left))
  (push-proof-log 'case-analysis index 1 t)
  (push-proof-log 'if-false (if-left-index) left t)
  (push-proof-log 'if-true (if-right-index) right t)
  ;; (if (if test (false) (true))
  ;;     (if (false) left right)
  ;;     (if (true) left right))
  (push-proof-log 'case-analysis index 1 t)
  ;; (if (if (if test (false) (true)) (false) (true)) left right)
  )



(defun log-justify-from-assume-if (node1 node2 kind index)
  (case kind
    (regular (log-justify-from-assume-if-aux node1 node2 index))
    (test (log-justify-from-assume-if-test-aux node1 node2 index))
    (right (log-justify-from-assume-if-right-aux node1 node2 index))))

;;; Log transformation of expr to (if (if x1 x2 (false)) expr (true)) to
;;; (true)
;;; where expr is either x1 or x2,
;;; node1 represents expr and
;;; node2 represents (if x1 x2 (false))

(defun log-justify-from-assume-if-aux (node1 node2 index)
  (let* ((expr (e-node-attribute node1))
         (equality-expr `(= ,expr (if (true) ,expr (true)))))
    (push-proof-log 'if-equal index equality-expr t)
    (push-proof-log 'look-up (if-left-index) (=-right equality-expr))
    ;; (if (= expr (if (true) expr (true))) (if (true) expr (true)) expr)
    (push-proof-log 'if-true (cons 2 (if-test-index)))
    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)
    ;; (if (true) expr (true))
    (log-node-equality *true-node* node2 (if-test-index))
    ;; (if (if x1 x2 (false)) expr (true))
    (push-proof-log 'case-analysis index 1)
    ;; (if x1 (if x2 expr (true)) (if (false) expr (true)))
    (push-proof-log 'look-up (cons 2 (if-left-index)) *true*)
    (push-proof-log 'if-equal (if-left-index))
    (push-proof-log 'if-false (if-right-index))
    (push-proof-log 'if-equal index)))

;;; Log transformation of expr to (if (if x1 (false) expr) expr (true)) to
;;; (true)
;;; where node1 represents expr and
;;; node2 represents (if x1 (false) expr)

(defun log-justify-from-assume-if-right-aux (node1 node2 index)
  (let* ((expr (e-node-attribute node1))
         (equality-expr `(= ,expr (if (true) ,expr (true)))))
    (push-proof-log 'if-equal index equality-expr t)
    (push-proof-log 'look-up (if-left-index) (=-right equality-expr))
    ;; (if (= expr (if (true) expr (true))) (if (true) expr (true)) expr)
    (push-proof-log 'if-true (cons 2 (if-test-index)))
    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)
    ;; (if (true) expr (true))
    (log-node-equality *true-node* node2 (if-test-index))
    ;; (if (if x1 (false) expr) expr (true))
    (push-proof-log 'case-analysis index 1)
    ;; (if x1 (if (false) expr (true)) (if expr expr (true)))
    (push-proof-log 'if-false (if-left-index))
    (push-proof-log 'look-up (cons 2 (if-right-index)) *true*)
    (push-proof-log 'if-equal (if-right-index))
    (push-proof-log 'if-equal index)))



;;; Log transformation of expr to
;;; (if (if (if expr x2 (true)) (false) (true)) expr (true)) to
;;; (true)
;;; where node1 represents expr and
;;; node2 represents (if expr x2 (true))

(defun log-justify-from-assume-if-test-aux (node1 node2 index)
  (let* ((expr (e-node-attribute node1))
         (equality-expr `(= ,expr (if (true) ,expr (true))))
         (expr2 (e-node-attribute node2))
         (equality-expr2
          `(= (true) (if (= ,expr2 (true)) (false) (true)))))
    (push-proof-log 'if-equal index equality-expr t)
    (push-proof-log 'look-up (if-left-index) (=-right equality-expr))
    ;; (if (= expr (if (true) expr (true))) (if (true) expr (true)) expr)
    (push-proof-log 'if-true (cons 2 (if-test-index)))
    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)
    ;; (if (true) expr (true))
    (push-proof-log 'if-equal index equality-expr2 t)
    (push-proof-log 'look-up (cons 1 (if-left-index))
                    (=-right equality-expr2))
    ;; (if (= (true) (if (= (if expr x2 (true)) (true)) (false) (true)))
    ;;     (if (if (= (if expr x2 (true)) (true)) (false) (true)) expr (true))
    ;;     (if (true) expr (true)))
    (log-forbid node2 *true-node* (cons 2 (if-test-index)))
    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)
    ;; (if (if (= (if expr x2 (true)) (true)) (false) (true)) expr (true))
    (push-proof-log 'if-test (if-test-index) t)
    ;; (log-convert-test-from-equal-true expr2 *false* *true* (if-test-index))
    ;; (if (if (if expr x2 (true)) (false) (true)) expr (true))
    (push-proof-log 'case-analysis index 1)
    ;; (if (if expr x2 (true))
    ;;     (if (false) expr (true))
    ;;     (if (true) expr (true)))
    (push-proof-log 'if-false (if-left-index))
    (push-proof-log 'if-true (if-right-index))
    ;; (if (if expr x2 (true)) (true) expr)
    (push-proof-log 'case-analysis index 1)
    ;; (if expr (if x2 (true) expr) (if (true) (true) expr))
    (push-proof-log 'look-up (cons 3 (if-left-index)) *true*)
    (push-proof-log 'if-equal (if-left-index))
    (push-proof-log 'if-true (if-right-index))
    (push-proof-log 'if-equal index)))



(defun log-justify-forbid-from-deny-if (node1 node2 kind index)
  (case kind
    (regular (log-justify-forbid-from-deny-if-aux node1 node2 index))
    (test (log-justify-forbid-from-deny-if-test-aux node1 node2 index))
    (left (log-justify-forbid-from-deny-if-left-aux node1 node2 index))))

;;; Log transformation of (if (= expr (true)) (false) (true)) to
;;; (if (if (if x1 (true) x2) (false) (true)) expr (true)) to
;;; (true)
;;; where expr is either x1 or x2,
;;; node1 represents expr and
;;; node2 represents (if x1 (true) x2)

(defun log-justify-forbid-from-deny-if-aux (node1 node2 index)
  (let* ((expr (e-node-attribute node1))
         (equality-expr1
          `(= (if ,expr (false) (true))
              (if (true) (if ,expr (false) (true)) (true))))
         (expr2 (e-node-attribute node2))
         (equality-expr2
          `(= (true) (if (= ,expr2 (true)) (false) (true)))))
    (push-proof-log 'if-test index t)
    ;; (log-convert-test-from-equal-true expr *false* *true* index)
    ;; (if expr (false) (true))
    (push-proof-log 'if-equal index equality-expr1 t)
    (push-proof-log 'look-up (if-left-index) (=-right equality-expr1))
    ;; (if (= (if expr (false) (true))
    ;;        (if (true) (if expr (false) (true)) (true)))
    ;;     (if (true) (if expr (false) (true)) (true))
    ;;     (if expr (false) (true)))
    (push-proof-log 'if-true (cons 2 (if-test-index)))
    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)
    ;;; (if (true) (if expr (false) (true)) (true))
    (push-proof-log 'if-equal index equality-expr2 t)
    (push-proof-log 'look-up (cons 1 (if-left-index))
                    (=-right equality-expr2))
    ;; (if (= (true)
    ;;        (if (= (if x1 (true) x2) (true)) (false) (true)))
    ;;     (if (if (= (if x1 (true) x2) (true)) (false) (true))
    ;;         (if expr (false) (true))
    ;;         (true)
    ;;     (if (true) (if expr (false) (true)) (true)))
    (log-forbid node2 *true-node* (cons 2 (if-test-index)))
    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)
    ;; (if (if (= (if x1 (true) x2) (true)) (false) (true))
    ;;     (if expr (false) (true))
    ;;     (true))
    (push-proof-log 'if-test (if-test-index) t)
    ;; (log-convert-test-from-equal-true expr2 *false* *true* (if-test-index))
    ;; (if (if (if x1 (true) x2) (false) (true))
    ;;     (if expr (false) (true))
    ;;     (true))
    (push-proof-log 'case-analysis index 1)
    ;; (if (if x1 (true) x2)
    ;;     (if (false) (if expr (false) (true)) (true))
    ;;     (if (true) (if expr (false) (true)) (true)))
    (push-proof-log 'if-false (if-left-index))
    (push-proof-log 'if-true (if-right-index))
    ;; (if (if x1 (true) x2) (true) (if expr (false) (true)))
    (push-proof-log 'case-analysis index 1)
    ;; (if x1
    ;;     (if (true) (true) (if expr (false) (true)))
    ;;     (if x2 (true) (if expr (false) (true))))
    (push-proof-log 'if-true (if-left-index))
    (push-proof-log 'look-up (cons 3 (if-right-index)) *true*)
    (push-proof-log 'if-equal (if-right-index))
    ;; (if x1 (true) (true))
    (push-proof-log 'if-equal index)))



;;; Log transformation of (if (= expr (true)) (false) (true)) to
;;; (if (if (if x1 expr (false)) (false) (true)) expr (true)) to
;;; (true)
;;; where node1 represents expr and
;;; node2 represents (if x1 expr (true))

(defun log-justify-forbid-from-deny-if-left-aux (node1 node2 index)
  (let* ((expr (e-node-attribute node1))
         (equality-expr1
          `(= (if ,expr (false) (true))
              (if (true) (if ,expr (false) (true)) (true))))
         (expr2 (e-node-attribute node2))
         (equality-expr2
          `(= (true) (if (= ,expr2 (true)) (false) (true)))))
    (push-proof-log 'if-test index t)
    ;; (log-convert-test-from-equal-true expr *false* *true* index)
    ;; (if expr (false) (true))
    (push-proof-log 'if-equal index equality-expr1 t)
    (push-proof-log 'look-up (if-left-index) (=-right equality-expr1))
    ;; (if (= (if expr (false) (true))
    ;;        (if (true) (if expr (false) (true)) (true)))
    ;;     (if (true) (if expr (false) (true)) (true))
    ;;     (if expr (false) (true)))
    (push-proof-log 'if-true (cons 2 (if-test-index)))
    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)
    ;;; (if (true) (if expr (false) (true)) (true))
    (push-proof-log 'if-equal index equality-expr2 t)
    (push-proof-log 'look-up (cons 1 (if-left-index))
                    (=-right equality-expr2))
    ;; (if (= (true)
    ;;        (if (= (if x1 expr (true)) (true)) (false) (true)))
    ;;     (if (if (= (if x1 expr (true)) (true)) (false) (true))
    ;;         (if expr (false) (true))
    ;;         (true)
    ;;     (if (true) (if expr (false) (true)) (true)))
    (log-forbid node2 *true-node* (cons 2 (if-test-index)))
    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)
    ;; (if (if (= (if x1 expr (true)) (true)) (false) (true))
    ;;     (if expr (false) (true))
    ;;     (true))
    (push-proof-log 'if-test (if-test-index) t)
    ;; (log-convert-test-from-equal-true expr2 *false* *true* (if-test-index))
    ;; (if (if (if x1 expr (true)) (false) (true))
    ;;     (if expr (false) (true))
    ;;     (true))
    (push-proof-log 'case-analysis index 1)
    ;; (if (if x1 expr (true))
    ;;     (if (false) (if expr (false) (true)) (true))
    ;;     (if (true) (if expr (false) (true)) (true)))
    (push-proof-log 'if-false (if-left-index))
    (push-proof-log 'if-true (if-right-index))
    ;; (if (if x1 expr (true)) (true) (if expr (false) (true)))
    (push-proof-log 'case-analysis index 1)
    ;; (if x1
    ;;     (if expr (true) (if expr (false) (true)))
    ;;     (if (true) (true) (if expr (false) (true))))
    (push-proof-log 'if-true (if-right-index))
    (push-proof-log 'look-up (cons 3 (if-left-index)) *true*)
    (push-proof-log 'if-equal (if-left-index))
    ;; (if x1 (true) (true))
    (push-proof-log 'if-equal index)))



;;; Log transformation of (if (= expr (true)) (false) (true)) to
;;; (if (if (if expr (false) x2) (false) (true)) expr (true)) to
;;; (true)
;;; where node1 represents expr and
;;; node2 represents (if expr (false) x2)

(defun log-justify-forbid-from-deny-if-test-aux (node1 node2 index)
  (let* ((expr (e-node-attribute node1))
         (equality-expr
          `(= (if ,expr (false) (true))
              (if (true) (if ,expr (false) (true)) (true)))))
    (push-proof-log 'if-test index t)
    ;; (log-convert-test-from-equal-true expr *false* *true* index)
    ;; (if expr (false) (true))
    (push-proof-log 'if-equal index equality-expr t)
    (push-proof-log 'look-up (if-left-index) (=-right equality-expr))
    ;; (if (= (if expr (false) (true))
    ;;        (if (true) (if expr (false) (true)) (true)))
    ;;     (if (true) (if expr (false) (true)) (true))
    ;;     (if expr (false) (true)))
    (push-proof-log 'if-true (cons 2 (if-test-index)))
    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)
    ;; (if (true) (if expr (false) (true)) (true))
    (log-node-equality *true-node* node2 (if-test-index))
    ;;(if (if expr (false) x2) (if expr (false) (true)) (true))
    (push-proof-log 'case-analysis index 1)
    ;; (if expr
    ;;     (if (false) (if expr (false) (true)) (true))
    ;;     (if x2 (if expr (false) (true)) (true)))
    (push-proof-log 'if-false (if-left-index))
    (push-proof-log 'look-up (cons 2 (if-right-index)) *true*)
    (push-proof-log 'if-equal (if-right-index))
    ;; (if x1 (true) (true))
    (push-proof-log 'if-equal index)))
