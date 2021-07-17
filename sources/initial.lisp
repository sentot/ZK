
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


(export '(lisp-mode))

;;;
;;; This is the initial state and initialization for the prover database.
;;;
;;; The initial state is described completely by the constant
;;; *initial-database.  It is simply the series of events needed to set
;;; up the basic theories in the system.  For the most part it just
;;; introduces the symbols to the parser since very few extensions to
;;; the logic have been added as of yet.
;;;
;;; At the very end of loading this file, the prover is initialized by
;;; resetting it.
;;; ____________________________________________________________________


;;; define the events which constitute the initial theory
;;; these are used to initialize the prover, and at each reset

(defparameter *initial-database*
	      (append '(

(tag 'map)
(tag 'that)
(tag 'select)
(tag 'make-set)
(tag 'all)
(tag 'some)

;;; simple types
(function-stub 'bool nil)
(function-stub 'int nil)

(function-stub '= '(|)X| |)Y|))
(setf (function-stub-type (get-event '=)) '(bool))
(setf (function-stub-computable (get-event '=)) t)
(function-stub 'if '(|)X| |)Y| |)Z|))
(setf (function-stub-computable (get-event 'if)) t)

;;; boolean functions
(function-stub 'true nil)
(setf (function-stub-type (get-event 'true)) '(bool))
(function-stub 'false nil)
(setf (function-stub-type (get-event 'false)) '(bool))
(function-stub 'not '(|)X|))
(setf (function-stub-type (get-event 'not)) '(bool))
(function-stub 'and '(|)X| |)Y|))
(setf (function-stub-type (get-event 'and)) '(bool))
(setf (function-stub-expand (get-event 'and)) t)
(function-stub 'or '(|)X| |)Y|))
(setf (function-stub-type (get-event 'or)) '(bool))
(setf (function-stub-expand (get-event 'or)) t)
(function-stub 'implies '(|)X| |)Y|))
(setf (function-stub-type (get-event 'implies)) '(bool))

(axiom 'not.definition '(|)X|) '(= (not |)X|) (if |)X| (false) (true))))
(axiom 'and.definition '(|)X| |)Y|)
       '(= (and |)X| |)Y|) (if |)X| (if |)Y| (true) (false)) (false))))
(axiom 'or.definition '(|)X| |)Y|)
       '(= (or |)X| |)Y|) (if |)X| (true) (if |)Y| (true) (false)))))
(axiom 'implies.definition '(|)X| |)Y|)
       '(= (implies |)X| |)Y|) (if |)X| (if |)Y| (true) (false)) (true))))


(axiom 'and.associative '(|)X| |)Y| |)Z|)
       '(= (and |)X| (and |)Y| |)Z|)) (and (and |)X| |)Y|) |)Z|)))
(axiom 'or.associative '(|)X| |)Y| |)Z|)
       '(= (or |)X| (or |)Y| |)Z|)) (or (or |)X| |)Y|) |)Z|)))
(axiom 'and.commutative '(|)X| |)Y|)
       '(= (and |)X| |)Y|) (and |)Y| |)X|)))
(axiom 'or.commutative '(|)X| |)Y|)
       '(= (or |)X| |)Y|) (or |)Y| |)X|)))

;;; arithmetic operators

(function-stub '+ '(|)X| |)Y|))
(setf (function-stub-type (get-event '+)) '(int))
(setf (function-stub-computable (get-event '+)) t)
(setf (function-stub-expand (get-event '+)) t)
(function-stub '- '(|)X| |)Y|))
(setf (function-stub-type (get-event '-)) '(int))
(setf (function-stub-computable (get-event '-)) t)
(function-stub '* '(|)X| |)Y|))
(setf (function-stub-type (get-event '*)) '(int))
(setf (function-stub-computable (get-event '*)) t)
(setf (function-stub-expand (get-event '*)) t)
(function-stub 'negate '(|)X|))
(setf (function-stub-type (get-event 'negate)) '(int))
(setf (function-stub-computable (get-event 'negate)) t)

;;; type functions/predicates
(function-stub 'type-of '(|)X|))

(function-stub 'in '(|)X| |)Y|))
(setf (function-stub-type (get-event 'in)) '(bool))

(function-stub 'ord '(|)X|))
(setf (function-stub-type (get-event 'ord)) '(int))


(function-stub 'succ '(|)X|))
(function-stub 'pred '(|)X|))



;;; arithmetic relations
(function-stub '< '(|)X| |)Y|))
(setf (function-stub-type (get-event '<)) '(bool))
(function-stub '> '(|)X| |)Y|))
(setf (function-stub-type (get-event '>)) '(bool))
(function-stub '<= '(|)X| |)Y|))
(setf (function-stub-type (get-event '<=)) '(bool))
(function-stub '>= '(|)X| |)Y|))
(setf (function-stub-type (get-event '>=)) '(bool))

(function-stub 'm< '(|)X| |)Y|))
(setf (function-stub-type (get-event 'm<)) '(bool))

(rule 'm<.nat '(|)X| |)Y|)
      '(implies (and (>= |)X| 0) (> |)Y| |)X|))
                (= (m< |)X| |)Y|) (true))))

(rule 'm<.in '(|)X| |)Y|)
      '(implies (in |)X| |)Y|)
                (= (m< |)X| |)Y|) (true))))

(axiom '<.definition '(|)X| |)Y|)
       '(= (< |)X| |)Y|) (>= |)Y| (succ |)X|))))

(axiom '>.definition '(|)X| |)Y|)
       '(= (> |)X| |)Y|) (>= |)X| (succ |)Y|))))

(axiom '<=.definition '(|)X| |)Y|)
       '(= (<= |)X| |)Y|) (>= |)Y| |)X|)))


(function-stub 'range '(|)L| |)H|))
(rule 'range.definition '(|)X| |)L| |)H|) '(= (in |)X| (range |)L| |)H|))
					   (and (>= |)X| |)L|) (>= |)H| |)X|))))



)



'(


(axiom 'boolean.coercion '(|)X|)
      '(= (if |)X| (true) (false))
          (if (= (type-of |)X|) (bool))
              |)X|
            (if |)X| (true) (false)))))

(axiom '=.commutes '(|)X| |)Y|)
      '(= (= |)X| |)Y|) (= |)Y| |)X|)))

(axiom '=.to.true '(|)X|)
      '(= (= |)X| |)X|) (true)))

;;; type axioms

(axiom 'true.type-of-axiom '() '(= (type-of (true)) (bool)))
(axiom 'false.type-of-axiom '() '(= (type-of (false)) (bool)))
(axiom '0.type-of-axiom '() '(= (type-of 0) (int)))
(axiom '1.type-of-axiom '() '(= (type-of 1) (int)))

(axiom 'not.type-of-axiom '(|)X|) '(= (type-of (not |)X|)) (bool)))
(axiom 'and.type-of-axiom '(|)X| |)Y|) '(= (type-of (and |)X| |)Y|)) (bool)))
(axiom 'or.type-of-axiom '(|)X| |)Y|) '(= (type-of (or |)X| |)Y|)) (bool)))
(axiom 'implies.type-of-axiom '(|)X| |)Y|)
      '(= (type-of (implies |)X| |)Y|)) (bool)))

(axiom '=.type-of-axiom '(|)X| |)Y|)
      '(= (type-of (= |)X| |)Y|)) (bool)))

(axiom '>=.type-of-axiom '(|)X| |)Y|)
      '(= (type-of (>= |)X| |)Y|)) (bool)))

(axiom 'in.type-of-axiom '(|)X| |)Y|)
      '(= (type-of (in |)X| |)Y|)) (bool)))

(axiom '+.type-of-axiom '(|)X| |)Y|)
      '(= (type-of (+ |)X| |)Y|)) (int)))

(axiom '-.type-of-axiom '(|)X| |)Y|)
       '(= (type-of (- |)X| |)Y|)) (int)))

(axiom '*.type-of-axiom '(|)X| |)Y|)
       '(= (type-of (* |)X| |)Y|)) (int)))

(axiom 'negate.type-of-axiom '(|)X|)
       '(= (type-of (negate |)X|)) (int)))

(axiom 'ord.type-of-axiom '(|)X|)
       '(= (type-of (ord |)X|)) (int)))

(axiom 'm<.type-of-axiom '(|)X| |)Y|)
      '(= (type-of (m< |)X| |)Y|)) (bool)))

(axiom '>.type-of-axiom '(|)X| |)Y|)
      '(= (type-of (> |)X| |)Y|)) (bool)))

(axiom '<.type-of-axiom '(|)X| |)Y|)
      '(= (type-of (< |)X| |)Y|)) (bool)))

(axiom '<=.type-of-axiom '(|)X| |)Y|)
      '(= (type-of (<= |)X| |)Y|)) (bool)))

)


;;; Continuation of the initial database.

'(


(disabled
  (ufunction 'div '(|)X| |)Y|)
	'(if (>= |)X| 0) |)X| (negate |)X|))
	'(if (and (= (type-of |)X|) (int))
		  (= (type-of |)Y|) (int))
		  (not (= |)Y| 0)))
	     (if (if (> |)Y| 0) (>= |)X| |)Y|) (<= |)X| |)Y|))
		 (+ (div (- |)X| |)Y|) |)Y|) 1)
	       (if (if (> |)Y| 0)
		       (>= (negate |)X|) |)Y|)
		     (>= |)X| (negate |)Y|)))
		     (- (div (+ |)X| |)Y|) |)Y|) 1)
		     0))
	     0)))
(put-event-property (get-event 'div) 'zk-modifiers
		    (cons (cons :disabled t) nil))
(disabled
  (ufunction 'mod '(|)X| |)Y|)
	'(if (> |)Y| 0)
	     (if (>= |)X| 0) |)X| (- |)Y| |)X|))
	     (if (<= |)X| 0) (negate |)X|) (- |)X| |)Y|)))
	'(if (and (= (type-of |)X|) (int))
		  (= (type-of |)Y|) (int))
		  (not (= |)Y| 0)))
	     (if (if (> |)Y| 0) (>= |)X| |)Y|) (<= |)X| |)Y|))
		 (mod (- |)X| |)Y|) |)Y|)
		 (if (if (> |)Y| 0) (< |)X| 0) (> |)X| 0))
		     (mod (+ |)X| |)Y|) |)Y|)
		     |)X|))
	     0)))
(put-event-property (get-event 'mod) 'zk-modifiers
		    (cons (cons :disabled t) nil))

(disabled
  (ufunction 'rem '(|)X| |)Y|)
	'(if (>= |)X| 0) |)X| (negate |)X|))
	'(if (and (= (type-of |)X|) (int))
		  (= (type-of |)Y|) (int))
		  (not (= |)Y| 0)))
	     (if (if (> |)Y| 0) (>= |)X| |)Y|) (<= |)X| |)Y|))
		 (rem (- |)X| |)Y|) |)Y|)
	       (if (if (> |)Y| 0)
		       (>= (negate |)X|) |)Y|)
		     (>= |)X| (negate |)Y|)))
		     (rem (+ |)X| |)Y|) |)Y|)
		     |)X|))
	     0)))
(put-event-property (get-event 'rem) 'zk-modifiers
		    (cons (cons :disabled t) nil))

(axiom 'div.type-of-axiom '(|)X| |)Y|) '(= (type-of (div |)X| |)Y|)) (int)))
(axiom 'mod.type-of-axiom '(|)X| |)Y|) '(= (type-of (mod |)X| |)Y|)) (int)))
(axiom 'rem.type-of-axiom '(|)X| |)Y|) '(= (type-of (rem |)X| |)Y|)) (int)))

(ufunction 'abs '(|)X|) '()
	     '(if (>= |)X| 0) |)X| (negate |)X|)))
)



'(


(grule 'succ.int '(|)X|)
       '(implies (= (type-of |)X|) (int)) (= (succ |)X|) (+ |)X| 1))))
(grule 'pred.int '(|)X|)
       '(implies (= (type-of |)X|) (int)) (= (pred |)X|) (- |)X| 1))))
(rule 'succ.int.rule '(|)X|)
      '(implies (= (type-of |)X|) (int)) (= (succ |)X|) (+ |)X| 1))))
(rule 'pred.int.rule '(|)X|)
      '(implies (= (type-of |)X|) (int)) (= (pred |)X|) (- |)X| 1))))


(rule 'ord.int '(|)X|) '(implies (= (type-of |)X|) (int))
				 (= (ord |)X|) |)X|)))	;a derived axiom

(ufunction 'min '(|)X| |)Y|) nil '(if (<= |)X| |)Y|) |)X| |)Y|))
(ufunction 'max '(|)X| |)Y|) nil '(if (<= |)X| |)Y|) |)Y| |)X|))

(disabled
  (rule '>=.definition '(|)X| |)Y|)
    '(= (>= |)Y| |)X|)
	(all (|)Z|) (implies (and (in |)X| |)Z|)
				(all (|)A|) (implies (in |)A| |)Z|)
                                                   (in (succ |)A|) |)Z|))))
			   (in |)Y| |)Z|))))))
(put-event-property (get-event '>=.definition) 'zk-modifiers
		    (cons (cons :disabled t) nil))

(frule '>=.same.type '(|)X| |)Y|)
  '(implies (>= |)X| |)Y|)
	    (= (type-of |)X|) (type-of |)Y|))))

)



;;; Arithmetic axioms

'(

(axiom '>=.zero.definition '(|)X|)
      '(= (>= |)X| 0) (if (= |)X| 0) (true) (>= |)X| 1))))

(axiom '>=.to.>=.zero '(|)X| |)Y|)
      '(= (>= |)X| |)Y|)
          (if (= (type-of |)X|) (int))
              (if (= (type-of |)Y|) (int))
                  (>= (- |)X| |)Y|) 0)
                (>= |)X| |)Y|))
            (>= |)X| |)Y|))))

(axiom '=.to.=.zero '(|)X| |)Y|)
      '(= (= |)X| |)Y|)
          (if (= (type-of |)X|) (int))
              (if (= (type-of |)Y|) (int))
                  (= (- |)X| |)Y|) 0)
                (= |)X| |)Y|))
            (= |)X| |)Y|))))

(axiom '+.zero.left '(|)X|)
      '(= (+ 0 |)X|) (if (= (type-of |)X|) (int)) |)X| (+ 0 |)X|))))

(axiom '+.zero.right '(|)X|)
      '(= (+ |)X| 0) (if (= (type-of |)X|) (int)) |)X| (+ |)X| 0))))

(axiom '*.zero.left '(|)X|)
      '(= (* 0 |)X|) 0))

(axiom '*.zero.right '(|)X|)
      '(= (* |)X| 0) 0))

(axiom '*.one.left '(|)X|)
      '(= (* 1 |)X|) (if (= (type-of |)X|) (int)) |)X| (* 1 |)X|))))

(axiom '*.one.right '(|)X|)
      '(= (* |)X| 1) (if (= (type-of |)X|) (int)) |)X| (* |)X| 1))))

(axiom '-.+.left.to.+.-.left '(|)X| |)Y| |)Z|)
      '(= (- (+ |)X| |)Y|) |)Z|) (+ (- |)X| |)Z|) |)Y|)))

(axiom '-.+.right.to.-.-.left '(|)X| |)Y| |)Z|)
      '(= (- |)X| (+ |)Y| |)Z|)) (- (- |)X| |)Y|) |)Z|)))

(axiom '+.times.1.left '(|)X| |)Y|)
      '(= (+ |)X| |)Y|) (+ (* 1 |)X|) |)Y|)))

(axiom '+.times.1.right '(|)X| |)Y|)
      '(= (+ |)X| |)Y|) (+ |)X| (* 1 |)Y|))))

(axiom 'from.+.times.1.left '(|)X| |)Y|)
      '(= (+ (* 1 |)X|) |)Y|) (+ |)X| |)Y|)))

(axiom 'from.+.times.1.right '(|)X| |)Y|)
      '(= (+ |)X| (* 1 |)Y|)) (+ |)X| |)Y|)))

(axiom '-.times.minus.1.right '(|)X| |)Y|)
      '(= (- |)X| |)Y|) (+ |)X| (* -1 |)Y|))))

(axiom '+.left.permute '(|)X| |)Y| |)Z|)
      '(= (+ (+ |)X| |)Y|) |)Z|) (+ (+ |)X| |)Z|) |)Y|)))

(axiom '+.right.permute '(|)X| |)Y| |)Z|)
      '(= (+ |)X| (+ |)Y| |)Z|)) (+ |)Y| (+ |)X| |)Z|))))

(axiom '*.left.permute '(|)X| |)Y| |)Z|)
      '(= (* (* |)X| |)Y|) |)Z|) (* (* |)X| |)Z|) |)Y|)))

(axiom '*.right.permute '(|)X| |)Y| |)Z|)
      '(= (* |)X| (* |)Y| |)Z|)) (* |)Y| (* |)X| |)Z|))))

(axiom '-.+.to.left '(|)X| |)Y| |)Z|)
      '(= (- |)X| (+ |)Y| |)Z|)) (- (- |)X| |)Y|) |)Z|)))

(axiom '+.-.to.left '(|)X| |)Y| |)Z|)
      '(= (+ |)X| (- |)Y| |)Z|)) (- (+ |)X| |)Y|) |)Z|)))

(axiom '-.-.to.left '(|)X| |)Y| |)Z|)
      '(= (- |)X| (- |)Y| |)Z|)) (+ (- |)X| |)Y|) |)Z|)))

(axiom '+.negate '(|)X| |)Y|)
      '(= (+ |)X| (negate |)Y|)) (- |)X| |)Y|)))

(axiom '-.negate '(|)X| |)Y|)
      '(= (- |)X| (negate |)Y|)) (+ |)X| |)Y|)))

(axiom '+.commutes '(|)X| |)Y|)
      '(= (+ |)X| |)Y|) (+ |)Y| |)X|)))

(axiom '*.commutes '(|)X| |)Y|)
      '(= (* |)X| |)Y|) (* |)Y| |)X|)))

)



'(

(axiom '+.ord '(|)X| |)Y|)
      '(= (+ (ord |)X|) (ord |)Y|)) (+ |)X| |)Y|)))

(axiom '+.ord.left '(|)X| |)Y|)
      '(= (+ (ord |)X|) |)Y|) (+ |)X| |)Y|)))

(axiom '+.ord.right '(|)X| |)Y|)
      '(= (+ |)X| (ord |)Y|)) (+ |)X| |)Y|)))

(axiom '-.ord '(|)X| |)Y|)
      '(= (- (ord |)X|) (ord |)Y|)) (- |)X| |)Y|)))

(axiom '-.ord.left '(|)X| |)Y|)
      '(= (- (ord |)X|) |)Y|) (- |)X| |)Y|)))

(axiom '-.ord.right '(|)X| |)Y|)
      '(= (- |)X| (ord |)Y|)) (- |)X| |)Y|)))

(axiom '*.ord '(|)X| |)Y|)
      '(= (* (ord |)X|) (ord |)Y|)) (* |)X| |)Y|)))

(axiom '*.ord.left '(|)X| |)Y|)
      '(= (* (ord |)X|) |)Y|) (* |)X| |)Y|)))

(axiom '*.ord.right '(|)X| |)Y|)
      '(= (* |)X| (ord |)Y|)) (* |)X| |)Y|)))

(axiom 'negate.ord '(|)X|)
      '(= (negate (ord |)X|)) (negate |)X|)))

(axiom 'ord.ord '(|)X|)
      '(= (ord (ord |)X|)) (ord |)X|)))

(axiom 'ord.+ '(|)X| |)Y|)
      '(= (ord (+ |)X| |)Y|)) (+ |)X| |)Y|)))

(axiom 'ord.- '(|)X| |)Y|)
      '(= (ord (- |)X| |)Y|)) (- |)X| |)Y|)))

(axiom 'ord.* '(|)X| |)Y|)
      '(= (ord (* |)X| |)Y|)) (* |)X| |)Y|)))

(axiom 'ord.negate '(|)X|)
      '(= (ord (negate |)X|)) (negate |)X|)))

(axiom '*.distribute.+.left '(|)X| |)Y| |)Z|)
      '(= (* (+ |)X| |)Y|) |)Z|) (+ (* |)X| |)Z|) (* |)Y| |)Z|))))

(axiom '*.collect.+.left '(|)X| |)Y| |)Z|)
      '(= (+ (* |)X| |)Y|) (* |)Z| |)Y|)) (* (+ |)X| |)Z|) |)Y|)))

(axiom '*.distribute.+.right '(|)X| |)Y| |)Z|)
      '(= (* |)X| (+ |)Y| |)Z|)) (+ (* |)X| |)Y|) (* |)X| |)Z|))))

(axiom '*.collect.+.right '(|)X| |)Y| |)Z|)
      '(= (+ (* |)X| |)Y|) (* |)X| |)Z|)) (* |)X| (+ |)Y| |)Z|))))

(axiom '*.distribute.+ '(|)A| |)B| |)X| |)Y|)
      '(= (* (+ |)A| |)B|) (+ |)X| |)Y|))
          (+ (* |)A| |)X|)
             (+ (* |)A| |)Y|)
                (+ (* |)B| |)X|)
                   (* |)B| |)Y|))))))

(axiom 'negate.distribute.+ '(|)X| |)Y|)
      '(= (negate (+ |)X| |)Y|)) (+ (negate |)X|) (negate |)Y|))))

(axiom 'negate.*.left '(|)X| |)Y|)
      '(= (negate (* |)X| |)Y|)) (* (negate |)X|) |)Y|)))

(axiom 'minimized.col.lemma '(|)X| |)Y|)
      '(= (= |)X| 0)
          (if (>= |)X| 0)
              (if (>= |)Y| 0)
                  (if (= (+ |)X| |)Y|) 0) (true) (= |)X| 0))
                (= |)X| 0))
            (= |)X| 0))))

(axiom '+.>=.zero.>=.left.right '(|)X| |)Y|)
      '(= (>= (+ |)X| |)Y|) 0)
          (if (>= |)X| 0)
              (if (>= |)Y| 0) (true) (>= (+ |)X| |)Y|) 0))
            (>= (+ |)X| |)Y|) 0))))

(axiom '*.>=.zero.>=.one.left '(|)X| |)Y|)
      '(= (>= (* |)X| |)Y|) 0)
          (if (>= |)X| 1)
              (if (= (type-of |)Y|) (int))
                  (>= |)Y| 0)
                (>= (* |)X| |)Y|) 0))
            (>= (* |)X| |)Y|) 0))))

)



'(

(axiom '+.associate.left '(|)X| |)Y| |)Z|)
      '(= (+ |)X| (+ |)Y| |)Z|)) (+ (+ |)X| |)Y|) |)Z|)))

(axiom '+.associate.right '(|)X| |)Y| |)Z|)
      '(= (+ (+ |)X| |)Y|) |)Z|) (+ |)X| (+ |)Y| |)Z|))))

(axiom '*.associate.left '(|)X| |)Y| |)Z|)
      '(= (* |)X| (* |)Y| |)Z|)) (* (* |)X| |)Y|) |)Z|)))

(axiom '*.associate.right '(|)X| |)Y| |)Z|)
      '(= (* (* |)X| |)Y|) |)Z|) (* |)X| (* |)Y| |)Z|))))

(axiom '>=.and.>=.negate.zero '(|)X|)
      '(= (= |)X| 0)
          (if (>= |)X| 0)
              (if (>= (negate |)X|) 0)
                  (true)
                (= |)X| 0))
            (= |)X| 0))))

(axiom 'square.non.negative '(|)X|)
      '(= (>= (* |)X| |)X|) 0) (true)))

(axiom 'integer.is.nat.or.negative '(|)X|)
      '(if (= (type-of |)X|) (int))
           (if (>= |)X| 0)
               (true)
             (>= (+ -1 (negate |)X|)) 0))
         (true)))

(axiom '>=.zero.and.not.=.zero '(|)X|)
      '(if (= |)X| 0)
           (true)
         (if (= (type-of |)X|) (int))
             (= (>= |)X| 0) (>= (+ -1 |)X|) 0))
           (true))))

(axiom 'negate.=.zero '(|)X|)
      '(= (= |)X| 0)
          (if (= (type-of |)X|) (int)) (= (negate |)X|) 0) (= |)X| 0))))

(axiom 'remove.common.multiplier '(|)X| |)Y| |)Z|)
      '(= (= (* |)X| |)Y|) (* |)X| |)Z|))
          (if (= (type-of |)X|) (int))
              (if (= |)X| 0)
                  (= (* |)X| |)Y|) (* |)X| |)Z|))
                (if (= (type-of |)Y|) (int))
                    (if (= (type-of |)Z|) (int))
                        (= |)Y| |)Z|)
                      (= (* |)X| |)Y|) (* |)X| |)Z|)))
                  (= (* |)X| |)Y|) (* |)X| |)Z|))))
            (= (* |)X| |)Y|) (* |)X| |)Z|)))))

(axiom 'normalize.>= '(|)X| |)Y| |)Z|)
      '(= (>= (+ |)X| (* |)Y| |)Z|)) 0)
          (if (>= |)X| 0)
              (if (>= |)Y| (+ |)X| 1))
                  (if (= (type-of |)Z|) (int))
                      (>= |)Z| 0)
                    (>= (+ |)X| (* |)Y| |)Z|)) 0))
                (>= (+ |)X| (* |)Y| |)Z|)) 0))
            (>= (+ |)X| (* |)Y| |)Z|)) 0))))

(axiom 'normalize.= '(|)X| |)Y|)
      '(= (= (* |)X| |)Y|) 0)
          (if (>= |)X| 1)
              (if (= (type-of |)Y|) (int))
                  (= |)Y| 0)
                (= (* |)X| |)Y|) 0))
            (= (* |)X| |)Y|) 0))))

(axiom '+.-.lemma '(|)X| |)Y|)
      '(= (+ |)X| (- |)Y| |)X|))
          (ord |)Y|)))

)



'(

(axiom 'inconsistent.restrictions '(|)X|)
      '(= (>= (negate |)X|) 1)
          (if (>= |)X| 0) (false) (>= (negate |)X|) 1))))

(axiom 'inequality.lemma '(|)X| |)Y|)
      '(= (>= |)X| 0)
          (if (= (type-of |)X|) (int))
              (if (>= |)Y| 0)
                  (if (>= (- |)X| |)Y|) 0)
                      (true)
                    (>= |)X| 0))
                (>= |)X| 0))
            (>= |)X| 0))))

(axiom 'square.zero '(|)X|)
      '(= (= (* |)X| |)X|) 0)
          (if (= (type-of |)X|) (int)) (= |)X| 0) (= (* |)X| |)X|) 0))))

(axiom 'product.zero.left '(|)X| |)Y|)
      '(= (= (* |)X| |)Y|) 0)
          (if (= (type-of |)X|) (int))
              (if (= (type-of |)Y|) (int))
                  (if (if (= |)Y| 0) (false) (true))
                      (= |)X| 0)
                    (= (* |)X| |)Y|) 0))
                (= (* |)X| |)Y|) 0))
            (= (* |)X| |)Y|) 0))))

(axiom 'product.zero.right '(|)X| |)Y|)
      '(= (= (* |)X| |)Y|) 0)
          (if (= (type-of |)X|) (int))
              (if (= (type-of |)Y|) (int))
                  (if (if (= |)X| 0) (false) (true))
                      (= |)Y| 0)
                    (= (* |)X| |)Y|) 0))
                (= (* |)X| |)Y|) 0))
            (= (* |)X| |)Y|) 0))))

(axiom '>=.reflexive '(|)X|)
      '(= (>= |)X| |)X|) (true)))

(axiom '=.to.>=.and.>=.negate '(|)X|)
      '(= (= |)X| 0)
          (if (>= |)X| 0)
              (if (>= (negate |)X|) 0) (true) (false))
            (false))))

)



;;; Non-linear arithmetic

'(

(axiom '*.up.1 '(|)X| |)Y|)
      '(= (>= (* |)X| |)Y|) 0)
	  (if (>= |)X| 0)
	      (if (>= |)Y| 0)
		  (true)
		(>= (* |)X| |)Y|) 0))
	    (>= (* |)X| |)Y|) 0))))

(axiom '*.up.2 '(|)X| |)Y|)
      '(= (>= (negate (* |)X| |)Y|)) 0)
	  (if (>= |)X| 0)
	      (if (>= (negate |)Y|) 0)
		  (true)
		(>= (negate (* |)X| |)Y|)) 0))
	    (>= (negate (* |)X| |)Y|)) 0))))

(axiom '*.up.3 '(|)X| |)Y|)
      '(= (>= (* |)X| |)Y|) 0)
	  (if (>= |)X| 0)
	      (if (>= (- |)Y| 1) 0)
		  (true)
		(>= (* |)X| |)Y|) 0))
	    (>= (* |)X| |)Y|) 0))))

(axiom '*.up.4 '(|)X| |)Y|)
      '(= (>= (negate (* |)X| |)Y|)) 0)
	  (if (>= |)X| 0)
	      (if (>= (- (negate |)Y|) 1) 0)
		  (true)
		(>= (negate (* |)X| |)Y|)) 0))
	    (>= (negate (* |)X| |)Y|)) 0))))

(axiom '*.up.5 '(|)X| |)Y|)
      '(= (>= (negate (* |)X| |)Y|)) 0)
	  (if (>= (negate |)X|) 0)
	      (if (>= |)Y| 0)
		  (true)
		(>= (negate (* |)X| |)Y|)) 0))
	    (>= (negate (* |)X| |)Y|)) 0))))

(axiom '*.up.6 '(|)X| |)Y|)
      '(= (>= (* |)X| |)Y|) 0)
	  (if (>= (negate |)X|) 0)
	      (if (>= (negate |)Y|) 0)
		  (true)
		(>= (* |)X| |)Y|) 0))
	    (>= (* |)X| |)Y|) 0))))

(axiom '*.up.7 '(|)X| |)Y|)
      '(= (>= (negate (* |)X| |)Y|)) 0)
	  (if (>= (negate |)X|) 0)
	      (if (>= (- |)Y| 1) 0)
		  (true)
		(>= (negate (* |)X| |)Y|)) 0))
	    (>= (negate (* |)X| |)Y|)) 0))))

(axiom '*.up.8 '(|)X| |)Y|)
      '(= (>= (* |)X| |)Y|) 0)
	  (if (>= (negate |)X|) 0)
	      (if (>= (- (negate |)Y|) 1) 0)
		  (true)
		(>= (* |)X| |)Y|) 0))
	    (>= (* |)X| |)Y|) 0))))
)



'(

(axiom '*.up.9 '(|)X| |)Y|)
      '(= (>= (* |)X| |)Y|) 0)
	  (if (>= (- |)X| 1) 0)
	      (if (>= |)Y| 0)
		  (true)
		(>= (* |)X| |)Y|) 0))
	    (>= (* |)X| |)Y|) 0))))

(axiom '*.up.10 '(|)X| |)Y|)
      '(= (>= (negate (* |)X| |)Y|)) 0)
	  (if (>= (- |)X| 1) 0)
	      (if (>= (negate |)Y|) 0)
		  (true)
		(>= (negate (* |)X| |)Y|)) 0))
	    (>= (negate (* |)X| |)Y|)) 0))))

(axiom '*.up.11 '(|)X| |)Y|)
      '(= (>= (- (* |)X| |)Y|) 1) 0)
	  (if (>= (- |)X| 1) 0)
	      (if (>= (- |)Y| 1) 0)
		  (true)
		(>= (- (* |)X| |)Y|) 1) 0))
	    (>= (- (* |)X| |)Y|) 1) 0))))

(axiom '*.up.12 '(|)X| |)Y|)
      '(= (>= (- (negate (* |)X| |)Y|)) 1) 0)
	  (if (>= (- |)X| 1) 0)
	      (if (>= (- (negate |)Y|) 1) 0)
		  (true)
		(>= (- (negate (* |)X| |)Y|)) 1) 0))
	    (>= (- (negate (* |)X| |)Y|)) 1) 0))))

(axiom '*.up.13 '(|)X| |)Y|)
      '(= (>= (negate (* |)X| |)Y|)) 0)
	  (if (>= (- (negate |)X|) 1) 0)
	      (if (>= |)Y| 0)
		  (true)
		(>= (negate (* |)X| |)Y|)) 0))
	    (>= (negate (* |)X| |)Y|)) 0))))

(axiom '*.up.14 '(|)X| |)Y|)
      '(= (>= (* |)X| |)Y|) 0)
	  (if (>= (- (negate |)X|) 1) 0)
	      (if (>= (negate |)Y|) 0)
		  (true)
		(>= (* |)X| |)Y|) 0))
	    (>= (* |)X| |)Y|) 0))))

(axiom '*.up.15 '(|)X| |)Y|)
      '(= (>= (- (negate (* |)X| |)Y|)) 1) 0)
	  (if (>= (- (negate |)X|) 1) 0)
	      (if (>= (- |)Y| 1) 0)
		  (true)
		(>= (- (negate (* |)X| |)Y|)) 1) 0))
	    (>= (- (negate (* |)X| |)Y|)) 1) 0))))

(axiom '*.up.16 '(|)X| |)Y|)
      '(= (>= (- (* |)X| |)Y|) 1) 0)
	  (if (>= (- (negate |)X|) 1) 0)
	      (if (>= (- (negate |)Y|) 1) 0)
		  (true)
		(>= (- (* |)X| |)Y|) 1) 0))
	    (>= (- (* |)X| |)Y|) 1) 0))))

)



'(

(axiom '*.l.1 '(|)X| |)Y|)
      '(= (>= (ord |)X|) 0)
          (if (>= (* |)X| |)Y|) 0)
              (if (>= (- |)Y| 1) 0) (true) (>= (ord |)X|) 0))
            (>= (ord |)X|) 0))))

(axiom '*.l.2 '(|)X| |)Y|)
      '(= (>= (negate |)X|) 0)
          (if (>= (* |)X| |)Y|) 0)
              (if (>= (- (negate |)Y|) 1) 0) (true) (>= (negate |)X|) 0))
            (>= (negate |)X|) 0))))

(axiom '*.l.3 '(|)X| |)Y|)
      '(= (>= (negate |)X|) 0)
          (if (>= (negate (* |)X| |)Y|)) 0)
              (if (>= (- |)Y| 1) 0) (true) (>= (negate |)X|) 0))
            (>= (negate |)X|) 0))))

(axiom '*.l.4 '(|)X| |)Y|)
      '(= (>= (ord |)X|) 0)
          (if (>= (negate (* |)X| |)Y|)) 0)
              (if (>= (- (negate |)Y|) 1) 0) (true) (>= (ord |)X|) 0))
            (>= (ord |)X|) 0))))

(axiom '*.l.5 '(|)X| |)Y|)
      '(= (>= (- |)X| 1) 0)
          (if (>= (- (* |)X| |)Y|) 1) 0)
              (if (>= |)Y| 0) (true) (>= (- |)X| 1) 0))
            (>= (- |)X| 1) 0))))

(axiom '*.l.6 '(|)X| |)Y|)
      '(= (>= (- (negate |)X|) 1) 0)
          (if (>= (- (* |)X| |)Y|) 1) 0)
              (if (>= (negate |)Y|) 0) (true) (>= (- (negate |)X|) 1) 0))
            (>= (- (negate |)X|) 1) 0))))

(axiom '*.l.7 '(|)X| |)Y|)
      '(= (>= (- |)X| 1) 0)
          (if (>= (- (* |)X| |)Y|) 1) 0)
              (if (>= (- |)Y| 1) 0) (true) (>= (- |)X| 1) 0))
            (>= (- |)X| 1) 0))))

(axiom '*.l.8 '(|)X| |)Y|)
      '(= (>= (- (negate |)X|) 1) 0)
          (if (>= (- (* |)X| |)Y|) 1) 0)
              (if (>= (- (negate |)Y|) 1) 0) (true) (>= (- (negate |)X|) 1) 0))
            (>= (- (negate |)X|) 1) 0))))

)



'(

(axiom '*.l.9 '(|)X| |)Y|)
      '(= (>= (- (negate |)X|) 1) 0)
          (if (>= (- (negate (* |)X| |)Y|)) 1) 0)
              (if (>= |)Y| 0) (true) (>= (- (negate |)X|) 1) 0))
            (>= (- (negate |)X|) 1) 0))))

(axiom '*.l.10 '(|)X| |)Y|)
      '(= (>= (- |)X| 1) 0)
          (if (>= (- (negate (* |)X| |)Y|)) 1) 0)
              (if (>= (negate |)Y|) 0) (true) (>= (- |)X| 1) 0))
            (>= (- |)X| 1) 0))))

(axiom '*.l.11 '(|)X| |)Y|)
      '(= (>= (- (negate |)X|) 1) 0)
          (if (>= (- (negate (* |)X| |)Y|)) 1) 0)
              (if (>= (- |)Y| 1) 0) (true) (>= (- (negate |)X|) 1) 0))
            (>= (- (negate |)X|) 1) 0))))

(axiom '*.l.12 '(|)X| |)Y|)
      '(= (>= (- |)X| 1) 0)
          (if (>= (- (negate (* |)X| |)Y|)) 1) 0)
              (if (>= (- (negate |)Y|) 1) 0) (true) (>= (- |)X| 1) 0))
            (>= (- |)X| 1) 0))))

(axiom '*.ll.1 '(|)X| |)Y|)
      '(= (>= (- |)X| 1) 0)
          (if (>= (- (* |)X| |)Y|) 1) 0)
              (>= (ord |)X|) 0)
            (>= (- |)X| 1) 0))))

(axiom '*.ll.2 '(|)X| |)Y|)
      '(= (>= (- (negate |)X|) 1) 0)
          (if (>= (- (* |)X| |)Y|) 1) 0)
              (>= (negate |)X|) 0)
            (>= (- (negate |)X|) 1) 0))))

(axiom '*.ll.3 '(|)X| |)Y|)
      '(= (>= (- |)X| 1) 0)
          (if (>= (- (negate (* |)X| |)Y|)) 1) 0)
              (>= (ord |)X|) 0)
            (>= (- |)X| 1) 0))))

(axiom '*.ll.4 '(|)X| |)Y|)
      '(= (>= (- (negate |)X|) 1) 0)
          (if (>= (- (negate (* |)X| |)Y|)) 1) 0)
              (>= (negate |)X|) 0)
            (>= (- (negate |)X|) 1) 0))))

)



'(

(axiom '*.r.1 '(|)X| |)Y|)
      '(= (>= (ord |)X|) 0)
          (if (>= (* |)Y| |)X|) 0)
              (if (>= (- |)Y| 1) 0) (true) (>= (ord |)X|) 0))
            (>= (ord |)X|) 0))))

(axiom '*.r.2 '(|)X| |)Y|)
      '(= (>= (negate |)X|) 0)
          (if (>= (* |)Y| |)X|) 0)
              (if (>= (- (negate |)Y|) 1) 0) (true) (>= (negate |)X|) 0))
            (>= (negate |)X|) 0))))

(axiom '*.r.3 '(|)X| |)Y|)
      '(= (>= (negate |)X|) 0)
          (if (>= (negate (* |)Y| |)X|)) 0)
              (if (>= (- |)Y| 1) 0) (true) (>= (negate |)X|) 0))
            (>= (negate |)X|) 0))))

(axiom '*.r.4 '(|)X| |)Y|)
      '(= (>= (ord |)X|) 0)
          (if (>= (negate (* |)Y| |)X|)) 0)
              (if (>= (- (negate |)Y|) 1) 0) (true) (>= (ord |)X|) 0))
            (>= (ord |)X|) 0))))

(axiom '*.r.5 '(|)X| |)Y|)
      '(= (>= (- |)X| 1) 0)
          (if (>= (- (* |)Y| |)X|) 1) 0)
              (if (>= |)Y| 0) (true) (>= (- |)X| 1) 0))
            (>= (- |)X| 1) 0))))

(axiom '*.r.6 '(|)X| |)Y|)
      '(= (>= (- (negate |)X|) 1) 0)
          (if (>= (- (* |)Y| |)X|) 1) 0)
              (if (>= (negate |)Y|) 0) (true) (>= (- (negate |)X|) 1) 0))
            (>= (- (negate |)X|) 1) 0))))

(axiom '*.r.7 '(|)X| |)Y|)
      '(= (>= (- |)X| 1) 0)
          (if (>= (- (* |)Y| |)X|) 1) 0)
              (if (>= (- |)Y| 1) 0) (true) (>= (- |)X| 1) 0))
            (>= (- |)X| 1) 0))))

(axiom '*.r.8 '(|)X| |)Y|)
      '(= (>= (- (negate |)X|) 1) 0)
          (if (>= (- (* |)Y| |)X|) 1) 0)
              (if (>= (- (negate |)Y|) 1) 0) (true) (>= (- (negate |)X|) 1) 0))
            (>= (- (negate |)X|) 1) 0))))

)



'(

(axiom '*.r.9 '(|)X| |)Y|)
      '(= (>= (- (negate |)X|) 1) 0)
          (if (>= (- (negate (* |)Y| |)X|)) 1) 0)
              (if (>= |)Y| 0) (true) (>= (- (negate |)X|) 1) 0))
            (>= (- (negate |)X|) 1) 0))))

(axiom '*.r.10 '(|)X| |)Y|)
      '(= (>= (- |)X| 1) 0)
          (if (>= (- (negate (* |)Y| |)X|)) 1) 0)
              (if (>= (negate |)Y|) 0) (true) (>= (- |)X| 1) 0))
            (>= (- |)X| 1) 0))))

(axiom '*.r.11 '(|)X| |)Y|)
      '(= (>= (- (negate |)X|) 1) 0)
          (if (>= (- (negate (* |)Y| |)X|)) 1) 0)
              (if (>= (- |)Y| 1) 0) (true) (>= (- (negate |)X|) 1) 0))
            (>= (- (negate |)X|) 1) 0))))

(axiom '*.r.12 '(|)X| |)Y|)
      '(= (>= (- |)X| 1) 0)
          (if (>= (- (negate (* |)Y| |)X|)) 1) 0)
              (if (>= (- (negate |)Y|) 1) 0) (true) (>= (- |)X| 1) 0))
            (>= (- |)X| 1) 0))))

(axiom '*.rr.1 '(|)X| |)Y|)
      '(= (>= (- |)X| 1) 0)
          (if (>= (- (* |)Y| |)X|) 1) 0)
              (>= (ord |)X|) 0)
            (>= (- |)X| 1) 0))))

(axiom '*.rr.2 '(|)X| |)Y|)
      '(= (>= (- (negate |)X|) 1) 0)
          (if (>= (- (* |)Y| |)X|) 1) 0)
              (>= (negate |)X|) 0)
            (>= (- (negate |)X|) 1) 0))))

(axiom '*.rr.3 '(|)X| |)Y|)
      '(= (>= (- |)X| 1) 0)
          (if (>= (- (negate (* |)Y| |)X|)) 1) 0)
              (>= (ord |)X|) 0)
            (>= (- |)X| 1) 0))))

(axiom '*.rr.4 '(|)X| |)Y|)
      '(= (>= (- (negate |)X|) 1) 0)
          (if (>= (- (negate (* |)Y| |)X|)) 1) 0)
              (>= (negate |)X|) 0)
            (>= (- (negate |)X|) 1) 0))))


)



'(


(function-stub 'nullset nil)
(rule 'nullset.definition '(|)X|) `(= (in |)X| (nullset)) ,*false*))
(axiom '=.extensional '(|)X| |)Y|)
  '(= (= |)X| |)Y|) (all (|)E|) (= (in |)E| |)X|) (in |)E| |)Y|)))))

(function-stub 'setadd '(|)X| |)Y|))
(rule 'setadd.definition '(|)E| |)X| |)Y|)
      '(= (in |)E| (setadd |)X| |)Y|)) (or (= |)E| |)X|) (in |)E| |)Y|))))

(function-stub 'unit '(|)X|))
(rule 'unit.definition '(|)E| |)X|) '(= (in |)E| (unit |)X|)) (= |)E| |)X|)))

(ufunction 'subset '(|)X| |)Y|) nil
      '(all (|)E|) (implies (in |)E| |)X|) (in |)E| |)Y|))))

(axiom 'subset.type-of-axiom '(|)X| |)Y|)
      '(= (type-of (subset |)X| |)Y|)) (bool)))

(disabled (rule '=.extensional.subset '(|)X| |)Y|)
	    '(= (= |)X| |)Y|) (and (subset |)X| |)Y|) (subset |)Y| |)X|)))))
(put-event-property (get-event '=.extensional.subset) 'zk-modifiers
		    (cons (cons :disabled t) nil))
(rule 'subset.transitive '(|)X| |)Y| |)Z|)
	     '(implies (and (subset |)X| |)Y|) (subset |)Y| |)Z|))
		       (= (subset |)X| |)Z|) (true))))
(rule 'subset.nullset.left '(|)S|) '(= (subset (nullset) |)S|) (true)))
(rule 'subset.nullset.right '(|)S|)
      '(= (subset |)S| (nullset)) (= |)S| (nullset))))
(rule 'subset.self '(|)S|) '(= (subset |)S| |)S|) (true)))

(function-stub 'union '(|)X| |)Y|))
(rule 'union.definition '(|)E| |)X| |)Y|)
      '(= (in |)E| (union |)X| |)Y|)) (or (in |)E| |)X|) (in |)E| |)Y|))))
(rule 'union.self '(|)X|) '(= (union |)X| |)X|) |)X|))
(rule 'union.nullset.left '(|)X|) '(= (union (nullset) |)X|) |)X|))
(rule 'union.nullset.right '(|)X|) '(= (union |)X| (nullset)) |)X|))
(rule '=.union.nullset '(|)X| |)Y|)
      '(= (= (union |)X| |)Y|) (nullset))
	  (and (= |)X| (nullset)) (= |)Y| (nullset)))))
(rule 'union.commutative '(|)X| |)Y|) '(= (union |)X| |)Y|) (union |)Y| |)X|)))
(rule 'union.associative '(|)X| |)Y| |)Z|)
      '(= (union (union |)X| |)Y|) |)Z|) (union |)X| (union |)Y| |)Z|))))
(rule 'union.permutative '(|)X| |)Y| |)Z|)
      '(= (union |)X| (union |)Y| |)Z|)) (union |)Y| (union |)X| |)Z|))))

(function-stub 'inter '(|)X| |)Y|))
(rule 'inter.definition '(|)E| |)X| |)Y|)
      '(= (in |)E| (inter |)X| |)Y|)) (and (in |)E| |)X|) (in |)E| |)Y|))))
(rule 'inter.self '(|)X|) '(= (inter |)X| |)X|) |)X|))
(rule 'inter.nullset.left '(|)X|) '(= (inter (nullset) |)X|) (nullset)))
(rule 'inter.nullset.right '(|)X|) '(= (inter |)X| (nullset)) (nullset)))
(rule 'inter.commutative '(|)X| |)Y|) '(= (inter |)X| |)Y|) (inter |)Y| |)X|)))
(rule 'inter.associative '(|)X| |)Y| |)Z|)
      '(= (inter (inter |)X| |)Y|) |)Z|) (inter |)X| (inter |)Y| |)Z|))))
(rule 'inter.permutative '(|)X| |)Y| |)Z|)
      '(= (inter |)X| (inter |)Y| |)Z|)) (inter |)Y| (inter |)X| |)Z|))))

(function-stub 'diff '(|)X| |)Y|))
(rule 'diff.definition '(|)E| |)X| |)Y|)
      '(= (in |)E| (diff |)X| |)Y|)) (and (in |)E| |)X|) (not (in |)E| |)Y|)))))

(function-stub 'delta '(|)X| |)Y|))
(rule 'delta.definition '(|)E| |)X| |)Y|)
      '(= (in |)E| (delta |)X| |)Y|)) (not (= (in |)E| |)X|) (in |)E| |)Y|)))))

(function-stub 'powerset '(|)X|))
(rule 'powerset.definition '(|)E| |)X|)
      '(= (in |)E| (powerset |)X|)) (subset |)E| |)X|)))

(function-stub 'cup '(|)X|))
(rule 'cup.definition '(|)E| |)X|)
      '(= (in |)E| (cup |)X|))
	  (some (|)Y|) (and (in |)E| |)Y|) (in |)Y| |)X|)))))

;;; we combine the axiom of (global) choice and the axiom of regularity
(function-stub 'choice '(|)X|))

(axiom 'axiom.of.regular.choice '(|)X|)
      '(implies (not (= |)X| (nullset)))
		(and (in (choice |)X|) |)X|)
		 (= (inter (choice |)X|) |)X|) (nullset)))))

;;; an instance of regularity that is worth noting, and keeps logs shorter
;;; (see onepoint.lisp)

(rule 'not.member.self '(|)X|)
 '(= (in |)X| |)X|)
     (false)))

;;; this recursive definition gives the "epsilon induction" scheme

(ufunction 'epsilon-induction '(|)X|) '|)X|
      '(all (|)Y|) (if (in |)Y| |)X|)
		     (epsilon-induction |)Y|)
                     |)X|)))

)



'(


(disabled
  (rule 'type-of.definition '(|)X| |)Y|)
    '(implies (or (= |)Y| (bool)) (= |)Y| (int)))
	      (= (in |)X| |)Y|) (= (type-of |)X|) |)Y|)))))
(put-event-property (get-event 'type-of.definition) 'zk-modifiers
		    (cons (cons :disabled t) nil))

(disabled
  (rule 'bool.definition '() '(= (bool) (union (unit (true)) (unit (false))))))
(put-event-property (get-event 'bool.definition) 'zk-modifiers
		    (cons (cons :disabled t) nil))
(axiom 'bool.definition.2 '(|)X|) '(= (= (type-of |)X|) (bool))
                                      (if (= |)X| (true)) (true)
                                        (= |)X| (false)))))

)



'(

(axiom 'true.not.false '() '(if (= (true) (false)) (false) (true)))
(axiom `bool.not.int '() '(if (= (bool) (int)) (false) (true)))

)



;;; The pre functions

'(

;;; type prescriptions

(grule 'abs.type-of '(|)X|)
       '(implies (= (type-of |)X|) (int))
		 (= (type-of (abs |)X|)) (int))))

)



'(
;;; a name for undoing
(tag nil)

)))						;end of initial database


;;; Things we want to do when the prover is initially loaded
;;; and a definition which servers as an upper bound for metering.

;;; reset the prover
(unless *compiling-zk*
  (reset t))

(defparameter *lisp-mode-help-string*
	      "
You are interacting with the ZK system in Lisp mode.
Type the command \"(help)\" for basic help.
Type \"(quit)\" to exit the ZK system Lisp mode.")

;;; top level for Lisp mode

(defvar *quit-lisp-mode* nil)

(defun quit ()
  (when (yes-or-no-p "Exit ZK Lisp mode? ")
    (setq *quit-lisp-mode* t)))

(defun lisp-mode ()
  (let ((*package* *zk-package*)
	(*quit-lisp-mode* nil))
    (format t "~%ZK version ~A Lisp Mode~%" *zk-version*)
    (format t *lisp-mode-help-string*)
    (with-lisp-mode-help
      (let ((input nil))
	(loop until *quit-lisp-mode*
	    do (read-and-evaluate
                *lisp-mode-help-string* "ZK>> "
		(setq input (read))
		(print (eval input))))))))
