
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


;;; ============  Proof Obligation Generation functions ============



;;; Proof obligations generated for (potentially recursive) functions
;;; are simplified without losing its basic logical structure.

(defvar *simplify-tag* 'simplify)

;;; A subexpression to be simplified is tagged as follows:
;;;  (*simplify-tag* <expression>)

(defun simplifiable-p (form)
  (and (consp form)
       (eq (car form) *simplify-tag*)))

(defun remove-tags-from-expression (form)
  (cond ((not (consp form)) form)
	((eq (car form) *simplify-tag*)
	 (remove-tags-from-expression (second form)))
	(t (cons (car form)
		 (mapcar #'remove-tags-from-expression (cdr form))))))

(defsubst make-simplifiable-and (x y)
  (list *simplify-tag* (make-and x y)))

(defsubst make-simplifiable-if (x y z)
  (list *simplify-tag* (make-if x y z)))

(defsubst make-simplifiable-all (var term)
  (list *simplify-tag* (list 'all (list var) term)))

(defsubst add-simplifiable-conjuncts (juncts term)
  (list *simplify-tag* (cons 'and (append juncts (list term)))))



(defun gen-var (variable)
  (let ((newname (gensym)))
    (setf (get newname 'original) variable)
    newname))

(defun original-var-name (var)
  (or (get var 'original) var))

;;; Substitutions

(defun apply-subst (subst var)
  (let ((x (assoc-eq var subst)))
    (if x
	(cdr x)
        var)))

(defun free-vars (term)
  (unique-symbol (free-vars-aux term nil)))

(defun free-vars-aux (term bound)
  (cond ((symbolp term)
	 (if (member-eq term bound)
	     nil
	   (list term)))
	((atom term) nil)
	((simplifiable-p term) (free-vars-aux (second term) bound))
	((quantification-p term)
	 (free-vars-aux (quantification-expr term)
			(cons (quantification-var term) bound)))
	(t (loop for x in (cdr term)
		 nconcing (free-vars-aux x bound)))))

;;; po-sublis renames quantified variables using gen-var. The original
;;; names are saved (by gen-var) so that nice unrenaming can be performed.

(defun po-sublis (term alist)
  (cond ((symbolp term) (apply-subst alist term))
	((atom term) term)
	((simplifiable-p term)
	 (list (car term) (po-sublis (second term) alist)))
	((quantification-p term)
	 (let ((q (quantification-kind term))
	       (bv (quantification-var term))
	       (subterm (quantification-expr term)))
	   (let ((newvar (gen-var bv)))
	     (make-quantification
	      q newvar (po-sublis subterm (cons (cons bv newvar) alist))))))
	(t (cons (first term)
		 (mapcar #'(lambda (u) (po-sublis u alist)) (rest term))))))

;;; The choice of variable name in unrenaming is made as close as
;;; possible to the original name, without any variable capture problem.

(defun unrename-bound-names (e)
  (unrename-bound-names-aux e nil (free-vars e)))

(defun unrename-bound-names-aux (e subst-alist names-to-avoid)
  (cond ((symbolp e) (apply-subst subst-alist e))
	((atom e) e)
	((simplifiable-p e)
	 (list (car e)
	       (unrename-bound-names-aux
		(second e) subst-alist names-to-avoid)))
	((quantification-p e)
	 (let ((new-name (pretty-bound-name
			  (original-var-name (quantification-var e))
			  names-to-avoid)))
	   (make-quantification
	    (quantification-kind e)
	    new-name
	    (unrename-bound-names-aux
	     (quantification-expr e)
	     (cons (cons (quantification-var e) new-name) subst-alist)
	     (cons new-name names-to-avoid)))))
	(t (cons (first e)
		 (mapcar #'(lambda (x)
			     (unrename-bound-names-aux
			      x subst-alist names-to-avoid))
			 (rest e))))))

(defun pretty-bound-name (orig-name names-to-avoid)
  (if (member-eq orig-name names-to-avoid)
      (loop for number = 0 then (1+ number)
	    for newvar = (intern (format nil "~A-~A" orig-name number)
				 *zk-package*)
	    until (not (member-eq newvar names-to-avoid))
	    finally (return newvar))
      orig-name))


;;; Proof Obligation Generation
;;;
;;; The input to generate-proof-obligations is a declaration
;;; The output is a list of 4-tuples (name back-name raw log simple),
;;; where name	      is the name of the event having the PO
;;;       raw         is the original PO
;;;	  log	      is the proof log for the simplification
;;;	  simple      is the simplified PO
;;;

;;; Each PO generator gives a triple (name po simplifiable-p),
;;; where name	           is the name of the event having the PO
;;;       po               is the PO in raw form
;;;       simplifiable-p   indicates whether PO is to be simplified


(defun generate-proof-obligations (decl)
  (let ((triples (generate-po-triples decl)))
    (mapcar #'(lambda (x)
		(let* ((*proof-log* nil)
		       (simplifiable-p (third x))
		       (simple
			(if simplifiable-p
			    (simplify-and-log (second x))
			  (second x))))
		  (list (first x) ; name
			(if simplifiable-p
			    (remove-tags-from-expression (second x)) ; raw
			  (second x))
			*proof-log* ; log
			simple))) ; simple
	    triples)))

(defun generate-po-triples (decl)
  (let ((f (get (car decl) 'po-generator)))
    (if f
	(apply f (cdr decl))
        (error "Bad declaration ~A" decl))))

;;; load commands: no PO

(defpropfun (load po-generator) (unit-name)
  unit-name
  nil)

;;; axioms: PO is simply the body

(defpropfun (axiom po-generator) (name args formula)
  args
  (list (list name formula nil)))

(defpropfun (rule po-generator) (name args formula)
  args
  (list (list name formula nil)))

(defpropfun (frule po-generator) (name args formula)
  args
  (list (list name formula nil)))

(defpropfun (grule po-generator) (name args formula)
  args
  (list (list name formula nil)))

;;; functions

;;; function-stub: PO is (FALSE)
(defpropfun (function-stub po-generator) (name &rest args)
  args
  (list (list name *false* nil)))

;;; zf-function: PO is (TRUE) for MAP and SELECT
;;; PO for (THAT x P): (SOME (x') (ALL (x) (= P (= x x'))))
(defpropfun (zf-function po-generator) (name parameter-list zf-body)
  parameter-list
  (if (member-eq (car zf-body) '(map select))
      (list (list name *true* nil))
      (list (list name
		  (unrename-bound-names
		    (let ((new-name (gen-var (second zf-body))))
		      (make-quantification
			'some
			new-name
			(make-quantification
			 'all (second zf-body)
			 `(= ,(third zf-body)
			     (= ,(second zf-body) ,new-name))))))
		  nil))))

;;; Function is potentially recursive.
(defpropfun (function po-generator) (&rest args)
  (let ((mi (measure-info `(function . ,args))))
    (list (apply #'fn-po (cons mi args)))))

(defun get-annotation (indicator default annotation-alist)
  (let ((x (assoc-eq indicator annotation-alist)))
     (if x
	 (cadr x)
	 default)))

(defmacro get-measure (annotation-alist)
  `(get-annotation 'measure 0 ,annotation-alist))


(defun fn-po (mi name parameter-list annotations body)
  parameter-list annotations
  (list name (unrename-bound-names (measure-< body mi))	t))

;;; mi is the measure info.
;;; Initially, e is the body of the (potentially recursive) function,
;;; and is traversed to generate the PO.
(defun measure-< (e mi)
  (cond ((symbolp e) *true*) ; no recursion here
	((atom e) *true*) ; no recursion here
	((quantification-p e)
	 ;; must dive inside quantification
	 ;; note that SOME is turned into ALL
	 ;; however, the quantification can be simplified away
	 ;; if there are no recursions in it
	 (make-simplifiable-all
	  (quantification-var e) (measure-< (quantification-expr e) mi)))
	((eq (car e) 'if)
	 ;; must dive into the test, left and right
	 (make-simplifiable-and
	   (measure-< (second e) mi)
	   (make-simplifiable-if (second e)
				 (measure-< (third e) mi)
				 (measure-< (fourth e) mi))))
	(t
	 ;; function call
	 ;; recursive function call is treated specially
	 ;; (i.e., measure must go down according to m<)
	 ;; In any case, must dive into arguments as well.
	 (add-simplifiable-conjuncts
	  (mapcar #'(lambda (u) (measure-< u mi)) (cdr e))
	  (if (eq (car e) (car mi))
	      `(m< ,(po-sublis (third mi) (mapcar #'cons (second mi) (cdr e)))
		   ,(third mi))
	    *true*)))))

(defun measure-info (fn-decl)
  (list (second fn-decl)                    ; name
	(third fn-decl)                     ; formals
	(get-measure (fourth fn-decl))))    ; measure expression



;;; simplifier for proof obligations
;;;

(defun simplify-and-log (form)
  (sl-aux form
	  (mapcar #'(lambda (x) 2) (free-vars form)) ; dive past implicit quant
	  nil))

(defun sl-aux (form index bool-p)
  (cond ((not (consp form)) form)
	((eq (car form) *simplify-tag*)
	 (let ((op (car (second form)))
	       (expr (second form)))
	   ;; For "if", we defer simplifying the left and right parts until
	   ;; necessary. Also "all" is treated specially.
	   (cond ((member-eq op '(if all))
		  (funcall (get op 'po-simplifier) expr index bool-p))
		 ;; Otherwise simplify the arguments first.
		 (t
		  (funcall (get op 'po-simplifier)
			   (cons op
				 (sl-list (cdr expr) 1 index
					  (make-context-for-bool-p expr index)))
			   index
			   bool-p)))))
	((eq (car form) 'if)
	 (list 'if
	       (sl-aux (second form) (cons 1 index)
		       (make-context-for-bool-p form index))
	       (sl-aux (third form) (cons 2 index) bool-p)
	       (sl-aux (fourth form) (cons 3 index) bool-p)))
	((or (eq (car form) 'all)
	     (eq (car form) 'some))
	 (list (car form)
	       (second form)
	       (sl-aux (third form) (cons 2 index)
		       (make-context-for-bool-p
			form index))))
        ((member-eq (car form) '(not and or implies))
         (cons (car form)
	       (sl-list (cdr form) 1 index
			(make-context-for-bool-p form index))))
	(t (cons (car form) (sl-list (cdr form) 1 index nil)))))

(defun sl-list (forms n index bool-p)
  (if (consp forms)
      (cons (sl-aux (car forms) (cons n index) bool-p)
	    (sl-list (cdr forms) (1+ n) index bool-p))
      nil))



;;; The simplifiers

(defpropfun (and po-simplifier) (form index bool-p)
  ;; form is (and ...), may have any number of arguments
  ;; all arguments have been simplified
  (if (some #'false-p (cdr form))
      ;; find the index
      (do ((xs (cdr form) (cdr xs))
	   (i 1 (1+ i)))
	  ((false-p (car xs))
	   (log-and-false i (length (cdr form)) index)
	   *false*))
    (let ((simplified (really-flatten-ands form index)))
      (cond ((and (if-p simplified)
		  (true-p (if-left simplified))
		  (false-p (if-right simplified))
		  (or (bool-p (if-test simplified)) bool-p))
	     (log-remove-coercion-for-boolean-or-bool-p
	      (if-test simplified) index bool-p)
	     (if-test simplified))
	    (t simplified)))))

(defpropfun (if po-simplifier) (form index bool-p)
    ;; form is (if x y z), x, y, and z are all unsimplified
  (let ((x (sl-aux (if-test form) (cons 1 index)
		   (make-context-for-bool-p form index)))
	(y (if-left form))
	(z (if-right form)))
    (cond ((true-p x) ;; (if (true) y z)
	   (push-proof-log 'if-true index)
	   (sl-aux y index bool-p))
	  ((false-p x) ;; (if (false) y z)
	   (push-proof-log 'if-false index)
	   (sl-aux z index bool-p))
	  (t (let ((simple-y (sl-aux y (cons 2 index) bool-p))
		   (simple-z (sl-aux z (cons 3 index) bool-p)))
	       (cond ((equal simple-y simple-z)
		      (push-proof-log 'if-equal index)
		      simple-y)
		     (t (make-if x simple-y simple-z))))))))

(defpropfun (all po-simplifier) (form index bool-p)
  ;; form is (all (var) body), body is unsimplified
  (let ((var (all-var form))
	(body (sl-aux (all-expr form) (all-expr-index)
		      (make-context-for-bool-p
		       (make-all (all-vars form) *true*) index))))
    (cond ((not (member-eq var (free-vars body)))
	   (push-proof-log 'remove-universal index)
	   (cond ((or bool-p (bool-p body))
		  (log-remove-coercion-for-boolean-or-bool-p body index bool-p)
		  body)
		 (t (make-if body *true* *false*))))
	  ((and (consp body)
		(eq (car body) 'all)) ;; (all (var) (all (var2 ...) b2))
	   (push-proof-log 'syntax index t)
	   (make-all (cons var (all-vars body)) (all-expr body)))
	  (t (make-all (all-vars form) body)))))
