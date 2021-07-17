
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
;;; Internal representation of formulas.
;;; Formulas are really expressions since ZK is untyped.
;;; =====================================================================

(in-package "ZK")

(defparameter *univ-type* t)
(defparameter *int-type* '(int))
(defparameter *bool-type* '(bool))

(defsubst univ-type-p (type) (eq type t))
(defsubst int-type-p (type) (equal type '(int)))
(defsubst bool-type-p (type) (equal type '(bool)))

;;; Return non nil if name is an expandable function.

(defsubst expand-p (name)
  (let ((event (get-event name)))
    (when (function-stub-p event) (function-stub-expand event))))

;;; Return the type associated with any formula.

(defun type-of-any (formula)
  (cond ((numberp formula) *int-type*)
	((atom formula) *univ-type*) ; really means unknown
	((if-p formula)	; if is handled as a special case
	 (let ((left-type (type-of-any (if-left formula)))
	       (right-type (type-of-any (if-right formula))))
	   (if (equal left-type right-type)
	       left-type
	       *univ-type*))) ; unknown
        ((member-eq (car formula)
                    '(true false and or implies not all some
                      = >= <= > < in m< subset))
         '(bool))
	((member-eq (car formula)
		    '(+ - * negate ord))
	 '(int))
	(t *univ-type*))) ; unknown

(defsubst int-p (formula) (equal (type-of-any formula) *int-type*))
(defsubst bool-p (formula) (equal (type-of-any formula) *bool-type*))


;;; Constructors, accessors and recognizers for expressions.

;;; Arithhmetic expressions.

;;; -----

;;; +

;;; Constructor constructs a binary operation.

(defun make-+ (left right)
  (list '+ left right))

;;; Left accessor assumes at least one argument.
;;; Otherwise produces nil.

(defun +-left (expr)
  (second expr))

;;; Right accessor assumes at least two arguments.
;;; Otherwise produces nil.

(defun +-right (expr)
  (third expr))

;;; Recognizer only checks the operator (+ expression can have any
;;; number of arguments including none).

(defun +-p (expr)
  (and (listp expr) (eq (car expr) '+)))


;;; -----

;;; -

(defun make-- (left right)
  (list '- left right))

(defun --left (expr)
  (second expr))

(defun --right (expr)
  (third expr))

(defun --p (expr)
  (and (listp expr) (eq (car expr) '-)))


;;; -----

;;; *

(defun make-* (left right)
  (list '* left right))

(defun *-left (expr)
  (second expr))

(defun *-right (expr)
  (third expr))

(defun *-p (expr)
  (and (listp expr) (eq (car expr) '*)))


;;; -----

;;; negate

(defun make-negate (expr)
  (list 'negate expr))

(defun negate-expr (expr)
  (second expr))

(defun negate-p (expr)
  (and (listp expr) (eq (car expr) 'negate)))


;;; Arithmetic comparisons.

;;; -----

;;; <

(defun make-< (left right)
  (list '< left right))

(defun <-left (expr)
  (second expr))

(defun <-right (expr)
  (third expr))

(defun <-p (expr)
  (and (listp expr) (eq (car expr) '<)))

;;; -----

;;; >

(defun make-> (left right)
  (list '> left right))

(defun >-left (expr)
  (second expr))

(defun >-right (expr)
  (third expr))

(defun >-p (expr)
  (and (listp expr) (eq (car expr) '>)))

;;; -----

;;; <=

(defun make-<= (left right)
  (list '<= left right))

(defun <=-left (expr)
  (second expr))

(defun <=-right (expr)
  (third expr))

(defun <=-p (expr)
  (and (listp expr) (eq (car expr) '<=)))

;;; -----

;;; >=

(defun make->= (left right)
  (list '>= left right))

(defun >=-left (expr)
  (second expr))

(defun >=-right (expr)
  (third expr))

(defun >=-p (expr)
  (and (listp expr) (eq (car expr) '>=)))


;;; Ordinal comparison

(defun make-m< (left right)
  (list 'm< left right))

(defun m<-left (expr)
  (second expr))

(defun m<-right (expr)
  (third expr))

(defun m<-p (expr)
  (and (listp expr) (eq (car expr) 'm<)))




;;; General comparisons.

;;; -----

;;; =

(defun make-= (left right)
  (list '= left right))

(defun =-left (expr)
  (second expr))

(defun =-right (expr)
  (third expr))

(defun =-p (expr)
  (and (listp expr) (eq (car expr) '=)))

;;; Logical connectives.

;;; -----

;;; or

(defun make-or (left right)
  (list 'or left right))

(defun or-left (expr)
  (second expr))

(defun or-right (expr)
  (third expr))

(defun or-p (expr)
  (and (listp expr) (eq (car expr) 'or)))

;;; -----

;;; and

(defun make-and (left right)
  (list 'and left right))

(defun and-left (expr)
  (second expr))

(defun and-right (expr)
  (third expr))

(defun and-p (expr)
  (and (listp expr) (eq (car expr) 'and)))

;;; -----

;;; not

(defun make-not (expr)
  (list 'not expr))

(defun not-expr (expr)
  (second expr))

(defun not-p (expr)
  (and (listp expr) (eq (car expr) 'not)))

;;; -----

;;; implies

(defun make-implies (left right)
  (list 'implies left right))

(defun implies-left (expr)
  (second expr))

(defun implies-right (expr)
  (third expr))

(defun implies-p (expr)
  (and (listp expr) (eq (car expr) 'implies)))

;;; -----

;;; the "if" expression

(defun make-if (test left right)
  (list 'if test left right))

(defun if-test (expr)
  (second expr))

(defun if-left (expr)
  (third expr))

(defun if-right (expr)
  (fourth expr))

(defun if-p (expr)
  (and (listp expr) (eq (car expr) 'if)))

;;; -----

;;; Set membership.

(defun make-in (elem set)
  (list 'in elem set))

(defun in-elem (expr)
  (second expr))

(defun in-set (expr)
  (third expr))

(defun in-p (expr)
  (and (listp expr) (eq (car expr) 'in)))

;;; -----

;;; Subset.

(defun make-subset (left right)
  (list 'subset left right))

(defun subset-left (expr)
  (second expr))

(defun subset-right (expr)
  (third expr))

(defun zk-subset-p (expr)
  (and (listp expr) (eq (car expr) 'subset)))

;;; -----

;;; Type predicate (the logic iself is untyped).
;;; Types are simply sets.

(defun make-type-of (expr)
  (list 'type-of expr))

(defun type-of-expr (expr)
  (second expr))

(defun type-of-p (expr)
  (and (listp expr) (eq (car expr) 'type-of)))


;;; -----

;;; Ordinals.

(defun make-ord (expr)
  (list 'ord expr))

(defun ord-expr (expr)
  (second expr))

(defun ord-p (expr)
  (and (listp expr) (eq (car expr) 'ord)))

;;; -----

;;; Universal quantification.

(defun make-all (vars expr)
  (list 'all vars expr))

(defun all-vars (expr)
  (second expr))

(defun all-expr (expr)
  (third expr))

(defun all-p (expr)
  (and (listp expr) (eq (car expr) 'all)))


;;; Accessor for variable in the case where the expression is an
;;; expanded all.

(defun all-var (expression)
  (cond ((and (all-p expression)
              (= (length expression) 3)
              (= (length (second expression)) 1))
         (first (all-vars expression)))
        (t (error "Expression '~A' is not an expanded all." expression))))

(defun make-all-single (var expr) (make-all (list var) expr))

;;; -----

;;; Existential quantification.

(defun make-some (vars expr)
  (list 'some vars expr))

(defun some-vars (expr)
  (second expr))

(defun some-expr (expr)
  (third expr))

(defun some-p (expr)
  (and (listp expr) (eq (car expr) 'some)))

;;; Accessor for variable in the case where the expression is an
;;; expanded all.

(defun some-var (expression)
  (cond ((and (some-p expression)
              (= (length expression) 3)
              (= (length (second expression)) 1))
         (first (some-vars expression)))
        (t (error "Expression '~A' is not an expanded some." expression))))

(defun make-some-single (var expr) (make-some (list var) expr))


;;; ===== Internal Representation of Variables =====

;;; Internally, a variable is a symbol with a "rename" property.
;;; It is up to the front end to ensure that there are no clashes
;;; between function symbols and variable symbols.

;;; The separator string, useful for "subscripts".

(defparameter *variable-separator-string* "$")

;;; List of unsubscripted variables. The database manager maintains this.

(defvar *variables* nil)

;;; The "rename" of a variable is the "original" name of the variable.

(defmacro get-rename (variable)
  `(get ,variable 'rename))

;;; A function to recognize or otherwise "declare" a variable,
;;; i.e., variables are automagically declared on input.

(defun input-variable-p (variable)
  (and (symbolp variable)
       (or (get-rename variable)
           (let ((index
                  (string-search= *variable-separator-string* variable t)))
             (if (null index)
                 (unless (get-event variable)
                   (push variable *variables*)
                   (setf (get-rename variable) variable))
                 (let ((parent (intern (substring variable 0 index)
                                       *zk-package*)))
                   (unless (or (get-event parent) (get-rename parent))
                     (push parent *variables*)
                     (setf (get-rename parent) parent))
                   (push variable *variables*)
                   (setf (get-rename variable) parent)))))))

;;; Function to generate a new variable that is different from other
;;; variables (using gensym and without interning).
;;; The new variable gets the rename property of the old variable.

(defun genvar (variable)
  (let ((newname (gensym)))
    ;; get the original rename not some other
    (setf (get-rename newname) (get-rename variable))
    newname))

;;; The inverse of genvar. The table is an avoidance list.

(defun ungenvar (variable table)
  (let ((oldvar (get-rename variable)))
    ;; if there is no conflict then use the original
    (cond ((not (member-eq oldvar table)) oldvar)
          ;; otherwise generate one that doesn't conflict
          (t (loop for number = 0 then (1+ number)
                   for newvar = (intern (format nil "~A~A~A"
                                                oldvar
                                                *variable-separator-string*
                                                number)
                                        *zk-package*)
                   until (not (member-eq newvar table))
                   finally (progn (unless (get-rename newvar)
                                    (push newvar *variables*)
                                    (setf (get-rename newvar) oldvar))
                                  (return newvar)))))))

;;; Return non-nil iff the given variable was produced using genvar.

(defsubst genvarp (variable)
  (null (symbol-package variable)))

;;; Given a genvar list return a list of the printable versions.
(defun make-printable-genvars (genvar-list)
  (loop for genvar in genvar-list
	for count = 1 then (1+ count)
	collecting (list count (get-rename genvar))))

;;; Return the list of all genvars appearing in the expr.
(defun list-of-genvars (expr)
  (unique-symbol (list-of-genvars-aux expr nil)))

;;; Return the list of genvars in expr appended to the result.
(defun list-of-genvars-aux (expr result)
  (cond ((atom expr) (if (and (symbolp expr)
			      (null (symbol-package expr)))
			 (cons expr result)
			 result))
	(t (list-of-genvars-aux (car expr)
				(list-of-genvars-aux (cdr expr)
						     result)))))

;;; Return the list of all printable genvars appearing in the expr.
(defun list-of-printable-genvars (expr)
  (unique (list-of-printable-genvars-aux expr nil)))

;;; Return the list of printable genvars in expr appended to the result.
(defun list-of-printable-genvars-aux (expr result)
  (cond ((atom expr) result)
	((numberp (car expr)) (cons expr result))
	(t (list-of-printable-genvars-aux
	     (car expr)
	     (list-of-printable-genvars-aux2 (cdr expr) result)))))

;;; Just like above list-of-printable-genvars-aux but takes a list of exprs.
(defun list-of-printable-genvars-aux2 (expr-list result)
  (cond ((atom expr-list) result)		;watch for dots
	(t (list-of-printable-genvars-aux
	     (car expr-list)
	     (list-of-printable-genvars-aux2 (cdr expr-list) result)))))

;;; Return an alist of substitutions for the variable list which can
;;; then be used to sublis to obtain a renamed formula.
(defun rename-variable-list (variable-list)
  (mapcar #'(lambda (u) (cons u (genvar u))) variable-list))


;;; =====


;;; Function to return the topmost symbol in a formula.
;;; The topmost symbol is used for indexing, e.g., for rewrite rules.

(defun index-of (formula)
  (cond ((atom formula) (and (symbolp formula) formula))
        ((symbolp (car formula)) (car formula))
        (t nil)))                               ;no index

;;; Definitions for the literals 'true' and 'false'.

;;; Internal representation of true.

(defparameter *true* '(true))

;;; Internal representation of false.

(defparameter *false* '(false))

;;; Recognizer for true.

(defsubst true-p (formula) (equal formula '(true)))

;;; Recognizer for false.

(defsubst false-p (formula) (equal formula '(false)))

;;; Recognizer for variables.

(defun variable-p (formula)
  (and (symbolp formula) (get-rename formula)))

;;; Recognizer for constants (applications of nullary functions).

(defun constant-p (formula)
  (cond ((symbolp formula)
         (function-event-p (get-event formula)))
        ((listp formula)
         (and (constant-p (car formula))
              (null (cdr formula))))))

;;; Recognizer for literals.
;;; Currently returns non-nil for (TRUE), (FALSE) and integers.

(defun literal-p (formula)
  (or (equal formula *true*) (equal formula *false*) (integerp formula)))

;;; A recognizer for the union of literals and constants.

(defun litconst-p (formula)
  (or (literal-p formula) (constant-p formula)))


;;; Given a function name and a list of arguments, return a sublist
;;; of those arguments in measured positions.
(defsubst measured-subset-arguments (name arguments)
  (remove-if #'null
	     (mapcar #'(lambda (u v) (and u v))
		     (ufunction-measured-subset name)
		     arguments)))

;;; When predicate is non-nil, return nil, t or instantiations
;;; depending on whether reduction was successful and whether
;;; there were instantiations. Othwerwise just return the formula.
(defun result-of (formula predicate instantiations)
  (cond ((null predicate) formula)
	((equal predicate formula) (or instantiations t))))

;;; Lookup the binding for a variable in an association list of
;;; substitutions. If not bound, simply return the variable.
(defmacro binding-of (variable substitutions &optional (unbound variable))
  (let ((value (gensym)))
    `(let ((,value (assoc-eq ,variable ,substitutions)))
       (if ,value (cdr ,value) ,unbound))))


;;; Return non-nil if formula produces a "value".
;;; Literals and function applications of only value arguments are values
(defun value-p (formula)
  (cond ((literal-p formula) t)
	((atom formula) nil)
	((symbolp (car formula))
	 (let ((event (get-event (car formula))))
	   (and (or (and (ufunction-p event) (ufunction-computable event))
		    (and (function-stub-p event)
			 (function-stub-computable event)))
		(every #'value-p (cdr formula)))))))

;;; return the number of values in the formula-list
(defun count-values-list (formula-list)
  (let ((result 0))
    (dolist (element formula-list)
      (when (value-p element) (incf result)))
    result))


;;; The induction pattern is used for display purposes only.

(defparameter *induction-pattern* '|))P|)

;;; ==============================================================

;;; Functions for constructing assorted kinds of formulas.

;;; Produce a conjunction in "expanded" form from a list of conjuncts.

(defun make-conjunction (conjunct-list)
  (if (null conjunct-list) *true* (make-conjunction-aux conjunct-list)))

(defun make-conjunction-aux (conjunct-list)
  (if (null (cdr conjunct-list))
      (first conjunct-list)
      (make-and (first conjunct-list)
                (make-conjunction-aux (cdr conjunct-list)))))

;;; Produce a disjunction in "expanded" form from a list of disjuncts.

(defun make-disjunction (disjunct-list)
  (if (null disjunct-list) *false* (make-disjunction-aux disjunct-list)))

(defun make-disjunction-aux (disjunct-list)
  (if (null (cdr disjunct-list))
      (first disjunct-list)
      (make-or (first disjunct-list)
               (make-disjunction-aux (cdr disjunct-list)))))

;;; Produce a quantification in expanded form. The quantifier kind
;;; determines whether it is a universal or existential quantification.

(defun make-series-of-quantification (quantifier-kind variables formula)
  (cond ((eq quantifier-kind 'all) (universally-quantify variables formula))
        ((eq quantifier-kind 'some)
         (existentially-quantify variables formula))))

(defun make-quantification (quantifier-kind variable formula)
  (cond ((eq quantifier-kind 'all) (make-all-single variable formula))
	((eq quantifier-kind 'some) (make-some-single variable formula))))

(defun quantification-p (expr)
  (or (all-p expr) (some-p expr)))

(defun quantification-kind (expr) (car expr))

(defun quantification-var (expr) (car (second expr)))

(defun quantification-expr (e)
  (if (null (cdr (second e)))
      (third e)
    (list (first e) (cdr (second e)) (third e))))

(defun universally-quantify (variables formula)
  (cond ((null variables) formula)
        (t (make-all-single (car variables)
                            (universally-quantify (cdr variables) formula)))))

(defun existentially-quantify (variables formula)
  (cond ((null variables) formula)
        (t (make-some-single
             (car variables)
             (existentially-quantify (cdr variables) formula)))))

(defun closed-form (formula)
  (universally-quantify
   (unique (list-of-free-variables-unexpanded formula))
   formula))

;;; simplifications used while building expressions
;;;
;;; Note that some of the simplification rules used
;;; do not always return expressions equal in value to the originals
;;; e.g (and (true) x) => x  when x = 1.
;;; However, the resulting expression is always boolean equivalent.

(defun make-simplified-and (x y)
  (cond ((equal x *true*) y)
        ((equal x *false*) x)
        ((equal y *true*) x)
        ((equal y *false*) y)
        ((and-p x) (cons 'and (append (conjuncts-of x) (conjuncts-of y))))
        ((and-p y) (list* 'and x (conjuncts-of y)))
        (t (make-and x y))))

(defun conjuncts-of (x)
  (cond ((and-p x)
	 (loop for c in (cdr x)
	       append (conjuncts-of c)))
	(t (list x))))

(defun make-simplified-if (x y z)
  (cond ((equal x *true*) y)
        ((equal x *false*) z)
        ((equal y z) y)
        (t (make-if x y z))))

;;; add-simplified-conjuncts (cj term) makes a simplified version of 
;;;     `(and (and . ,cj) term)

(defun add-simplified-conjuncts (conjuncts term)
  (if (null conjuncts)
      term
      (make-simplified-and
       (car conjuncts)
       (add-simplified-conjuncts (cdr conjuncts) term))))


;;; Wrap an application of ORD around expr unless expr is an integer
;;; literal or an application of ORD, +, -, * or NEGATE.
(defun wrap-ord (expr)
  (cond ((or (integerp expr) (ord-p expr)
             (+-p expr) (--p expr) (*-p expr) (negate-p expr))
         expr)
        (t (list 'ord expr))))


;;; Primitives for finding lists of free or quantified variables.

;;; given a formula return a list of all variables refered to
;;; this is effectivelly the union of the free and bound variables
(defun list-of-all-variables (formula)
  (cond ((atom formula) (and (variable-p formula) (list formula)))
        (t (mapcan #'list-of-all-variables formula))))

;;; given a formula return a list of bound variables it uses
;;; these are all of the variables which are used by the quantifiers
(defun list-of-bound-variables (formula)
  (cond ((atom formula) nil)
        ((all-p formula)
         (cons (all-var formula) (list-of-bound-variables (all-expr formula))))
        ((some-p formula)
         (cons (some-var formula)
               (list-of-bound-variables (some-expr formula))))
        (t (mapcan #'list-of-bound-variables formula))))

(defun list-of-bound-variables-unexpanded (unexpanded-formula)
  (cond ((atom unexpanded-formula) nil)
        ((all-p unexpanded-formula)
         (append (all-vars unexpanded-formula)
                 (list-of-bound-variables-unexpanded
                   (all-expr unexpanded-formula))))
        ((some-p unexpanded-formula)
         (append (some-vars unexpanded-formula)
                 (list-of-bound-variables-unexpanded
                    (some-expr unexpanded-formula))))
        (t (mapcan #'list-of-bound-variables-unexpanded unexpanded-formula))))

;;; given a formula return a list of variables it uses free
;;; these are the variables which are used but not bound by quantifiers
(defun list-of-free-variables (formula)
  (list-of-free-variables-aux formula nil))

(defun list-of-free-variables-unexpanded (unexpanded-formula)
  (list-of-free-variables-unexpanded-aux unexpanded-formula nil))

;;; the workhorse for list-of-free-variables
;;; it returns a list of free variables for formula where bound-variables
;;; is a list of variables which a considered to be already bound in the
;;; formula

(defun list-of-free-variables-aux (formula bound-variables)
  (cond ((atom formula)
         (cond ((or (null formula)
                    (litconst-p formula)
                    (member-eq formula bound-variables)) nil)
               (t (list formula))))
        ((all-p formula)
         (list-of-free-variables-aux
           (all-expr formula)
           (cons (all-var formula) bound-variables)))
        ((some-p formula)
         (list-of-free-variables-aux
           (some-expr formula)
           (cons (some-var formula) bound-variables)))
        (t (mapcan
             #'(lambda (u) (list-of-free-variables-aux u bound-variables))
             formula))))

(defun list-of-free-variables-unexpanded-aux (formula bound-variables)
  (cond ((atom formula)
         (cond ((or (null formula)
                    (litconst-p formula)
                    (member-eq formula bound-variables)) nil)
               (t (list formula))))
        ((all-p formula)
         (list-of-free-variables-unexpanded-aux
           (all-expr formula)
           (append (all-vars formula) bound-variables)))
        ((some-p formula)
         (list-of-free-variables-unexpanded-aux
           (some-expr formula)
           (append (some-vars formula) bound-variables)))
        (t (mapcan
             #'(lambda (u)
                (list-of-free-variables-unexpanded-aux u bound-variables))
             formula))))


;;; Functions for finding calls in a formula.

;;; return non-nil if there is a call to the function in formula
(defun calls-p (function formula)
  (cond ((atom formula) nil)
        ((eq (car formula) function))
        (t (some #'(lambda (u) (calls-p function u))
                 formula))))

;;; return non-nil if there is a call to any of the functions in formula
(defun calls-any-p (function-list formula)
  (cond ((atom formula) nil)
        ((member-eq (car formula) function-list))
        (t (some #'(lambda (u) (calls-any-p function-list u))
                 formula))))

;;; return non-nil if either of the quantifiers occurs in the formula
(defun contains-quantifier (formula)
  (calls-any-p '(all some) formula))

;;; return a list of the calls to function in formula
;;; it includes all calls even those nested within other calls
(defun list-of-calls (function formula)
  (list-of-calls-aux function formula nil))

;;; auxilliary function for the function list-of-calls
;;; it adds the calls in to function in formula to those already in aux
;;; returning the result consisting of all the calls in formula and aux
(defun list-of-calls-aux (function formula aux)
  (cond ((atom formula) aux)
        ((eq (car formula) function)
         (cons formula (list-of-calls-aux function (cdr formula) aux)))
        (t (list-of-calls-aux function (car formula)
                              (list-of-calls-aux function (cdr formula) aux)))))


;;; Functions for finding calls in a formula continued.

;;; return a list of all the functions which are referenced by a formula
;;; notice we do consider the quantifiers to be functions (though they're not)
;;; the functions returned are only those which are actually applied in the
;;; formula
(defun list-of-applied-functions (formula)
  (cond ((atom formula) nil)
        ((symbolp (car formula))
         (cons (car formula)
               (mapcan #'list-of-applied-functions (cdr formula))))
        (t (mapcan #'list-of-applied-functions formula))))

;;; given some formula return it represented as a list of conjuncts
;;; if the formula is not a conjunction then a single element list is returned
(defun list-of-conjuncts (formula)
  (list-of-conjuncts-aux formula nil))

;;; auxilliary function for the function list-of-conjuncts
;;; it adds the conjuncts in formula to those already in aux
;;; returning the result consisting of all the conjuncts in formula and aux
(defun list-of-conjuncts-aux (formula aux)
  (if (or (not (if-p formula)) (not (equal (if-right formula) *false*)))
      (cons formula aux)
      (list-of-conjuncts-aux (if-test formula)
                             (list-of-conjuncts-aux (if-left formula) aux))))

;;; Additiona predicates on expressions.

(defsubst simple-expression-p (sexpr)
  (or (litconst-p sexpr)
      (symbolp sexpr)))

;;; returns t if the given expression is a '>=' or '=' with simple left
;;; and right parts, returns nil otherwise.

(defsubst simple-relation-p (expr)
  (and (or (>=-p expr) (=-p expr))
       (simple-expression-p (second expr))
       (simple-expression-p (third expr))))

;;; Given an 'all return a 'some, and given a 'some return an 'all.

(defsubst other-quantifier-kind (quantifier-kind)
  (cond ((eq quantifier-kind 'all) 'some)
	((eq quantifier-kind 'some) 'all)))

;;; Operator may be an integer relation.
;;; Used by the simplifier.

(defun integer-relation-operator-p (operator)
  (or (eq operator '=) (eq operator '>=)))

;;; Given the test, left, and right parts of an if expression, replace either
;;; the left part or right part by the alternate, depending on the value of
;;; alter-left.

(defsubst alter-branch (test left right alternate alter-left)
  (if alter-left
      (make-if test alternate right)
      (make-if test left alternate)))


;;; Given a symbol, return a pair:
;;; if symbol is BLAH.PO: BLAH . PO
;;; otherwise: symbol . nil

(defun true-name (name)
  (let ((index nil))
    (cond ((and (setq index (string-search= ".PO" name))
                (= (string-length name) (+ index 3)))
           (cons (intern (substring name 0 index) *zk-package*)
		 'po))
          (t (cons name nil)))))
