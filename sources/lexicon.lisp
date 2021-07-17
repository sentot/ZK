
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

;;; =====================================================================
;;; ========================  L E X I C O N  ============================
;;; =====================================================================
;;;
;;;     Lexicon of the "core" Lisp used. Most symbols are ANSI Common
;;;     Lisp symbols, but additional symbols are also defined here.
;;;
;;;     The lexicon is enforced using the package mechanism of ANSI
;;;     Common Lisp. A ZK package must first be defined which uses no
;;;     other packages. ANSI Common Lisp symbols that are in the lexicon
;;;     are then imported. The imports are done exclusively in this file.
;;;
;;;     In addition to the ANSI Common Lisp symbols, this file also
;;;     contains definitions of utilities that may be read-time
;;;     conditionalized for the different Lisp systems.
;;;
;;;     The file is structured according to Guy Steele's book
;;;     "Common Lisp the Language".
;;;
;;; =====================================================================


;;; =====================================================================
;;;
;;; Chapter 2 - Data Types
;;;
;;; =====================================================================


;;; Section 2.1 - Numbers

;;; Subsection 2.1.1 - Integers
;;;     The ZK system requires arbitrary precision integers.

;;; Subsection 2.1.2 - Ratios
;;;     The ZK system uses ratios.  However, for extra clarity, we
;;;     define cover functions for rational operations in the appendix.

;;; Subsection 2.1.3 - Floating Point Numbers
;;;     The ZK system makes minimal use of floating point numbers.
;;;     They are only used in utilities for dealing with timing.


;;; Section 2.2 - Characters

;;; Subsection 2.2.1 - Standard Characters
;;;     The ZK system uses all of the Common Lisp standard
;;;     characters.

;;; Subsection 2.2.2 - Line Divisions
;;;     The ZK system uses the #\Newline character.

;;; Subsection 2.2.5 - String Characters
;;;     The ANSI standard removed string-char subtype of
;;;     characters.  The ZK system does not use attributes of characters.


;;; Section 2.3 - Symbols
;;;     The ZK system uses symbols with no restrictions.


;;; Section 2.4 - Lists and Conses
;;;     The ZK system uses lists and conses.


;;; Section 2.5 - Arrays
;;;     The ZK system uses arrays.


;;; Subsection 2.5.1 - Vectors
;;;     The ZK system uses vectors.

;;; Subsection 2.5.2 - Strings
;;;     The ZK system uses strings.

;;; Section 2.6 - Hash Tables
;;;     The ZK system uses hash tables.


;;; Section 2.10 - Packages
;;;     The ZK system uses packages.


;;; Section 2.9 - Pathnames
;;;     The ZK system uses pathnames.


;;; Section 2.10 - Streams
;;;     The ZK system uses streams.


;;; Section 2.12 - Structures
;;;     The ZK system uses structures.


;;; Section 2.13 - Functions
;;;     The ZK system uses functions.


;;; =====================================================================
;;;
;;; Chapter 3 - Scope and Extent
;;;
;;; =====================================================================

;;;     The ZK system relies on the following scope and extent
;;;     features of Common Lisp:
;;;
;;;     - Lexical scope.  Currently, the lexical scope feature is only
;;;       used in a limited way: free variables are allowed in lambda
;;;       expressions passed to mapping functions.
;;;
;;;     - Indefinite scope.  No restriction is placed on the use of
;;;       this feature.
;;;
;;;     - Dynamic extent.  The binding of special variables in ZK
;;;       rely on this feature of Common Lisp.
;;;
;;;     - Indefinite extent.  No restriction is placed on the use of
;;;       this feature.


;;; =====================================================================
;;;
;;; Chapter 4 - Type Specifiers
;;;
;;; =====================================================================

;;; Section 4.1 - Type Specifier Symbols

;;;      The ZK system uses the following type specifier symbols:
;;;      "array", "atom", "bignum", "character", "compiled-function",
;;;      "cons", "float", "function", "hash-table", "integer", "keyword",
;;;      "list", "nil", "null", "number", "package", "pathname", "ratio",
;;;      "rational", "sequence", "standard-char", "stream", "string",
;;;      "symbol", "t", and "vector".

(cl:import '(cl:array cl:atom cl:bignum cl:character
                      cl:compiled-function cl:cons cl:float
                      cl:function cl:hash-table cl:integer
                      cl:keyword cl:list cl:nil cl:null cl:number
                      cl:package cl:pathname cl:ratio cl:rational
                      cl:sequence cl:standard-char cl:stream
                      cl:string cl:symbol cl:t
                      cl:vector))

;;; Section 4.6 - Type Specifiers That Abbreviate
;;;     The ZK system uses the "unsigned-byte" abbreviation.

(cl:import '(cl:unsigned-byte))

;;; Section 4.9 - Determining the Type of an Object
;;;     The ZK system uses the function "type-of".

(cl:import '(cl:type-of))


;;; =====================================================================
;;;
;;; Chapter 5 - Program Structure
;;;
;;; =====================================================================


;;; Section 5.1 - Forms

;;; Subsection 5.1.1 - Self-Evaluating Forms
;;;     The ZK system uses self-evaluating forms.

;;; Subsection 5.1.2 - Variables
;;;     The ZK system uses both lexical and special variables.

;;; Subsection 5.1.3 - Special Forms

;;;     The ZK system uses the following special forms:
;;;     "catch", "declare", "eval-when", "function", "if", "let", "let*",
;;;     "progn", "quote", "return-from", "setq", "throw",
;;;     and "unwind-protect".

(cl:import '(cl:catch cl:declare cl:eval-when cl:function cl:if
                      cl:let cl:let* cl:progn cl:quote cl:return-from
                      cl:setq cl:throw cl:unwind-protect))

;;; Subsection 5.1.4 - Macros
;;;     The ZK system uses macros.

;;; Subsection 5.1.5 - Function Calls
;;;     The ZK system uses function calls.


;;; Section 5.2 - Functions

;;; Subsection 5.2.2 - Named Functions
;;;     The ZK system uses only global named functions.

;;; Subsection 5.2.2 - Lambda-Expressions
;;;     The ZK system uses lambda expressions.  All the argument
;;;     keywords are used by the system.

(cl:import '(cl:lambda cl:&optional cl:&rest cl:&key cl:&aux))

;;; Section 5.3 - Top-Level Forms

;;; Subsection 5.3.1 - Defining Named Functions
;;;     The ZK system uses the "defun" special form.

(cl:import '(cl:defun))

;;; Subsection 5.3.2 - Declaring Global Variables and Named Constants
;;;     The ZK system uses the "defvar", "defparameter", and "defconstant"
;;;     special forms.

(cl:import '(cl:defvar cl:defparameter cl:defconstant))

;;; Subsection 5.3.3 - Control of Time of Evaluation
;;;     The ZK system uses the "eval-when" special form.

(cl:import '(cl:eval-when))


;;; =====================================================================
;;;
;;; Chapter 6 - Predicates
;;;
;;; =====================================================================


;;; Section 6.1 - Logical Values
;;;     The ZK system uses "nil" and "t" for logical values.

(cl:import '(cl:nil cl:t))

;;; Section 6.2 - Data Type Predicates

;;; Subsection 6.2.2 - Specific Data Type Predicates
;;;     The ZK system uses "null", "symbolp", "atom", "consp",
;;;     "listp", "numberp", "integerp", "rationalp", "floatp",
;;;     "characterp", "stringp", "vectorp", "arrayp", "packagep",
;;;     "functionp", and "compiled-function-p".

(cl:import '(cl:null cl:symbolp cl:atom cl:consp cl:listp
                     cl:numberp cl:integerp cl:rationalp cl:floatp
                     cl:characterp cl:stringp cl:vectorp cl:arrayp
                     cl:packagep cl:functionp cl:compiled-function-p))

;;; Section 6.3 - Equality Predicates
;;;     The ZK system uses "eq" and "equal".

(cl:import '(cl:eq cl:equal))

;;; ------ Additional functionality ------
;;; The ``not eq'' predicate.

(cl:defmacro neq (x y) `(cl:not (cl:eq ,x ,y)))

;;; ---------------------------------------

;;; Section 6.4 - Logical Operators
;;;     The ZK system uses "not", "and", and "or".

(cl:import '(cl:not cl:and cl:or))


;;; =====================================================================
;;;
;;; Chapter 7 - Control Structure
;;;
;;; =====================================================================


;;; Section 7.1 - Constants and Variables

;;; Subsection 7.1.1 - Reference
;;;     The ZK system uses "quote", "function", "symbol-value",
;;;     "symbol-function" "boundp" and "fboundp".

(cl:import '(cl:quote cl:function cl:symbol-value cl:symbol-function
                      cl:boundp cl:fboundp))

;;; Subsection 7.1.2 - Assignment
;;;     The ZK system uses "setq" and set".

(cl:import '(cl:setq cl:set))

;;; Section 7.2 - Generalized Variables
;;;     The ZK system uses "setf".  "setf" is allowed on all accessor
;;;     functions used by the system.

(cl:import '(cl:setf))

;;; ------ Additional functionality ------

;;; Define swapf to be a two-argument version of rotatef.

(cl:defmacro swapf (x y)
  `(cl:rotatef ,x ,y))

;;; --------------------------------------


;;; Section 7.3 - Function Invocation
;;;    The ZK system uses "apply" and "funcall".

(cl:import '(cl:apply cl:funcall))

;;; Section 7.4 - Simple Sequencing
;;;    The ZK system uses "progn" and "prog1".

(cl:import '(cl:progn cl:prog1))

;;; Section 7.5 - Establishing New Variable Bindings
;;;    The ZK system uses "let" and "let*".

(cl:import '(cl:let cl:let*))

;;; Section 7.6 - Conditionals
;;;    The ZK system uses "if", "when", "unless", "cond", and "case".

(cl:import '(cl:if cl:when cl:unless cl:cond cl:case))

;;; Section 7.7 - Blocks and Exits
;;;    The ZK system uses "return-from" and "return".

(cl:import '(cl:return-from cl:return))


;;; Section 7.8 - Iteration

;;; Subsection 7.8.1 - Indefinite Iteration
;;;    The ZK system uses the more powerful (than the simple) "loop"
;;;    macro.  For Lisp implementations that do not provide this
;;;    capability, we use the standard M.I.T. loop macro described
;;;    in Burke, G. and Moon, D., "LOOP Iteration Macro", M.I.T L.C.S.
;;;    Technical Report, 1981.  The source for this is in loop.lisp.

(cl:import '(cl:loop))

;;; Subsection 7.8.2 - General Iteration
;;;    The ZK system uses "do" and "do*".

(cl:import '(cl:do cl:do*))

;;; ------ Additional functionality ------

;;; Define a while loop macro.

(cl:defmacro while (test cl:&body forms)
  `(cl:do () ((cl:not ,test) cl:t) . ,forms))

;;; Subsection 7.8.3 - Simple Iteration Constructs
;;;    The ZK system uses "dolist" and "dotimes".

(cl:import '(cl:dolist cl:dotimes))

;;; Subsection 7.8.4 - Mapping
;;;    The ZK system uses "mapcar", "maplist", "mapc", "mapl",
;;;    "mapcan", and "mapcon".

(cl:import '(cl:mapcar cl:maplist cl:mapc cl:mapl
                       cl:mapcan cl:mapcon))


;;; Section 7.9 - Multiple Values

;;; Subsection 7.9.1 - Constructs for Handling Multiple Values
;;;     The ZK system uses "values", "multiple-value-bind", and
;;;     "multiple-value-setq".

(cl:import '(cl:values cl:multiple-value-bind cl:multiple-value-setq))

;;; Section 7.10 - Dynamic Non-local Exits
;;;     The ZK system uses "catch", "unwind-protect", and "throw".

(cl:import '(cl:catch cl:unwind-protect cl:throw))


;;; =====================================================================
;;;
;;; Chapter 8 - Macros
;;;
;;; =====================================================================


;;; Section 8.1 - Macro Definition
;;;     The ZK system uses the "defmacro" macro.  All the argument
;;;     keywords allowed for lambda expressions are also allowed in macro
;;;     definitions.  In addition, the system uses the "&body" argument
;;;     keyword.

(cl:import '(cl:defmacro cl:&body))


;;; =====================================================================
;;;
;;; Chapter 9 - Declarations
;;;
;;; =====================================================================


;;; Section 9.1 - Declaration Syntax
;;;     The ZK system uses "declare" and "proclaim".

(cl:import '(cl:declare cl:proclaim))

;;; Section 9.2 - Declaration Specifiers
;;;     The ZK system uses "special", "inline", "ignore",
;;;     and "optimize".

(cl:import '(cl:special cl:inline cl:ignore cl:optimize))

;;; ------ Additional functionality ------

;;; Define defsubst macro for inline function definitions

(cl:defmacro defsubst (name args cl:&body body)
   `(cl:progn (cl:proclaim '(cl:inline ,name))
              (cl:defun ,name ,args . ,body)))


;;; --------------------------------------


;;; =====================================================================
;;;
;;; Chapter 10 - Symbols
;;;
;;; =====================================================================


;;; Section 10.1 - The Property List
;;;     The ZK system uses property lists, "get", "remprop", "getf",
;;;     and "remf".

(cl:import '(cl:get cl:remprop cl:getf cl:remf))

;;; Section 10.3 - Creating Symbols
;;;     The ZK system uses "gensym" and "symbol-package".

(cl:import '(cl:gensym cl:symbol-package))


;;; =====================================================================
;;;
;;; Chapter 11 - Packages
;;;
;;; =====================================================================

;;;    The ZK system uses the package mechanism for two reasons:
;;;      - to enforce the lexicon; and
;;;      - to avoid name clashes with other software loaded in the
;;;        Lisp environment.


;;; Section 11.6 - Built-In Packages
;;;     The ZK system imports symbols from the "lisp" package
;;;     and uses symbols from the "keyword" package.


;;; Section 11.7 - Package System Functions and Variables
;;;     The ZK system uses "*package*", "in-package", "intern",
;;;     "export", and "import".

(cl:import '(cl:*package* cl:in-package cl:export cl:import))

;;; Leaving off the (optional) package is a constant source of errors, so we
;;; make it mandatory in ZK.

(cl:defmacro intern (sym pkg)
  `(cl:intern ,sym ,pkg))

(cl:import '(cl:do-symbols))


;;; --------------------------------------


;;; =====================================================================
;;;
;;; Chapter 12 - Numbers
;;;
;;; =====================================================================

;;;     The ZK system uses only three of the four categories of
;;;     Common Lisp numbers: integers, ratios, and floating points.


;;; Section 12.2 - Predicates on Numbers
;;;     The ZK system uses "zerop", "plusp", and "minusp".

(cl:import '(cl:zerop cl:plusp cl:minusp))

;;; Section 12.3 - Comparison on Numbers
;;;     The ZK system uses "=", "/=", "<", ">", "<=", and ">="
;;;     always with two arguments.  The system also uses "max" and "min".

(cl:import '(cl:= cl:/= cl:< cl:> cl:<= cl:>= cl:max cl:min))

;;; Section 12.4 - Arithmetic Operations
;;;     The ZK system uses "+", "-", "*", "/", "1+", "1-", "incf",
;;;     "decf", "gcd", and "lcm".

(cl:import '(cl:+ cl:- cl:* cl:/ cl:1+ cl:1- cl:incf cl:decf
                  cl:gcd cl:lcm))

;;; ------ Additional functionality ------

;;; Define quotient as Common Lisp's "truncate" on two integers.

(cl:defmacro quotient (number divisor)
  `(cl:truncate ,number ,divisor))

;;; --------------------------------------


;;; Section 12.5 - Irrational and Transcendental Functions

;;; Subsection 12.5.1 - Exponential and Logarithmic Functions
;;;     The ZK system uses "expt".

(cl:import '(cl:expt))

;;; Subsection 12.5.2 - Trigonometric and Related Functions
;;;     The ZK system uses "abs".

(cl:import '(cl:abs))


;;; Section 12.6 - Type Conversions and Component Extractions on Numbers
;;;     The ZK system uses "float", "floor", "ceiling", "truncate",
;;;     "round", "mod", "rem, "numerator", and "denominator"".

(cl:import '(cl:float cl:floor cl:ceiling cl:truncate cl:round
                      cl:mod cl:rem cl:numerator cl:denominator))


;;; Section 12.7 - Logical Operations on Numbers
;;;     The ZK system uses "ash" and "logand"

(cl:import '(cl:ash cl:logand))

;;; Section 12.8 - Byte Manipulation Functions
;;;     The ZK system uses "byte", "ldb", and "dpb".

(cl:import '(cl:byte cl:ldb cl:dpb))

;;; ------ Additional functionality ------

;;; for optimization of arithmetic and logical operations in various lisps,
;;; the common denominator seems to be to assert that the operands and results
;;; are all fixnums.  We provide a simple way to do this with the following
;;; macro, e.g. (fixnum-op + foo (fixnum-op * 3 baz)) or
;;;  (fixnum-rel < x y)

(cl:defmacro fixnum-op (op x y)
  `(cl:the cl:fixnum (,op (cl:the cl:fixnum ,x)
                          (cl:the cl:fixnum ,y))))

;; can/should we declare the result type?
(cl:defmacro fixnum-rel (op x y)
  `(,op (cl:the cl:fixnum ,x)
        (cl:the cl:fixnum ,y)))


;;; =====================================================================
;;;
;;; Chapter 13 - Characters
;;;
;;; =====================================================================


;;; Section 13.2 - Predicates on Characters
;;;     The ZK system uses "standard-char-p", "graphic-char-p",
;;;     "alpha-char-p", "upper-case-p", "lower-case-p",
;;;     "digit-char-p", "char=", and "char-equal".

(cl:import '(cl:standard-char-p cl:graphic-char-p
                                cl:alpha-char-p cl:upper-case-p
                                cl:lower-case-p cl:digit-char-p
                                cl:char= cl:char-equal))

;;; Section 13.3 - Character Construction and Selection
;;;     The ZK system uses "char-code" and "code-char".

(cl:import '(cl:char-code cl:code-char))


;;; =====================================================================
;;;
;;; Chapter 14 - Sequences
;;;
;;; =====================================================================


;;; Section 14.1 - Simple Sequence Functions
;;;     The ZK system uses "subseq", "length", "reverse", and "nreverse".

(cl:import '(cl:subseq cl:length cl:reverse cl:nreverse))

;;; Section 14.2 - Concatenating, Mapping, and Reducing Sequences
;;;     The ZK system uses "some" and "every".

(cl:import '(cl:some cl:every))

;;; Section 14.3 - Modifying Sequences
;;;     The ZK system uses "remove-if" and "remove-if-not".

(cl:import '(cl:remove-if cl:remove-if-not))

;;; ------ Alternative functionality ------

;;;     A convention for the ZK system is to avoid passing
;;;     a test function as a parameter.  As a result, cover macros
;;;     are defined for functions which require test functions.

;;; Alternatives for "remove" and "delete".

(cl:defmacro remove-eq (item sequence cl:&optional count)
  `(cl:remove ,item ,sequence :test #'cl:eq . ,(cl:and count `(:count ,count))))

(cl:defmacro remove-equal (item sequence cl:&optional count)
  `(cl:remove ,item ,sequence
              :test #'cl:equal . ,(cl:and count `(:count ,count))))

(cl:defmacro delete-eq (item sequence cl:&optional count)
  `(cl:delete ,item ,sequence
              :test #'cl:eq . ,(cl:and count `(:count ,count))))

(cl:defmacro delete-equal (item sequence cl:&optional count)
  `(cl:delete ,item ,sequence
              :test #'cl:equal . ,(cl:and count `(:count ,count))))

;;; ---------------------------------------


;;; Section 14.5 - Sorting and Merging
;;;     The ZK system uses "sort".

(cl:import '(cl:sort))


;;; =====================================================================
;;;
;;; Chapter 15 - Lists
;;;
;;; =====================================================================


;;; Section 15.1 - Conses
;;;     The ZK system uses "car", "cdr", ... , "cddddr", and "cons".

(cl:import '(cl:car cl:cdr
                    cl:caar cl:cadr cl:cdar cl:cddr
                    cl:caaar cl:caadr cl:cadar cl:caddr
                    cl:cdaar cl:cdadr cl:cddar cl:cdddr
                    cl:caaaar cl:caaadr cl:caadar cl:caaddr
                    cl:cadaar cl:cadadr cl:caddar cl:cadddr
                    cl:cdaaar cl:cdaadr cl:cdadar cl:cdaddr
                    cl:cddaar cl:cddadr cl:cdddar cl:cddddr
                    cl:cons))

;;; Section 15.2 - Lists
;;;     The ZK system uses "endp", "nth", "first", "second", ... ,
;;;     "tenth", "rest", "nthcdr", "last", "list", "list*", "make-list",
;;;     "append", "copy-list", "copy-tree", "revappend", "nconc",
;;;     "nreconc", "push", "pushnew", "pop", and "butlast".

(cl:import '(cl:endp cl:nth cl:first cl:second cl:third cl:fourth
                     cl:fifth cl:sixth cl:seventh cl:eighth
                     cl:ninth cl:tenth cl:rest cl:nthcdr cl:last
                     cl:list cl:list* cl:make-list cl:append
                     cl:copy-list cl:copy-tree cl:revappend cl:nconc
                     cl:nreconc cl:push cl:pushnew cl:pop
                     cl:butlast))


;;; Section 15.4 - Substitution of Expressions

;;; ------ Alternative functionality ------

;;; Alternatives for "subst" and "sublis".

(cl:defmacro subst-eq (new old tree)
  `(cl:subst ,new ,old ,tree :test #'cl:eq))

(cl:defun subst-equal (new old list)
  (cl:cond ((cl:equal old list) new)
           ((cl:atom list) list)
           (cl:t (subst-equal-list new old list))))

(cl:defun subst-equal-list (new old list)
  (cl:mapcar #'(cl:lambda (u) (subst-equal new old u)) list))

(cl:defmacro sublis-eq (alist tree)
  `(cl:sublis ,alist ,tree :test #'cl:eq))


;;; Need assoc-equal (formally introduced in 15.6) for sublis-equal, but some
;;; Lisps complain about redefinition.

(cl:defun sublis-equal (alist list)
  (cl:let ((pair (cl:assoc list alist :test #'cl:equal)))
    (cl:cond (pair (cl:cdr pair))
             ((cl:atom list) list)
             (cl:t (sublis-equal-list alist list)))))

(cl:defun sublis-equal-list (alist list)
  (cl:mapcar #'(cl:lambda (u) (sublis-equal alist u)) list))

;;; ---------------------------------------


;;; Section 15.5 - Using Lists as Sets

;;; ------ Alternative functionality ------

;;; Alternatives for "member", "set-difference", "union",
;;; "intersection", and "subsetp".

(cl:defmacro member-eq (item list)
  `(cl:member ,item ,list :test #'cl:eq))

(cl:defmacro member-equal (item list)
  `(cl:member ,item ,list :test #'cl:equal))

;;;    The ZK system uses its own set operations which are more
;;;    predictable than their Common Lisp counterparts.

(cl:defun set-difference-eq (list0 list1)
  (cl:cond ((cl:null list0) cl:nil)
           ((member-eq (cl:car list0) list1)
            (set-difference-eq (cl:cdr list0) list1))
           (cl:t
            (cl:cons (cl:car list0) (set-difference-eq (cl:cdr list0) list1)))))

(cl:defun set-difference-equal (list0 list1)
  (cl:cond ((cl:null list0) cl:nil)
           ((member-equal (cl:car list0) list1)
            (set-difference-equal (cl:cdr list0) list1))
           (cl:t
            (cl:cons (cl:car list0)
                     (set-difference-equal (cl:cdr list0) list1)))))

(cl:defun union-eq (list0 list1)
  (cl:append list0 (set-difference-eq list1 list0)))

(cl:defun union-equal (list0 list1)
  (cl:append list0 (set-difference-equal list1 list0)))

(cl:defun intersection-eq (list0 list1)
  (cl:cond ((cl:null list0) cl:nil)
           ((member-eq (cl:car list0) list1)
            (cl:cons (cl:car list0) (intersection-eq (cl:cdr list0) list1)))
           (cl:t (intersection-eq (cl:cdr list0) list1))))

(cl:defun intersection-equal (list0 list1)
  (cl:cond ((cl:null list0) cl:nil)
           ((member-equal (cl:car list0) list1)
            (cl:cons (cl:car list0) (intersection-equal (cl:cdr list0) list1)))
           (cl:t (intersection-equal (cl:cdr list0) list1))))

(cl:defun subsetp-eq (list0 list1)
  (cl:every #'(cl:lambda (u) (member-eq u list1)) list0))

(cl:defun subsetp-equal (list0 list1)
  (cl:every #'(cl:lambda (u) (member-equal u list1)) list0))

;;; ---------------------------------------


;;; Section 15.6 - Association Lists
;;;     The ZK system uses "pairlis".

(cl:import '(cl:pairlis))

;;; ------ Alternative functionality ------

;;; Alternatives for "assoc" and "rassoc".

(cl:defmacro assoc-eq (item alist)
  `(cl:assoc ,item ,alist :test #'cl:eq))

(cl:defmacro assoc-equal (item alist)
  `(cl:assoc ,item ,alist :test #'cl:equal))

(cl:defmacro rassoc-eq (item alist)
  `(cl:rassoc ,item ,alist :test #'cl:eq))

(cl:defmacro rassoc-equal (item alist)
  `(cl:rassoc ,item ,alist :test #'cl:equal))

;;; ---------------------------------------



;;; =====================================================================
;;;
;;; Chapter 16 - Hash Tables
;;;
;;; =====================================================================


;;; Section 16.1 - Hash Table Functions
;;;     The ZK system uses "make-hash-table", "hash-table-p",
;;;     "gethash", "remhash", "maphash", "clrhash" and "sxhash".

(cl:import '(cl:make-hash-table cl:hash-table-p cl:gethash cl:remhash
                                cl:maphash cl:clrhash cl:sxhash))


;;; =====================================================================
;;;
;;; Chapter 17 - Arrays
;;;
;;; =====================================================================


;;; Section 17.1 - Array Creation
;;;     The ZK system uses "make-array" and "vector".

(cl:import '(cl:make-array cl:vector))

;;; Section 17.2 - Array Access
;;;     The ZK system uses "aref".

(cl:import '(cl:aref))

;;; Additional functionality:
;;; for optimization, we can use "unsafe-aref", that assumes that the
;;; first argument is a one-dimensional array and the second a fixnum.

(cl:defmacro unsafe-aref (array index)
  `(cl:aref (cl:the (cl:array t) ,array) (cl:the cl:fixnum ,index)))


;;; Section 17.3 - Array Information
;;;     The ZK system uses "array-total-size".

(cl:import '(cl:array-total-size))


;;; Section 17.5 - Fill Pointers
;;;     The ZK system uses "fill-pointer", "vector-push",
;;;     "vector-push-extend", and "vector-pop".

(cl:import '(cl:fill-pointer cl:vector-push cl:vector-push-extend
                             cl:vector-pop))

;;; Section 17.6 - Changing the Dimensions of an Array
;;;     The ZK system uses "adjust-array".

(cl:import '(cl:adjust-array))


;;; =====================================================================
;;;
;;; Chapter 18 - Strings
;;;
;;; =====================================================================


;;; Section 18.1 - String Access
;;;     The ZK system uses "char".

(cl:import '(cl:char))

;;; ------ Additional functionality ------

;;; Define string-length.

(cl:defmacro string-length (string)
  `(cl:length (cl:string ,string)))

;;; --------------------------------------

;;; Section 18.2 - String Comparison
;;;     The ZK system uses "string=", "string-equal",
;;;     "string<", and "string-lessp".

(cl:import '(cl:string= cl:string-equal cl:string< cl:string-lessp))

;;; ------ Additional functionality ------

;;; Define string search routines.

(cl:defmacro string-search= (key string cl:&optional from-end)
  `(cl:search (cl:string ,key) (cl:string ,string)
              :test #'cl:char=  :from-end ,from-end))

(cl:defmacro string-search-equal (key string cl:&optional from-end)
  `(cl:search (cl:string ,key) (cl:string ,string)
              :test #'cl:char-equal :from-end ,from-end))

;;; --------------------------------------


;;; Section 18.3 - String Construction and Manipulation
;;;     The ZK system uses "make-string", "string-trim", "string-upcase",
;;;     "string-downcase", "string-capitalize", and "string".

(cl:import '(cl:make-string cl:string-trim cl:string-upcase
                            cl:string-downcase cl:string-capitalize
                            cl:string))

;;; ------ Additional functionality ------

;;; Define string-append and substring.

(cl:defun string-append (cl:&rest strings)
  (cl:apply #'cl:concatenate `(cl:string . ,(cl:mapcar #'cl:string strings))))

(cl:defmacro substring (string start cl:&optional to)
  (cl:cond ((cl:null to)
           `(cl:subseq (cl:string ,string) ,start (string-length ,string)))
           (cl:t `(cl:subseq (cl:string ,string)
                             ,start
                             ,to))))

(cl:defun string-from-sequence (seq)
  (cl:coerce seq 'cl:string))

;;; --------------------------------------


;;; =====================================================================
;;;
;;; Chapter 19 - Structures
;;;
;;; =====================================================================


;;; ------ Additional functionality ------

;;; Fill structure with corresponding elements from list.

(cl:defmacro fillstruct (struct list)
  `(cl:replace ,struct ,list))

;;; List of elements of the structure.

(cl:defmacro liststruct (struct)
  `(cl:concatenate 'list ,struct))


;;; --------------------------------------


;;; Section 19.2 - How to use Defstruct
;;;     The ZK system uses "defstruct" with a restricted set of
;;;     options, which appears in Section 19.5.

(cl:import '(cl:defstruct))


;;; Section 19.3 - Using the Automatically Defined Constructor Function
;;;     The ZK system uses automatically defined constructor
;;;     functions as well as by-position constructors.


;;; Section 19.5 - Defstruct Options
;;;     The ZK system uses the following options:
;;;         :constructor,
;;;         :copier with no arguments,
;;;         :predicate with no arguments,
;;;         :include with no defaults,
;;;         :print-function,
;;;         :type, and
;;;         :named.


;;; =====================================================================
;;;
;;; Chapter 20 - The Evaluator
;;;
;;; =====================================================================
;;;     The ZK system uses "eval".

(cl:import '(cl:eval))



;;; =====================================================================
;;;
;;; Chapter 21 - Streams
;;;
;;; =====================================================================


;;; ------ Additional functionality ------

;;; Return the print line width, or *default-line-length* if it is undefined.

(cl:defvar *default-print-width* 79)

(cl:defun size-in-characters (cl:&optional (stream cl:*standard-output*))
  stream *default-print-width*)

;;; --------------------------------------


;;; Section 21.1 - Standard Streams
;;;     The ZK system uses *standard-input*, *standard-output*,
;;;     *error-output*, and *query-io*.

(cl:import '(cl:*standard-input* cl:*standard-output*
                                 cl:*error-output* cl:*query-io*))

;;; Section 21.2 - Creating New Streams
;;;     The ZK system uses "make-broadcast-stream",
;;;     "with-input-from-string"
;;;     and "with-output-to-string".

(cl:import '(cl:make-broadcast-stream cl:with-input-from-string
                                      cl:with-output-to-string))

;;; Section 21.3 - Operations on Streams
;;;     The ZK system uses "streamp", "input-stream-p",
;;;     "output-stream-p", and "stream-element-type".

(cl:import '(cl:streamp cl:input-stream-p cl:output-stream-p
                        cl:stream-element-type))


;;; --------------------------------------


;;; =====================================================================
;;;
;;; Chapter 22 - Input/Output
;;;
;;; =====================================================================


;;; Section 22.1 - Printed Representation of LISP Objects

;;; Subsection 22.1.2 - Parsing of Numbers and Symbols
;;;     The ZK system does not change the value of *read-base*
;;;     and assumes that it always has the value of 10.

;;; Subsection 22.1.3 - Macro Characters
;;;     The ZK system uses the following macro characters:
;;;        ( and ) (parentheses)
;;;        . (dot)
;;;        ' (single-quote)
;;;        ; (semicolon)
;;;        " (double-quote)
;;;        ` (backquote)
;;;        , (comma)
;;;        @ (at-sign)

;;; Subsection 22.1.4 - Standard Dispatching Macro Character Syntax
;;;     The ZK system uses the following standard # macros:
;;;        #\ for character objects
;;;        #' function abbreviation
;;;        #+ read-time conditional
;;;        #- read-time conditional
;;;        #| |# balanced comment


;;; Subsection 22.1.5 - The Readtable
;;;     The ZK system uses the following symbols:
;;;     "*readtable*", "copy-readtable", "set-syntax-from-char",
;;;     "set-macro-character", and "set-dispatch-macro-character".

(cl:import '(cl:*readtable* cl:copy-readtable cl:set-syntax-from-char
                            cl:set-macro-character
                            cl:set-dispatch-macro-character))


;;; Section 22.2 - Input Functions

;;; Subsection 22.2.1 - Input from Character Streams
;;;     The ZK system uses "read", "read-line", "read-char",
;;;     "unread-char", "peek-char", "read-from-string",
;;;     and "parse-integer".

(cl:import '(cl:read cl:read-line cl:read-char cl:unread-char
                     cl:peek-char cl:read-from-string cl:parse-integer))

;;; Subsection 22.2.2 - Input from Binary Streams
;;;     The ZK system uses "read-byte".

(cl:import '(cl:read-byte))

;;; Section 22.3 - Output Functions

;;; Subsection 22.3.1 - Output to Character Streams
;;;     The ZK system uses "prin1", "print", "princ", "prin1-to-string",
;;;     "princ-to-string", "write-char", "write-string", "terpri",
;;;     and "force-output".

(cl:import '(cl:prin1 cl:print cl:princ cl:prin1-to-string
                      cl:princ-to-string cl:write-char
                      cl:write-string cl:terpri cl:force-output))

;;; Subsection 22.3.2 - Output to Binary Streams
;;;     The ZK system uses "write-byte".

(cl:import '(cl:write-byte))

;;; Subsection 22.3.3 - Formatted Output to Character Streams
;;;     The ZK system uses "format" with the following directives:
;;;       ~A, ~S, ~D with mincol and padchar, and ~%.

(cl:import '(cl:format))

;;; Section 22.4 - Querying the User
;;;     The ZK system uses "y-or-n-p" and "yes-or-no-p".

(cl:import '(cl:y-or-n-p cl:yes-or-no-p))


;;; =====================================================================
;;;
;;; Chapter 23 - File System Interface
;;;
;;; =====================================================================


;;; Section 23.1 - File Names

;;; Subsection 23.1.2 - Pathname Functions
;;;     The ZK system uses "pathname", "truename", "merge-pathnames",
;;;     "make-pathname", "pathnamep", "pathname-directory",
;;;     "pathname-name", "pathname-type", "namestring",
;;;     "*default-pathname-defaults".

(cl:import '(cl:pathname cl:pathnamep cl:truename cl:pathname-directory
                         cl:pathname-name cl:pathname-type
                         cl:namestring cl:merge-pathnames
                         cl:make-pathname cl:*default-pathname-defaults*))

;;; Section 23.2 - Opening and Closing Files
;;;     The ZK system uses "with-open-file".

;;; We define our own "safe" file operations that don't crash.
;;; They use the ignore-errors macro defined or imported below.

(cl:import '(cl:ignore-errors))

;;; Macro for opening files without errors. If successful, returns a stream,
;;; nil otherwise.

(cl:defmacro safe-open (file cl:&rest args)
  `(cl:ignore-errors (cl:open ,file . ,args)))

;;; with-open-file macro that uses safe-open.

(cl:defmacro with-open-file ((stream . filespec) . body)
  `(cl:let ((,stream (safe-open ,@filespec)))
     (cl:unwind-protect (cl:progn ,@body)
       (cl:when ,stream (cl:close ,stream)))))

;;; Section 23.3 - Renaming, Deleting, and Other File Operations
;;;     The ZK system uses "rename-file", "delete-file", and
;;;     "probe-file".

;;; We define "safe versions of these functions.

(cl:defmacro rename-file (old new)
  `(cl:ignore-errors
    (cl:rename-file ,old ,new)))

(cl:defmacro delete-file (file)
  `(cl:ignore-errors (cl:delete-file ,file)))

(cl:defmacro probe-file (file)
  `(cl:ignore-errors (cl:probe-file ,file)))

;;; Section 23.4 - Loading Files
;;;     The ZK system uses "load".

(cl:import '(cl:load))


;;; Section 23.5 - Accessing Directories
;;;     The ZK system uses "directory".

(cl:defmacro directory (pathname)
  `(cl:ignore-errors (cl:directory ,pathname)))


;;; =====================================================================
;;;
;;; Chapter 24 - Errors
;;;
;;; =====================================================================


;;; Section 24.1 - General Error-Signalling Functions
;;;     The ZK system uses "error".

(cl:import '(cl:error))


;;; =====================================================================
;;;
;;; Chapter 25 - Miscellaneous Features
;;;
;;; =====================================================================


;;; Section 25.1 The Compiler
;;;     The ZK system uses "compile" and "compile-file".

(cl:import '(cl:compile cl:compile-file))


;;; Section 25.3 - Debugging Tools
;;;     The ZK system uses "time" and "room".

(cl:import '(cl:time cl:room))


;;; Section 25.4 - Environment Inquiries

;;; Subsection 25.4.1 - Time Functions
;;;     The ZK system uses "get-decoded-time",
;;;     "internal-time-units-per-second", "get-internal-run-time"
;;;     and "get-internal-real-time".

(cl:import '(cl:get-decoded-time cl:internal-time-units-per-second
                                 cl:get-internal-run-time
                                 cl:get-internal-real-time))

;;; Subsection 25.4.2 - Other Environment Inquiries
;;;     The ZK system uses "lisp-implementation-type",
;;;     "machine-type", "machine-instance" and "*features*".

(cl:import '(cl:lisp-implementation-type cl:machine-type
                                         cl:machine-instance
                                         cl:*features*))

;;; --------------------------------------



;;; =====================================================================
;;;
;;; Chapter 27 - Pretty Printing
;;;
;;; =====================================================================


;;; We use the pretty-printing feature of ANSI Common Lisp.

(cl:import '(cl:*print-pretty* cl:*print-pprint-dispatch*
             cl:*print-right-margin*
             cl:*print-miser-width* cl:*print-lines*))

(cl:import '(cl:pprint-newline cl:pprint-logical-block
             cl:pprint-exit-if-list-exhausted cl:pprint-pop
             cl:pprint-indent cl:pprint-tab cl:pprint-fill
             cl:pprint-linear cl:pprint-tabular))


;;; =====================================================================
;;;
;;; Chapter 29 - Conditions
;;;
;;; =====================================================================


;;; We use handler-case.

(cl:import '(cl:handler-case))


;;; =====================================================================
;;;
;;; Appendix
;;;
;;; =====================================================================


;;; ========================= The rationals. ============================

;;; Although ratios are built-in for ANSI Common Lisp, we thought that it
;;; would be a good idea to have cover functions to make oue code better
;;; in terms of self-documentation (it is clear where operations are
;;; rational rather than integer operations).


;;; ========================= rational predicates =======================

(defsubst rational-plusp (r) (cl:plusp r))

(defsubst rational-minusp (r) (cl:minusp r))

(defsubst rational-zerop (r) (cl:zerop r))

;;; ====================== unary rational operations ====================

(defsubst rational-minus (r) (cl:- r))

(defsubst rational-abs (r) (cl:abs r))

;;; ====================== binary rational operations ===================

(defsubst rdiv (r1 r2) (cl:/ r1 r2))

(defsubst rational-+ (r1 r2) (cl:+ r1 r2))

(defsubst rational-- (r1 r2) (cl:- r1 r2))

(defsubst rational-* (r1 r2) (cl:* r1 r2))

;;; ========================= rational relations ========================

(defsubst rational-= (r1 r2) (cl:= r1 r2))

(defsubst rational->= (r1 r2) (cl:>= r1 r2))

(defsubst rational-<= (r1 r2) (cl:<= r1 r2))

(defsubst rational-> (r1 r2) (cl:> r1 r2))

(defsubst rational-< (r1 r2) (cl:< r1 r2))


;;; =====================================================================
;;; 
;;;                         Additional Symbols
;;; 
;;; =====================================================================

;;; flatc returns the print length of object x without any
;;; escape characters.

(cl:defmacro flatc (object)
  `(cl:length (cl:princ-to-string ,object)))

;;; flatsize returns the print length of object x including
;;; escape characters.

(cl:defmacro flatsize (object)
  `(cl:length (cl:prin1-to-string ,object)))

;;; circular-list is a function that constructs a circular list
;;; from its arguments.

(cl:defun circular-list (cl:&rest elements)
  (cl:when elements
    (cl:setq elements (cl:copy-list elements))
    (cl:setf (cl:cdr (cl:last elements)) elements)
    elements))


;;; Macro to define a function which is stored on the property
;;; list(s) of the symbol(s) under indicator.

(cl:defmacro defpropfun ((symbols indicator) arglist cl:&body body)
  (cl:let ((function-name (cl:gensym)))
    `(cl:progn
       (cl:defun ,function-name ,arglist . ,body)
       (cl:mapc #'(cl:lambda (x)
                    (cl:setf (cl:get x ',indicator)
                             (cl:symbol-function ',function-name)))
                (cl:if (cl:listp ',symbols) ',symbols (cl:list ',symbols)))
       (cl:list ',symbols ',indicator))))

;;; Arbitrary Comparison of s-expressions according to some total
;;; ordering (essentially, an alphabetic ordering).

(cl:defun alphalessp (x y)
  (cl:cond ((cl:numberp x) (cl:or (cl:not (cl:numberp y)) (cl:< x y)))
           ((cl:numberp y) cl:nil)
           ((cl:or (cl:symbolp x) (cl:stringp x))
            (cl:or (cl:not (cl:or (cl:symbolp y) (cl:stringp y)))
                   (cl:string-lessp x y)))
           ((cl:or (cl:symbolp y) (cl:stringp y)) cl:nil)
           ((cl:atom x)
            (cl:or (cl:not (cl:atom y))
                   (cl:string-lessp (cl:format cl:nil "~S" x)
                                    (cl:format cl:nil "~S" y))))
           ((cl:atom y) cl:nil)
           (cl:t (cl:do ((x1 x (cl:cdr x1)) (y1 y (cl:cdr y1)))
                        (cl:nil)
                   (cl:cond ((cl:null y1) (cl:return cl:nil))
                            ((cl:null x1) (cl:return cl:t))
                            ((cl:or (cl:atom y1) (cl:atom x1))
                             (cl:return (alphalessp x1 y1)))
                            ((alphalessp (cl:car x1) (cl:car y1))
                             (cl:return cl:t))
                            ((alphalessp (cl:car y1) (cl:car x1))
                             (cl:return cl:nil)))))))


;;; ===================== Handling of aborts. ===========================

;;; Aborts here are user keyboard interrupts (e.g. using control-c).
;;; There are two functionalities provided:
;;;   - Temporarily disable (really defer) aborts.
;;;   - Catch aborts.


;;; CMUCL, SBCL, Clozure, GCL (ANSI version) and ECL have without-interrupts

#+CMU
(cl:defmacro with-abort-disabled (cl:&body body)
  `(system:without-interrupts . ,body))

#+SBCL
(cl:defmacro with-abort-disabled (cl:&body body)
  `(sb-sys:without-interrupts . ,body))

#+CCL
(cl:defmacro with-abort-disabled (cl:&body body)
  `(ccl:without-interrupts . ,body))

#+GCL
(cl:defmacro with-abort-disabled (cl:&body body)
  `(system::without-interrupts . ,body))

#+ECL
(cl:defmacro with-abort-disabled (cl:&body body)
  `(mp:without-interrupts . ,body))


;;; Macro for catching aborts.
;;; We establish system interrupt handlers that throw to 'abort.

#+CMU
(cl:defmacro catch-abort (cl:&body body)
  `(cl:catch 'abort
     (system:with-enabled-interrupts
         ((unix:SIGINT #'(cl:lambda (signal code scp)
                           (cl:declare (cl:ignore signal code scp))
                           (cl:throw 'abort cl:nil))))
       ,@body)))

#+SBCL
(cl:defmacro catch-abort (cl:&body body)
  `(cl:catch 'abort
     (cl:handler-bind
         ((sb-sys:interactive-interrupt #'(cl:lambda (signal)
                           (cl:declare (cl:ignore signal))
                           (cl:throw 'abort cl:nil))))
       ,@body)))

#+CCL
(cl:defmacro catch-abort (cl:&body body)
  `(cl:catch 'abort
     (cl:let
         ((ccl:*break-hook* #'(cl:lambda (condition hook)
                           (cl:declare (cl:ignore condition hook))
                           (cl:throw 'abort cl:nil))))
       ,@body)))

#+GCL
(cl:defmacro catch-abort (cl:&body body)
  `(cl:catch 'abort
     (cl:handler-bind
         ((cl:simple-error #'(cl:lambda (signal)
                           (cl:declare (cl:ignore signal))
                           (cl:throw 'abort cl:nil))))
       ,@body)))

#+ECL
(cl:defmacro catch-abort (cl:&body body)
  `(cl:catch 'abort
     (cl:handler-bind
         ((ext:interactive-interrupt #'(cl:lambda (signal)
                           (cl:declare (cl:ignore signal))
                           (cl:throw 'abort cl:nil))))
       ,@body)))


;;; A standard macro for the read and evaluate loop with prompting.

;;; We have catching of aborts, with input editing if any provided by
;;; the underlying system.  The read-form and eval-form use variables
;;; bound outside of read-and-evaluate to pass results between them.

(cl:defmacro read-and-evaluate (help-string prompt-string read-form eval-form)
  #+GCL `(catch-abort
           (cl:let ((si:*ignore-eof-on-terminal-io* t))
                (cl:terpri)
                ,help-string
                (cl:write-string ,prompt-string)
                (cl:finish-output)
                ,read-form
                ,eval-form))
  #-GCL
  `(catch-abort
     (cl:terpri)
     ,help-string
     (cl:write-string ,prompt-string)
     (cl:finish-output)
     ,read-form
     ,eval-form))
