
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
;;;                         Error Messages
;;; =====================================================================

(in-package "ZK")



;;; Well-formedness error.
(deferror apply-non-function (object)
  (list (list :string "The expression")
	(list :formula object)
	(list :string "being applied is not a function."))
  ((:string "Only declared function symbols can be applied
in an expression.")))

;;; Library error.
(deferror circular-dependency (object)
  (list
   '(:string "Circular dependency detected while adding library")
   '(:string "unit")
   (list ':event-name object)
   '(:punctuation "."))
  ((:string "There must not be any circular logical dependency among
library units.")))

;;; Library error.
(deferror declarations-inconsistent (object)
  (list
   '(:string "The declarations")
   (list :event-name-list object)
   '(:string "are inconsistent with their counterparts."))
  ((:string "Declarations to be made into a")
   (:event-name spec)
   (:string "or")
   (:event-name model)
   (:string "unit must be consistent with their corresponding
declarations, if they exist, in the corresponding")
   (:event-name model)
   (:string "or")
   (:event-name spec)
   (:string "unit in the library.")))

;;; Library error.
(deferror declarations-unimplemented (object)
  (list '(:string "The following declarations in the")
	(list ':event-name 'spec)
	'(:string "unit are not in the")
	(list ':event-name 'model)
	'(:string "unit:")
	(list :event-name-list (reverse object))
	'(:punctuation "."))
  ((:string "Each declaration in a")
   (:event-name spec)
   (:string "unit must have a corresponding declaration in the")
   (:event-name model)
   (:string "unit.")))

;;; Library error.
(deferror declarations-unproven (object)
  (list '(:string "The following declarations are unproven:")
	(list :event-name-list object)
	'(:punctuation "."))
  ((:string "A")
   (:event-name model)
   (:string "library unit cannot be made if there are any 
proof obligations that have not been discharged.")))

;;; General file error.
(deferror directory-does-not-exist (object)
  (list '(:string "The directory")
	(list :string (format nil "\"~A\"" object))
	'(:string "does not exist."))
  ((:string "An operation being performed expected the
specified directory to exist.")))

;;; Well-formedness error.
(deferror duplicate-instantiations (object)
  (list '(:string "The identifiers")
	(list :event-name-list object)
	'(:string "are duplicated in the instantiation list."))
  ((:string "All instantiated identifiers in an")
   (:command-name instantiate)
   (:punctuation ",")
   (:command-name assume)
   (:string "or")
   (:command-name add)
   (:string "command must be pairwise distinct.")))

;;; Well-formedness error.
(deferror duplicate-variables (object)
  (list '(:string "The variables in a variable list")
	'(:punctuation ",")
	(list :event-name-list object)
	'(:punctuation ",")
	'(:string "are not unique."))
  ((:string "The identifiers of a quantification identifier list, a
parameter list, or a ZF mapping identifier list must be pairwise distinct.")))

;;; Internal well-formedness error. Lisp level only.
(deferror event-not-symbol (object)
  (list (list :string (format nil "~A" object))
	(list :string "is not a symbol."))
  ((:string "Only symbols can be declared as events. This is a Lisp level
error since the ZK parser already catches this as a syntax error.")))

;;; General file error.
(deferror file-does-not-exist (object)
  (list '(:string "The file")
	(list :string (format nil "\"~A\"" object))
	'(:string "does not exist."))
  ((:string "An operation being performed expected the
specified file to exist.")))

;;; General file error.
(deferror file-error (info)
  (list '(:string "Cannot")
	(list ':string (car info))
	'(:string "the file")
	(list ':string (cdr info))
	'(:punctuation "."))
  ((:string "ZK cannot perform the specified action on the specified file.
Check that if a file is to be opened, it exists and is readable, and if a
file is to be created, that you have permission to create the file in the
directory.")))

;;; Library error or general file error?
(deferror file-not-compressed (object)
  (list '(:string "The file")
	(list :string (format nil "~A" object))
	'(:string "is not a compressed file."))
  ((:string "Certain types of files such as those for library units
must be in compressed form.")))

;;; Library error.
(deferror file-not-valid (object)
  (list '(:string "The library unit file")
	(list :string (format nil "~A" object))
	'(:string "is not valid."))
  ((:string "A file containing a library unit must have the same version
number as the current system.")))

;;; General file error.
(deferror filename-not-string (object)
  (list '(:string "File or directory name")
	(list :string (format nil "~S" object))
	'(:string "is not a string."))
  ((:string "The name of a file or directory must be a string.")))

;;; Extra well-formedness arror.
(deferror frule-invalid-conclusion (object)
  (list (list :string "The frule conclusion")
	(list :formula object)
	(list :string "is invalid."))
  ((:string "The conclusion of a frule must be either a literal or a
conjunction of literals (see")
   (:help-name frule)
   (:punctuation ")")
   (:punctuation ".")))

;;; Extra well-formedness error.
(deferror frule-invalid-condition (object)
  (list (list :string "The frule pattern")
	(list :formula object)
	(list :string "is invalid."))
  ((:string "The condition of a frule must be either a simple expression
or the negation of a simple expression (see")
   (:help-name frule)
   (:punctuation ")")
   (:punctuation ".")))

;;; Extra well-formedness error.
(deferror grule-false-condition (object)
  (list (list :string "The grule has an unsatisfiable condition."))
  ((:string "A grule that has an unsatisfiable condition
can never be applied.")))

;;; Extra well-formedness error.
(deferror grule-invalid-conclusion (object)
  (list (list :string "The grule conclusion")
	(list :formula object)
	(list :string "is invalid."))
  ((:string "The conclusion of a grule must be a literal (see")
   (:help-name grule)
   (:punctuation ")")
   (:punctuation ".")))

;; Extra well-formedness error.
(deferror grule-invalid-condition (object)
  (list (list :string "The condition")
	(list :formula object)
	(list :newline)
	(list :string "is invalid for a grule."))
  ((:string "The condition of a grule must be either a literal or a
conjunction of literals (see")
   (:help-name grule)
   (:punctuation ")")
   (:punctuation ".")))

;;; Internal well-formedness error. Lisp level specific.
(deferror instantiations-ill-formed (instantiations)
  (list '(:string "The instantiation list")
	(list :string (format nil "~A" instantiations))
	'(:string "is ill formed."))
  ((:string "At the Lisp level, an instantiation list must consist of a
list of equality expressions, with a variable on the left side of each
equality.")))

;;; Well-formedness error.
(deferror invalid-expression (object)
  (list (list :string
	      (cond ((characterp object)
		     (string-append "'" (string object) "'"))
		    ((stringp object)
		     (string-append "\"" object "\""))
		    (t
		     (format nil "~S" object))))
	'(:string "is not a valid expression."))
  ((:string "An expression must be one of symbol, integer,
function application or quantification.")))

;;; Well-formedness error.
(deferror invalid-free-variable-reference (object)
  (list '(:string "Identifier")
	(list :event-name object)
	'(:string "is an invalid reference to a free variable."))
  ((:string "In many situations, a free variable of an expression
must be contained in some set, e.g., the identifiers of the parameter
list of a function.")))

;;; Library error.
(deferror invalid-unit-type (object)
  (list '(:string "Library unit type")
	(list :string (format nil "~A" object))
	'(:string "is invalid."))
  ((:string "The type of a library unit must be")
   (:event-name spec)
   (:punctuation ",")
   (:event-name model)
   (:punctuation ",")
   (:string "or")
   (:event-name freeze)
   (:punctuation ".")))

;;; Library error.
(deferror library-does-not-exist (object)
  (list '(:string "The library")
	(list :string (format nil "~S" object))
	'(:string "does not exist."))
  ((:string "A library operation other than")
   (:command-name create)
   (:string "requires that the library exists.")))

;;; Library error.
(deferror library-not-set (object)
  (append
   '((:string "Library operation"))
   (when object (list '(:string "on") (list ':event-name object)))
   '((:string "cannot be performed; there is no current library.")))
  ((:string "Library operations may be performed only
when a library has been set.")))

;;; Well-formedness error.
(deferror name-not-declared (object)
  (list '(:string "The identifier")
	(list :event-name object)
	'(:string "is not declared."))
  ((:string "An identifier that is in a function position or is
expected to be a function or axiom name is not declared.")))

;;; Extra well-formedness error.
(deferror no-measure (object)
  (list (list :string "The recursive function")
	(list :event-name object)
	(list :string "has no measure."))
  ((:string "A recursive function must have a measure to prove its
termination.")))

;;; Well-formedness error.
(deferror not-a-formal (object)
  (list '(:string "The name")
	(list :event-name (first object))
	'(:string "is not a formal of")
	(list :event-name (second object))
	'(:punctuation "."))
  ((:string "A variable to be instantiated in a")
   (:command-name assume)
   (:string "or")
   (:command-name add)
   (:string "command must be in the formals list of the referred
axiom or function.")))

;;; Well-formedness error.
(deferror not-a-function-name (object)
  (list '(:string "The identifier")
	(list :event-name object)
	'(:string "is not a function name."))
  ((:string "The")
   (:command-name invoke)
   (:punctuation ",")
   (:command-name print-rules-about)
   (:string "and")
   (:command-name rules-about)
   (:string "commands expect that the specified identifier be the
name of a function.")))

;;; Well-formedness error.
(deferror not-a-function-or-axiom-name (object)
  (list '(:string "The identifier")
	(list :event-name object)
	'(:string "is not a function or axiom name."))
  ((:string "The")
   (:command-name assume)
   (:string "and")
   (:command-name add)
   (:string "commands expect that the specified identifier be the
name of a function or axiom.")))

;;; Well-formedness error.
(deferror not-a-rule-name (object)
  (list '(:string "The identifier")
	(list :event-name object)
	'(:string "is not a rewrite rule name."))
  ((:string "The")
   (:command-name applyf)
   (:string "command expects that the specified identifier be the
name of a rewrite rule.")))

;;; Internal well-formedness error. Lisp level only.
(deferror parameter-not-list (object)
  (list (list :string (format nil "~A" object))
	(list :string "occurred where a parameter list was expected."))
  ((:string "A parameter list must be a list of variables.")))

;;; Internal well-formedness error. Lisp level only.
(deferror parameter-not-variable (object)
  (list (list :string "The parameter")
	(if (symbolp object)
	    (list :formula object)
	    (list :string (format nil "~A" object)))
	(list :string "is not a variable."))
  ((:string "Each symbol appearing in a parameter list must be a variable.")))

;;; Extra well-formedness error.
(deferror pattern-connective (object)
  (list (list :string "The pattern")
	(list :formula object)
	(list :string "contains an IF or a logical connective."))
  ((:string "A rule pattern may not contain an IF expression
or a logical connective.  See")
   (:help-name pattern-matching)
   (:string "for additional information.")))

;;; Extra well-formedness error.
(deferror pattern-not-function-application (object)
  (list (list :string "The pattern")
	(list :formula object)
	(list :string "is not a function application."))
  ((:string "A rule pattern must be a function application.  See")
   (:help-name pattern-matching)
   (:string "for additional information.")))

;;; Extra well-formedness error.
(deferror pattern-quantifier (object)
  (list (list :string "The pattern")
	(list :formula object)
	(list :string "contains a quantifier."))
  ((:string "A rule pattern may not contain a quantifier.  See")
   (:help-name pattern-matching)
   (:string "
for additional information.")))

;;; Internal well-formedness error. Lisp level only.
(deferror quantification-syntax (object)
  (list (list :string "Syntax error for quantification:")
	(list :formula object))
  ((:string "Quantification syntax is (ALL (v ...) expr) or
(SOME (v ...) expr).")))

;;; Well-formedness error.
(deferror redeclaration (object)
  (list (list :event-name object)
	'(:string "has already been declared."))
  ((:string "An identifier introduced by the declaration already exists
in the vocabulary.")))

;;; Extra well-formedness warning.
(deferror rule-condition-loops (object)
  (list (list :string "The rule")
	(list :event-name object)
	(list :string "applies to its own condition."))
  ((:string "A rewrite rule that applies to its own condition may cause the
prover to loop.")))

;;; Extra well-formedness error.
(deferror rule-false-condition  (object)
  (list (list :string "The rule")
	(list :event-name object)
	(list :string "has an unsatisfiable condition."))
  ((:string "A rewrite rule that has an unsatisfiable condition can never be
applied.")))

;;; Extra well-formedness error.
(deferror rule-invalid-conclusion (object)
  (list (list :string "The rewrite rule conclusion,")
	(list :formula object)
	(list :punctuation ",")
	(list :string "is invalid."))
  ((:string "The conclusion of a rewrite rule must be an equality.")))

;;; Extra well-formedness error.
(deferror rule-loops (object)
  (list (list :string "The rule")
	(list :event-name object)
	(list :string "loops upon itself."))
  ((:string "A rewrite rule that loops may cause the prover to run
indefinitely.")))

;;; Extra well-formedness warning.
(deferror rule-not-reducing (object)
  (list (list :string "The rule")
	(list :event-name object)
	(list :string "is not reducing according to the simplification
ordering."))
  ((:string "A rewrite rule that does not reduce according to the
simplification ordering may cause indefinite rewriting (bounded by
the reducer's depth limit).")))

;;; Internal well-formedness error. Lisp level only.
(deferror symbol-declared (object)
  (list (list :string "The symbol")
	(list :event-name object)
	(list :string "has already been declared."))
  ((:string "A variable symbol in an expression must not be a declared
symbol.")))

;;; Internal well-formedness error. Lisp level only.
(deferror symbol-undeclared (object)
  (list (list :string "The symbol")
	(list :event-name object)
	(list :string "has not been declared."))
  ((:string "All function symbols in an expression must be declared.")))

;;; Library error.
(deferror unit-does-not-exist (object)
  (list '(:string "The")
	(list ':formula (second object))
	'(:string "unit")
	(list ':formula (first object))
	'(:string "does not exist in the library."))
  ((:string "For operations on library units other than the")
   (:command-name make)
   (:string "operation, the unit must already exist.")))

;;; Library error.
(deferror unit-exists (object)
  (list '(:string "The")
	(list ':formula (second object))
	'(:string "unit")
	(list ':formula (first object))
	'(:string "already exists in the library."))
  ((:string "You cannot make a library unit that already exists.")))

;;; Library error.
(deferror unit-name-not-symbol (object)
  (list (list :string (format nil "~A" object))
	(list :string "is not a symbol."))
  ((:string "The name of a library unit must be a symbol.")))

;;; Library error.
(deferror units-loaded (object)
  (list '(:string "The following specification")
	'(:string "units to be deleted are currently loaded:")
	(list :event-name-list object)
	'(:punctuation "."))
  ((:string "Library units currently loaded cannot be deleted.")))

;;; Well-formedness warning.
(deferror variable-already-used (object)
  (list '(:string "The identifier")
	(list :event-name object)
	'(:string "has already been used."))
  ((:string "It may be confusing to have nested bindings of the
same variable.")))

;;; Extra well-formedness error.
(deferror variable-capture (object)
  (list (list :string "The variable")
	(list :formula object)
	(list :string "is captured by a quantifier."))
  ((:string "Nested quantification over the same variable is
not allowed in a declaration.  In addition, quantification over
a variable that is a parameter is disallowed.")))

;;; Internal well-formedness error. Lisp level only.
(deferror variable-free (object)
  (list (list :string "Free variables")
	(list :formula-list object)
	(list :string "are not parameters."))
  ((:string "A variable occurring free in the body of a declaration
must be a parameter of the declaration.")))

;;; Extra well-formedness error.
(deferror variable-unbound (object)
  (list (list :string "Variables")
	(list :formula-list object)
	(list :string "are not bound by the pattern or subgoal."))
  ((:string "For")
   (:event-name rule)
   (:punctuation "s")
   (:string "there must be an occurrence of each
variable in the pattern or in the subgoal.  For")
   (:event-name grule)
   (:punctuation "s")
   (:string "there must be an occurrence of each variable in the
trigger or in the subgoal.")))

;;; Well-formedness warning.
(deferror variables-unused (object)
  (list '(:string "The following")
	(list :string (first object))
	'(:string "were not used:")
	(list :event-name-list (second object)))
  ((:string "It is not an error to declare formals or bind variables and
then not refer to them, but this is sometimes a symptom of
a problem.")))

;;; Well-formedness error.
(deferror wrong-number-of-arguments (object)
  (list '(:string "In")
	(list :formula object)
	'(:string "function")
	(list :event-name (car object))
	'(:string "is applied to the wrong number of arguments."))
  ((:string "A function must be applied to the correct number of arguments.")))
