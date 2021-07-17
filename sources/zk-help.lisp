
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



(defparameter *zk-help-topic-list*
    '(introduction
		 
      (overview
       design-philosophy
       theory-development
       prover-capabilities)

      ;; ZK dependent
		 
      (declarations
       (functions function-stub function zf-function)
       (axioms axiom rule frule grule)
       library-units
       proof-obligation
       )
		 
      (current-formula try print-formula)
		 
      (proof-steps
		   
       (simplification
	simplify
	trivial-simplify)
		   
       (rewriting
	rewrite
	trivial-rewrite)
		   
       (reduction
	reduce
	trivial-reduce)

       pattern-matching
       subgoaling
		   
       (using-definitions add apply invoke use)
		   
       (equality equality-substitute label)
		   
       (rearranging contradict rearrange split suppose delete-hypotheses)

       (cases-mechanism cases next)
		   
       (normal-forms conjunctive disjunctive)
		   
       (quantifiers prenex instantiate)
		   
       (induction induct)
		   
       (macro-steps
	prove
	prove-by-cases
	prove-by-induction
	prove-by-rearrange))
	

      (libraries load make edit delete
       print-library-status
       set-library)
		 
      (undoing back back-thru back-to retry
       undo undo-back-thru undo-back-to reset)
		 
      (printing
       help
       print-declaration
       print-recent-declarations
       print-proof
       print-proof-summary
       print-rules-about
       print-working-directory
       rules-about
       print-status
       print-history)

      (proof-logging
       check-all-proofs check-proof dump-log log-on log-off)

      (proof-browsing
       browse-begin browse-forward browse-back rebrowse browse-down browse-up
       browse-print-formula)

      (miscellaneous
       script
       end-script
       clear-stats
       print-stats
       set-working-directory
       read)

      (command-modifiers
       with-subexpression
       with-instantiation
       without-instantiation
       with-case-analysis
       without-case-analysis
       with-normalization
       without-normalization
       (enable-disable
	disabled
	with-enabled
	with-disabled))
		

      syntax
		 
      initial-theory
		 
      (error-codes
       apply-non-function               ;whcheck
       circular-dependency		;library
       declarations-inconsistent	;library
       declarations-unimplemented	;library
       declarations-unproven		;library
       directory-does-not-exist         ;general
       duplicate-instantiations		;wfcheck
       duplicate-variables              ;wfcheck
       file-does-not-exist		;library
       file-error                       ;general
       file-not-compressed		;library
       file-not-valid			;library
       filename-not-string		;library
       frule-invalid-conclusion         ;extra wfcheck
       frule-invalid-condition          ;extra wfcheck
       grule-false-condition            ;extra wfcheck
       grule-invalid-conclusion         ;extra wfcheck
       grule-invalid-condition          ;extra wfcheck
       invalid-expression               ;wfcheck
       invalid-free-variable-reference  ;wfcheck
       invalid-unit-type		;library
       library-does-not-exist		;library
       library-not-set			;library
       name-not-declared		;wfcheck
       no-measure                       ;extra wfcheck
       not-a-formal			;wfcheck
       not-a-function-name		;wfcheck
       not-a-function-or-axiom-name	;wfcheck
       not-a-rule-name			;wfcheck
       pattern-connective               ;extra wfcheck
       pattern-not-function-application ;extra wfcheck
       pattern-quantifier               ;extra wfcheck
       redeclaration			;wfcheck
       rule-condition-loops             ;extra wfcheck
       rule-false-condition             ;extra wfcheck
       rule-invalid-conclusion          ;extra wfcheck
       rule-loops                       ;extra wfcheck
       rule-not-reducing                ;extra wfcheck
       unit-does-not-exist		;library
       unit-exists			;library
       unit-name-not-symbol             ;library
       units-loaded			;library
       variable-already-used		;wfcheck
       variable-capture                 ;extra wfcheck
       variable-unbound                 ;extra wfcheck
       variables-unused			;wfcheck
       wrong-number-of-arguments        ;wfcheck

       )
		 
      bibliography
      ))


;;; Create a new help explanation, by replacing specified elements in an
;;; existing explanation.  The second argument is a list of items of the
;;; following forms:
;;; (directive [data])		replace the matching directive
;;; (directive :delete)		delete the matching directive
;;; (directive :copy)		copy the matching directive
;;; Steps through the explain, stepping the replacements list when a match
;;; is found.

(eval-when (:compile-toplevel :load-toplevel)
(defun replace-help (explain replacements)
  (cond
   ((null explain)
    (when replacements
      (error "no match found for replacement help ~S" (car replacements)))
    nil)
   ((null replacements)
    explain)
   ((eq (caar explain) (caar replacements))
    (cond
     ((eq (cadar replacements) :delete)
      (replace-help (cdr explain) (cdr replacements)))
     ((eq (cadar replacements) :copy)
      (cons (car explain) (replace-help (cdr explain) (cdr replacements))))
     (t
      (cons (car replacements)
	    (replace-help (cdr explain) (cdr replacements))))))
   (t
    (cons (car explain) (replace-help (cdr explain) replacements)))))
)

;;; Define help for the ZK help alist. If type is modify, create the
;;; explanation by modifying the existing Lisp mode help. In this case,
;;; the help is found by looking for the corresponding Lisp mode name,
;;; as specified by *command-name-translations*.

;;; NOTE: All forms in the help are converted to Lisp mode syntax on
;;; output. This works OK for reusing help, but you must ensure that,
;;; if the forms are already in ZK syntax, the conversion won't damage
;;; them. Don't have a Lisp mode command argument which is a list that
;;; starts with QUOTE; the conversion will treat it as a quoted list
;;; and strip it.  Quantifications in ZK syntax are OK.

(defmacro defzkhelp (symbol type explain)
  (if (eq type 'modify)
      (let* ((sym (or (cdr (assoc-eq symbol *command-name-translations*))
		      symbol))
	     (help (assoc-eq sym *lisp-mode-help-alist*)))
	(unless help
	  (error "No help for ~A to be modified" symbol))
	`(defhelp ,symbol ,(second help)
	   ,(replace-help (third help) explain)
	   *zk-help-alist*))
    `(defhelp ,symbol ,type ,explain *zk-help-alist*)))

;;; Arrange for ZK help to be available when body is executed.

(defmacro with-zk-help (&body body)
  `(let ((*help-topic-list* *zk-help-topic-list*)
	 (*help-alists* (list *zk-help-alist* *lisp-mode-help-alist*)))
     ,@body))

;;; Introduction and Overview

(defzkhelp introduction extra-help
  ((:newline)
   (:string "This is on-line documentation for Release")
   (:string (:eval *zk-version*))
   (:string "of the ZK theorem proving system.
The notation used by the ZK system is Verdi minus its
executable features. Verdi is described in
'Reference Manual for the Language Verdi' (see")
   (:help-name bibliography)
   (:punctuation ")")
   (:punctuation ".")))

(defzkhelp overview extra-help
  ((:newline)
   (:string "ZK supports the incremental development of theories.
You may develop a theory in ZK by introducing ZK
declarations and discharging their proof obligations.
To help you discharge the proof obligations, the system provides
you with various proof commands ranging from those that perform very
simple steps to the")
   (:command-name reduce)
   (:string "command that uses the entire automatic capabilities of
the theorem prover.")
   (:paragraph)
   (:string "In addition to introducing declarations and performing proof
steps, you may perform other operations such as loading
saved library units, undoing declarations and proof steps, performing
queries on the state of the curent development, and saving the contents
of the current development as a library unit.")
   (:paragraph)
   (:string "You may perform any of the above using a ZK command
line interface or using an editor that has a ZK mode.")))

(defzkhelp design-philosophy extra-help
  ((:newline)
   (:string "ZK is intended to be used for the development of mathematical
theories. The ZK theorem prover is neither fully automatic nor
entirely manual. In general, you must
guide the system towards proofs by supplying heuristics and performing
proof steps. However, the theorem prover provides you
with some powerful commands (the reduction commands), which incorporate
decision procedures for equality and integer reasoning. The most powerful
of these is the")
   (:command-name reduce)
   (:string "command, which uses heuristics to replace function
applications with appropriate instances of the functions' definitions,
as well as apply rewrite rules, assumption rules, and forward rules.")))

(defzkhelp theory-development extra-help
  ((:newline)
   (:string "ZK supports theory development by maintaining a database
containing information about symbols and axioms. Some of these symbols
and axioms are predefined while others are added using declarations
directly or through loaded library units. Library units (see")
   (:help-name libraries)
   (:punctuation ")")
   (:string "are proved separately and may
be loaded even if they have not been proved - ZK supports modularization
and allows top-down, bottom-up, and mixed strategies of development.")
   (:paragraph)
   (:string "Typically, you would be developing a library unit that
is either a")
   (:command-name spec)
   (:string "or a")
   (:command-name model)
   (:punctuation ".")
   (:string "A")
   (:command-name model)
   (:string "unit is not allowed to contain a")
   (:command-name function-stub)
   (:string "declaration and all proof obligations in it must be
discharged. In contrast, there are no restrictions on a")
   (:command-name spec)
   (:string "unit and proof obligations and proofs in it are discarded.")
   (:paragraph)
   (:string "During a development, you are unrestricted from
entering declarations that would not be allowed in a")
   (:command-name model)
   (:string "unit, as the system does not have modes for developing the
different kinds of units. Only when you try to make a library unit does
the system check to make sure that the restrictions are met. Additional
checks are performed by the system to ensure that the a")
   (:command-name model)
   (:string "unit is in fact a model for the corresponding")
   (:command-name spec)
   (:string "unit.")))

(defzkhelp prover-capabilities extra-help
  ((:newline)
   (:string "The theorem prover operates by applying its capabilities to
transform the current formula to a new formula. A proof is simply
a sequence of transformations to")
   (:formula (TRUE))
   (:punctuation ".")
   (:string "For each proof step, the resulting formula is logically
equivalent to the original formula, modulo the \"current theory\".")
   (:paragraph)
   (:string "The simplifier (invoked using the")
   (:command-name simplify)
   (:string "command) recognizes propositional tautologies and
fallacies. In addition, it can find elementary proofs involving integers,
equalities, and instantiations of quantified variables, although it
does not try very hard to find instantiations. It can also
be \"programmed\" using assumption rules and forward rules, to create
decision procedures or near decision procedures for various theories.
When a simplification does not result in a proof or refutation, it can
produce a formula that is more elementary (according to the simplifier's
measure) than the original.")
   (:paragraph)
   (:string "The rewriter (invoked using the")
   (:command-name rewrite)
   (:string "command) performs all the things that the simplifier
does plus it applies rewrite rules, replacing instances of a rewrite
rule pattern with the corresponding instances of the replacing
expression of the rewrite rule. A rewrite rule may be conditional,
in which case the condition for the rewrite rule must be shown to
hold before the rule is applied.")
   (:paragraph)
   (:string "The reducer (invoked using the")
   (:command-name reduce)
   (:string "command) performs everything that the rewriter does plus
it replaces function applications with appropriate instances
of the functions' definitions, using heuristics to deal with
recursive functions.")
   (:paragraph)
   (:string "The simplifier, rewriter and reducer can be controlled
further by enabling/disabling automatic use of rules and function
definitions. (see")
   (:help-name enable-disable)
   (:punctuation ")")
   (:punctuation ".")
   (:paragraph)
   (:string "In addition to the above three commands, there are various
commands available to perform simpler proof steps. For example, the")
   (:command-name invoke)
   (:string "command can be used to manually replace function
applications with appropriate instances of the functions' definitions.
Mathematical induction with various degrees of automation can be
performed using the")
   (:command-name induct)
   (:string "comand.")
   (:paragraph)
   (:string "You may focus on parts of the conjecture that you
are trying to prove using the")
   (:command-name cases)
   (:string "and")
   (:help-name subexpression)
   (:string "mechanisms of the theorem prover. Variations on prover
commands are provided by command modifiers.")
   (:paragraph)
   (:string "Finally, more sophisticated capabilities are provided by the
macro proof steps (see")
   (:help-name macro-steps)
   (:punctuation ")")
   (:punctuation ",")
   (:string "which may perform a combination of above proof steps.")))



;;; Declarations

(defzkhelp declarations extra-help
  ((:newline)
   (:string "Symbols may be introduced into a theory development through
various types of declarations directly or through the LOAD command.
A declaration extends the current theory by the addition of one or
more symbols and, in most cases, some axioms. Some of the declarations
include explicit heuristics for the theorem prover.")
   (:paragraph)
   (:string "You may undo declarations and LOAD commands in a
last-in-first-out basis (see")
   (:help-name undoing)
   (:punctuation ")")
   (:punctuation ".")
   (:string "You also may print declarations (see") (:help-name printing)
   (:punctuation ").")))

;;; Functions

(defzkhelp functions extra-help
  ((:newline)
   (:string "There are three kinds of function declarations in ZK:")
   (:command-name function-stub)
   (:punctuation ",")
   (:command-name function)
   (:string "and")
   (:command-name zf-function)
   (:string "declarations.")))

(defzkhelp function-stub prover-command
  ((:syntax (function-stub |restricted_identifier| (|parameter_list|)))
   (:newline) (:newline)
   (:string "Declare a function without a defining body.
The syntax for parameter_list is:")
   (:newline) (:newline)
   (:syntax |identifier*|)
   (:newline) (:newline)
   (:string "If you declare a function using")
   (:command-name function-stub)
   (:string "then you cannot make the current development into a")
   (:command-name model)
   (:punctuation ".")))

(defzkhelp function prover-command
  ((:syntax (function |restricted_identifier| (|parameter_list|)
		      (|[measure]|) |expression|))
   (:newline) (:newline)
   (:string "Declare a function with a defining body, where
parameter_list is:")
   (:newline) (:newline)
   (:syntax |identifier*|)
   (:newline) (:newline)
   (:string "and measure is")
   (:newline) (:newline)
   (:syntax (measure |expression|))
   (:newline) (:newline)
   (:string "If the function is recursive then the measure expression
is mandatory and defines a measure function. Application of the measure
function to expressions at the parameter positions of a recursive call
must produce a value that is smaller according to M< than application
of the measure function to the parameters of the function.")))

(defzkhelp zf-function prover-command
  ((:syntax (zf-function |restricted_identifier|
			 (|parameter_list|) |ZF_body|))
   (:newline) (:newline)
   (:string "Declare a function indirectly using MAP, SELECT or THAT.
Correspondingly, the ZF_body must be one of:")
   (:newline) (:newline)
   (:syntax (map |expression| |{((identifier+) expression)}+|))
   (:newline) (:newline)
   (:syntax (select (|identifier| |expression|) |expression|))
   (:newline) (:newline)
   (:syntax (that |identifier| |expression|))
   (:newline) (:newline)
   (:string "A")
   (:help-name map)
   (:string "or")
   (:help-name select)
   (:string "lets you define a function as a set constructor, while a")
   (:help-name that)
   (:string "lets you specify a function by its properties. If you declare a")
   (:command-name zf-function)
   (:string "with a")
   (:help-name that)
   (:punctuation ",")
   (:string "there would be a proof obligation that must be discharged
to show that the definition does in fact define a function.")))



;;; Axioms

(defzkhelp axioms extra-help
  ((:newline)
   (:string "In ZK, lemmas and theorems are called axioms. There are
four types of axiom declarations in ZK each having different theorem prover
heuristics:")
   (:newline)
   (:string "-")
   (:command-name axiom)
   (:string "declares an axiom with no theorem prover heuristics,")
   (:newline)
   (:string "-")
   (:command-name rule)
   (:string "declares a rewrite rule,")
   (:newline)
   (:string "-")
   (:command-name frule)
   (:string "declares a forward rule,")
   (:newline)
   (:string "-")
   (:command-name grule)
   (:string "declares an assumption rule.")
   (:paragraph)
   (:string "All four types of axioms may be used
manually during a subsequent proof and the latter three may also be
used by the theorem prover automatically.")))

(defzkhelp axiom prover-command
  ((:syntax (axiom |restricted_identifier|
		   (|parameter_list|) |expression|))
   (:newline) (:newline)
   (:string "Declare an axiom without any theorem prover heuristics,
where parameter_list is:")
   (:newline) (:newline) (:syntax |identifier*|)
   (:newline) (:newline)
   (:string "You may manually bring in the axiom as an assumption
in a subsequent proof using the")
   (:command-name use)
   (:string "command.")
   (:paragraph)
   (:string "If you declare an axiom then you ought to prove it,
unless you are in the process of developing a")
   (:command-name spec)
   (:punctuation ".")
   (:string "The proof obligation is simply the defining
expression.")))

(defzkhelp rule prover-command
  ((:syntax (rule |restricted_identifier|
		  (|parameter_list|) |expression|))
   (:newline) (:newline)
   (:string "Declare an axiom which is to be used as a rewrite rule,
where parameter_list is:")
   (:newline) (:newline) (:syntax |identifier*|)
   (:newline) (:newline)
   (:string "The")
   (:formula |expression|)
   (:string "part must be an equality if the rule is unconditional
or an implication with an equality as a conclusion if the rule is
conditional. In both cases, the left hand side of the equality is
the rule's pattern while the right hand side of the equality is the
rule's replacing expression. For a conditional rule, the hypothesis
part of the implication is the rule's condition.")
   (:paragraph)
   (:string "There are restrictions on the form of a pattern.
First, a pattern must be a function application. Second, quantifiers,")
   (:event-name if)
   (:string "expressions and logical connectives are disallowed
in a pattern.")
   (:paragraph)
   (:string "Rewrite rules are replacement rules that are applied
during rewriting. When a subexpression being rewritten matches a
rewrite rule's pattern then the rewriter replaces the subexpression
with an appropriate instance of the rule's replacing expression. A
conditional rewrite rule is applied only if the theorem prover can
prove the condition.")
   (:paragraph)
   (:string "You may manually apply a rewrite rule in a proof
using the")
   (:command-name apply)
   (:string "command. You also may bring in a rewrite rule as an
assumption in a proof using the")
   (:command-name use)
   (:string "command.")
   (:paragraph)
   (:string "If you declare a rewrite rule then you ought to
prove it, unless you are in the process of developing a")
   (:command-name spec) (:punctuation ".")
   (:string "The proof obligation is simply the defining
expression.")))

(defzkhelp frule prover-command
  ((:syntax (frule |restricted_identifier| (|parameter_list|)
		   |expression|))
   (:newline) (:newline)
   (:string "Declare an axiom that is to be used as a forward rule,
where parameter_list is:")
   (:newline) (:newline) (:syntax |identifier*|)
   (:newline) (:newline)
   (:string "The")
   (:formula |expression|)
   (:string "part must be an implication with a condition that is either a
simple pattern or a logical negation of a simple pattern, where a simple
pattern is defined to be a function other than")
   (:event-name if)
   (:string "or the boolean connectives applied to zero or more
non-repeated variables. The conclusion must be a literal or a conjunction
of literals, where a literal is a quantifier-free expression that does
not contain an")
   (:event-name if)
   (:string "or any boolean connectives except a possible logical
negation at the outermost level. Each parameter must occur in the
condition.")
   (:paragraph)
   (:string "A frule is an axiom whose conclusion instance is
asserted in a particular context during simplification when the
corresponding condition instance is known to be (TRUE) in that context.
By being asserted, the conclusion instance is available as an
assumption in that context. Unlike rewrite rules, frules are
applied at the simplifier level.")
   (:paragraph)
   (:string "You may manually bring in a frule as an
assumption in a proof using the")
   (:command-name use)
   (:string "command.")
   (:paragraph)
   (:string "If you declare a frule then you ought to
prove it, unless you are in the process of developing a")
   (:command-name spec)
   (:punctuation ".")
   (:string "The proof obligation is simply the defining
expression.")))

(defzkhelp grule prover-command
  ((:syntax (grule |restricted_identifier| (|parameter_list|)
		   |expression|))
   (:newline) (:newline)
   (:string "Declare an axiom which is to be used as an assumption
rule, where parameter_list is:")
   (:newline) (:newline) (:syntax |identifier*|)
   (:newline) (:newline)
   (:string "For an unconditional grule, the expression must be a
literal, where a literal is a quantifier-free expression
that does not contain an")
   (:event-name if)
   (:string "or any boolean connectives, except a possible logical
negation at the outermost level. The expression is the asserted
expression.")
   (:paragraph)
   (:string "For a conditional grule, the expression
must be an implication with the conclusion being the asserted
expression with the same restriction as that for an unconditional
grule and the condition being a literal or conjunction of literals.")
   (:paragraph)
   (:string "The trigger of a grule is the first subexpression in the
asserted expression (scanning from left to right) that is a simple
pattern, where simple pattern is defined to be a function applied to
zero or more non-repeated variables. Each parameter must occur in the
trigger or in the condition.")
   (:paragraph)
   (:string "During simplification of a subexpression, when the
subexpression matches the trigger and the grule's condition is
known to be (TRUE) in the context of the subexpression, then
an appropriate instance of the asserted expression is asserted
in that context.")
   (:paragraph)
   (:string "You may manually bring in a grule as an assumption in
a proof using the")
   (:command-name use)
   (:string "command.")
   (:paragraph)
   (:string "If you declare a grule rule then you ought to prove
it, unless you are in the process of developing a")
   (:command-name spec)
   (:punctuation ".")
   (:string "The proof obligation is simply the defining
expression.")))

;;; Library Units

(defzkhelp library-units extra-help
  ((:newline)
   (:string "In addition to introducing declarations directly, you also may
load previously saved declarations from library units.
This is done using the")
   (:command-name load)
   (:string "command, which loads a specified")
   (:command-name spec)
   (:string "unit from the current library. For more information
about library units please see")
   (:help-name libraries)
   (:punctuation ".")))

;;; Proof Obligation

(defzkhelp proof-obligation extra-help
  ((:newline)
   (:string "When you introduce a declaration, the system
may generate a proof obligation. You must discharge the proof obligation
if you plan to make the development into a")
   (:command-name model)
   (:string "unit. Otherwise, you do not need to complete the proof.")
   (:paragraph)
   (:string "The proof obligation have to do with showing that
the theory extension resulting from the declaration is a conservative
extension which, among other things, does not introduce inconsistencies
(e.g. by showing that recursive definitions are terminating definitions).")))

;;; Current Formula

(defzkhelp current-formula extra-help
  ((:newline)
   (:string "To perform a proof of a formula, the formula
must first be made current, since proof steps transform only the
current formula. When you introduce a declaration that generates a
proof obligation (see")
   (:help-name proof-obligation)
   (:punctuation ")")
   (:string "the proof obligation is automatically made the current
formula. You can defer your proof and then later come back to the
proof using the")
   (:command-name try)
   (:string "command. The system allows arbitrary order of proofs
of declarations, but the proof of a declaration can use only
axioms associated with declarations or library units that are
introduced or loaded earlier then the declaration being proved.
If you are proving an anonymous formula then all axioms can be used.")
   (:paragraph)
   (:string "You can focus your proof on a case across multiple
commands using the")
   (:command-name cases)
   (:string "command, or on a subformula within a single command
using the")
   (:command-name with-subexpression)
   (:string "command modifier. When working on a case, the displayed
formula would be a subformula of the current formula. Most proof
commands operate on the current subformula.")
   (:paragraph)
   (:string "At anytime, you can print the current subformula
(current formula if not working on a case) using the")
   (:command-name print-formula)
   (:string "command. The current subformula is the same as the
current formula when not focusing on a subformula and not working
on a case.")))


(defzkhelp try prover-command
  ((:syntax (try |symbol-or-expression|))
   (:newline) (:newline)
   (:string "Begin or continue a proof. The")
   (:command-name try)
   (:string "command must be applied to either a declared symbol or an
expression. If it is applied to a declared symbol, then the proof
obligation for the declaration (if any) is made the current formula.
Otherwise, it must be applied to a well-formed expression and the
expression (which is not associated with any declaration) is made
the current formula.")
   (:paragraph)
   (:string "Note that if")
   (:command-name try)
   (:string "is applied to a declared symbol, the proof continues
where it left off. The current subformula of the proof is displayed.")))

;;; Proof Steps

(defzkhelp proof-steps extra-help
  ((:newline)
   (:string "A proof step transforms the current subformula to a new
subformula. Although a proof step may change the focus of a proof,
each proof step is equivalence preserving on the current formula
(modulo the \"current theory\").")
   (:paragraph)
   (:string "Some proof steps use the theorem prover's
automatic capabilities and may apply complex transformations.
There are other proof steps, considered to be manual steps, that
apply simpler transformations. Finally, there are macro proof
steps, each of which may perform a combination of automatic and
manual proof steps.")
   (:paragraph)
   (:string "You may undo proof steps in a last-in-first-out basis (see")
   (:help-name undoing)
   (:punctuation ")")
   (:punctuation ".")
   (:string "You also may print proof steps (see")
   (:help-name printing)
   (:punctuation ").")))

;;; Simplification

(defzkhelp simplification extra-help
  ((:newline)
   (:string "The process of simplification attempts to simplify
an expression to one that the system considers to be simpler.
Propositional tautologies are always detected.  In addition,
the simplification process reasons about equalities, integers,
and quantifiers.")
   (:paragraph)
   (:string "Forward and assumption rules are applied
during simplification.  In effect,")
   (:command-name frule)
   (:punctuation "s")
   (:string "and")
   (:command-name grule)
   (:punctuation "s")
   (:string "provide you with the mechanisms to extend the simplifier.
There are techniques (such as Nelson-Oppen's) that may be used to
extend the simplifier with decision procedures.")
   (:paragraph)
   (:string "Simplification works by traversing the")
   (:event-name if)
   (:string "form of an expression and simplifying the subexpressions.
Logical connectives are replaced by their IF form equivalents before
the expression is simplified")
   (:paragraph)
   (:string "When an")
   (:event-name if)
   (:string "expression is encountered, the")
   (:event-name test)
   (:string "expression becomes available as an assumption during
simplification of the")
   (:event-name left)
   (:string "branch, and the logical negation of the")
   (:event-name test)
   (:string "becomes available as an assumption during the
simplification of the")
   (:event-name right)
   (:string "branch.")
   (:paragraph)
   (:string "The main operation of the simplification of a
non-IF subexpression is a lookup operation which may result in a
simplified subexpression. The lookup operation uses all the capabilities
an underlying deductive database, which performs equality and integer
reasoning as well as applying FRULEs and GRULEs, all in a context
built by the traversal into the subexpression.")
   (:paragraph)
   (:string "The main operations for the simplification of an IF
subexpression are simplifying the subexpression to the")
   (:event-name left)
   (:string "part if the")
   (:event-name test)
   (:string "part is (TRUE), simplifying the subexpression to the")
   (:event-name right)
   (:string "part if the")
   (:event-name test)
   (:string "part is (FALSE), and simplifying the subexpression to the")
   (:event-name left)
   (:string "part if the LEFT part and the RIGHT part are the same.
In addition, the traversal may perform IF normalization if the TEST
part is an IF expression.")
   (:paragraph)
   (:string "Simplification is performed by the")
   (:command-name simplify)
   (:punctuation ",")
   (:command-name rewrite)
   (:punctuation ",")
   (:string "and")
   (:command-name reduce)
   (:string "commands.")
   (:newline)
   (:newline)
   (:string "Example of simplification:")
   (:newline)
   (:newline)
   (:string "Beginning proof of ... ")
   (:newline)
   (:formula (IMPLIES (AND (= (TYPE-OF I) (INT))
			   (>= I 3)
			   (<= I 3)
			   (ALL (J) (IMPLIES (>= J 0) (P J))))
		      (AND (P I)
			   (Q I)
			   (OR (Q 2)
			       (NOT (Q 2))))))
   (:newline)
   (:newline)
   (:command (simplify))
   (:newline) (:newline)
   (:string "Which simplifies")
   (:newline)
   (:string "forward chaining using")
   (:event-name >=.same.type)
   (:newline)
   (:string "with the instantiation ")
   (:formula-list ((= J 3)))
   (:string "to ... ")
   (:newline)
   (:formula (IMPLIES (AND (= (TYPE-OF I) (INT))
			   (>= I 3)
			   (<= I 3)
			   (ALL (J) (IMPLIES (>= J 0) (P J))))
		      (Q 3)))))

(defzkhelp simplify proof-step
  ((:syntax (simplify))
   (:newline) (:newline)
   (:string "Perform simplification on the current subformula.
The theorem prover may perform equality and integer reasoning,
and try to instantiate quantified variables to find a proof.
In addition, forward and assumption rules may be applied. You
may use the proof modifiers")
   (:command-name with-instantiation)
   (:string "or")
   (:command-name without-instantiation)
   (:string "to control whether you want the theorem prover
to try variable instantiations. Currently, the theorem prover will
try variable instantiations by default.")))

(defzkhelp trivial-simplify modify
  ((:syntax (trivial-simplify))))

;;; Rewriting

(defzkhelp rewriting extra-help
  ((:newline)
   (:string "The rewriting process applies rewrite rules while
performing simplification.  While traversing a formula being
rewritten, the theorem prover tries to apply rewrite rules that
match the subexpression being traversed.")
   (:paragraph)
   (:string "In the simple case, the rule being applied is
unconditional and the rule is applied immediately.  The
subexpression that has matched the pattern is replaced by
the appropriate instance of the replacing expression of the
rule, produced by replacing variables in the replacing
expression with expressions determined during the pattern
match.")
   (:paragraph)
   (:string "In the more complicated case, the rule being applied
is conditional.  The theorem prover must prove the condition as a
subgoal before the rule can be applied. The process of proving the
condition also may determine some of the variable replacements.")
   (:paragraph)
   (:string "Rewriting is performed by the")
   (:command-name rewrite)
   (:string "and")
   (:command-name reduce)
   (:string "commands.")
   (:newline) (:newline)
   (:string "Example of rewriting:")
   (:newline)
   (:newline)
   (:event (RULE NTH-IN (I0 S0)
		 (IMPLIES (AND (< 0 I0)
			       (<= I0 (LENGTH S0)))
			  (= (IN-SEQ (NTH I0 S0) S0) (TRUE)))))
   (:newline) (:newline)
   (:event (GRULE LENGTH-NON-NEGATIVE (S0)
		  (>= (LENGTH S0) 0)))
   (:newline) (:newline)
   (:command (TRY (IMPLIES (= (LENGTH S1) (+ (LENGTH S0) 1))
			   (IN (NTH 1 S1) S1))))
   (:newline) (:newline)
   (:string "Beginning proof of ... ")
   (:newline)
   (:formula (IMPLIES (= (LENGTH S1) (+ (LENGTH S0) 1))
		      (IN-SEQ (NTH 1 S1) S1)) )
   (:newline) (:newline)
   (:command (REWRITE))
   (:newline) (:newline)
   (:string "Which simplifies")
   (:newline)
   (:string "when rewriting with")
   (:event-name NTH-IN)
   (:newline)
   (:string "forward chaining using")
   (:event-name-list (>=.same.type))
   (:newline)
   (:string "with the assumptions")
   (:event-name-list
    (succ.int length-non-negative))
   (:string "to ... ")
   (:newline)
   (:formula (TRUE))))

(defzkhelp pattern-matching extra-help
  ((:newline)
   (:string "Pattern matching is the process in which the theorem
prover selects rules for application. The process of pattern
matching proceeds by comparing the pattern to the current
subexpression being traversed by the prover. If there exists a
set of substitutions for the variables occurring in the pattern
which makes the pattern equal to the subexpression, then the
pattern is said to have matched the subexpression with those
substitutions.")
   (:paragraph)
   (:string "If the rule is unconditional then it may immediately
be applied using these substitutions. If the rule is conditional,
then the condition must be proved as a subgoal before the rule is
applied. The subgoaling process may result in additional
substitutions for the application of the rule.")
   (:paragraph)
   (:string "Some restrictions are placed on an expression
that is to be used as a pattern.  First, a pattern must be a
function application. Second, quantifiers,")
   (:event-name if)
   (:string "expressions and logical connectives are disallowed
in a pattern.")
   (:paragraph)
   (:string "For the following rewrite rule")
   (:newline)
   (:event (rule join-empty (s0) (= (join s0 (empty)) s0)))
   (:newline) (:newline)
   (:string "the pattern is")
   (:formula (join s0 (empty)))
   (:newline) (:newline)
   (:string "in which")
   (:event-name s0)
   (:string "is a variable. Thus, this pattern will match all
expressions that")
   (:event-name join)
   (:string "an arbitrary expression with the empty sequence.
The arbitrary expression will become the substitution for")
   (:event-name s0)
   (:punctuation ".")))

(defzkhelp rewrite modify
  ((:syntax (rewrite))))

(defzkhelp trivial-rewrite modify
  ((:syntax (trivial-rewrite))))

;;; Reduction

(defzkhelp reduction extra-help
  ((:newline)
   (:string "The reduction process may replace function applications
with appropriate instances of the functions' definitions,
in addition to performing all the things that rewriting does. Reduction
is the most powerful tool in the arsenal of the theorem prover.
Reduction is performed by the")
   (:command-name reduce)
   (:string "command.")
   (:paragraph)
   (:string "All accessible and enabled non-recursive definitions
are used to replace function applications. For recursive function
definitions, heuristics are used to determine whether to replace
a recursive function application. The heuristics are matched to the
way automatic induction is performed (see")
   (:help-name induction)
   (:punctuation ")")
   (:punctuation ".")))

(defzkhelp trivial-reduce modify
  ((:syntax (trivial-reduce))))

(defzkhelp subgoaling extra-help
  ((:newline)
   (:string "Subgoaling is the process of attempting to prove
a rule's condition. For an assumption rule, subgoaling is
performed entirely within simplification. For a rewrite rule,
the condition is recursively rewritten or reduced depending
on whether rewriting or reduction is being performed. Only if
the condition is proved to be")
   (:formula (true))
   (:string "is the subgoal said to have succeeded and may
the application of the rule proceed.")
   (:paragraph)
   (:string "There may be variables that occur
in the condition of a rewrite rule but not in the pattern. These
variables will not have been instantiated by the pattern
matching process. During subgoaling, the theorem prover will
attempt to instantiate these variables to rewrite or reduce the
condition to")
   (:formula (true))
   (:punctuation ".")
   (:string "However, no backtracking is performed on the
instantiations.  Although this strategy is simple, it can be
effective in practice.")
   (:paragraph)
   (:string "There is a limit on the depth to which subgoaling
will attempt to find a proof requiring additional subgoaling.
If this limit is reached before a proof is found, then the
subgoaling immediately fails.")))

(defzkhelp reduce proof-step
  ((:syntax (reduce))
   (:newline) (:newline)
   (:string "Reduce the current subformula. The reduction
consists of simplification, rewriting, and replacing
function applications with appropriate instances of their
definitions. The")
    (:command-name reduce)
    (:string "command is the most powerful of the automatic
proof commands.")))


;;; Using Definitions

(defzkhelp using-definitions extra-help
  ((:newline)
   (:string "The reduction commands may use function
definitions and axioms automatically.  However, you may
want to use a function definition or axiom manually.
You may apply rewrite rules manually using the")
   (:command-name apply)
   (:string "command; function applications may be
replaced with their definition instances manually using the")
   (:command-name invoke)
   (:string "command; and you may manually use axioms
including function definitions, forward rules, assumption
rules and rewrite rules as hypotheses using the")
   (:command-name use)
   (:string "command.")))

(defzkhelp apply modify
  ((:syntax (apply |identifier| |[expression]|))))

(defzkhelp invoke proof-step
  ((:syntax (invoke |expression|))
   (:newline) (:newline)
   (:string  "Replace applications of a function using the
function's definition everywhere within the current subformula.")
   (:command-name invoke)
   (:string "works for functions that are disabled.")
   (:command-name invoke)
   (:string "may be applied to an expression rather than to a
function, in which case it works like a selective invoke in that
occurrences of the expression in the current subformula are replaced.")
   (:newline) (:newline)
   (:string "Example:") (:newline) (:newline)
   (:command (function plus-abs (i j) () (+ (abs i) (abs j))))
   (:newline) (:newline)
   (:command (try (= k (* (plus-abs i 3) (plus-abs j 4)))))
   (:newline) (:newline)
   (:string "Beginning proof of ...") (:newline)
   (:formula (= k (* (plus-abs i 3) (plus-abs j 4)))) (:newline) (:newline)
   (:command (invoke (plus-abs j 4))) (:newline) (:newline)
   (:string "Invoking")
   (:formula (plus-abs j 4))
   (:string "gives ...") (:newline)
   (:formula (= k (* (plus-abs i 3) (+ (abs j) (abs 4)))))
   (:newline) (:newline)
   (:command (invoke plus-abs)) (:newline) (:newline)
   (:string "Invoking")
   (:event-name plus-abs)
   (:string "gives ...") (:newline)
   (:formula (= k (* (+ (abs i) (abs 3)) (+ (abs j) (abs 4)))))))

(defzkhelp add modify
  ((:syntax (add |identifier| |{(identifier expression)}*|))
   (:command-argument |identifier|)))

(defzkhelp use modify
  ((:syntax (use |identifier| |{(identifier expression)}*|))
   (:command-argument |identifier|)))


;;; Equality

(defzkhelp equality extra-help
  ((:newline)
   (:string "The following subsections describe proof steps
that perform simple equality reasoning. More sophisticated
equality reasoning is performed by the simplifier (see")
   (:help-name simplification)
   (:punctuation ").")))

(defzkhelp equality-substitute modify
  ((:syntax (equality-substitute |[expression]|))))

(defzkhelp label modify
  ((:syntax (label |expression|))))


(defzkhelp contradict modify
  ((:syntax (contradict))))

;;; Rearranging

(defzkhelp rearranging extra-help
  ((:newline)
   (:string "The automatic part of the theorem prover is sensitive
to the ordering of the subexpressions within the formula being
reduced (see")
   (:help-name reduction)
   (:punctuation ").")
   (:string "Thus, it is sometimes required, and often advantageous,
to rearrange the order of a formula. Most of the rearranging
commands are directly controlled by the user. An exception is
the")
   (:command-name rearrange)
   (:string "command which is fully automatic and uses heuristics
to rearrange the current subformula.")))

(defzkhelp rearrange proof-step
  ((:syntax (rearrange))
   (:newline) (:newline)
   (:string "Try to rearrange the current formula. The
rearrangement consists of reordering the arguments of the
conjunctions and disjunctions of the current subformula. In
general, type assertions, equalities and simple expressions
are placed before more complex arguments such as quantified
expressions.")
   (:paragraph)
   (:string "Rearranging can be useful because the prover is
sensitive to the ordering within formulas (see")
   (:help-name reduction) (:punctuation ").")
   (:string "The theorem prover is often more likely to obtain
a proof, and may do so more efficiently, if a formula has been
rearranged using the") (:command-name rearrange)
   (:string "command.")))

(defzkhelp split proof-step
  ((:syntax (split |expression|))
   (:newline) (:newline)
   (:string "Perform a case split on the current subformula with
the supplied")
   (:command-argument expression)
   (:punctuation ".")
   (:string "This results in a new subformula of the form")
   (:newline)
   (:formula (if |expression| |subformula| |subformula|))
   (:punctuation ".")
   (:paragraph)
   (:string "This is useful if you want the theorem prover to
consider the two cases when processing the current subformula,
one where expression is assumed (TRUE) and the other where the
logical negation of the expression is assumed (TRUE).")
   (:paragraph)
   (:string "You can follow the")
   (:command-name split)
   (:string "command with the")
   (:command-name cases)
   (:string "command to work on the two cases separately.")
   (:paragraph)
   (:string "You also may use the")
   (:command-name split)
   (:string "command to place a specific hypothesis before a
subexpression. This step may be required because of the
sensitivity of the theorem  prover towards the ordering of
subexpressions within the formula being reduced (see")
   (:help-name reduction)
   (:punctuation ").")
   (:paragraph)
   (:string "Example:") (:newline) (:newline)
   (:command (try (implies (all (i j k) (p i j k)) (all (l m n) (q l m n)))))
   (:newline) (:newline)
   (:string "Beginning proof of ...") (:newline)
   (:formula (implies (all (i j k) (p i j k)) (all (l m n) (q l m n))))
   (:newline) (:newline)
   (:command (split (= m 0))) (:newline) (:newline)
   (:string "Splitting on") (:formula (= m 0)) (:string "generates ...")
   (:newline)
   (:formula (implies (all (i j k) (p i j k))
		      (all (l m) (if (= m 0) (all n (q l m n))
				 (all (n$0) (q l m n$0))))))))

(defzkhelp suppose proof-step
  ((:syntax (suppose |expression|))
   (:newline) (:newline)
   (:string "Convert the current subformula to a conjunction of two cases.
The first case is an implication with the")
   (:command-argument predicate)
   (:string "as a hypothesis and the current subformula as a conclusion.
The second case is a disjunction of the")
   (:command-argument predicate)
   (:string "and the current subformula.")
   (:paragraph)
   (:string "Given a current subformula")
   (:newline)
   (:formula formula)
   (:newline)
   (:string "the command")
   (:newline)
   (:command (suppose expression))
   (:newline)
   (:string "produces")
   (:newline)
   (:formula (and (implies expression formula) (or expression formula)))))


;;; Cases Mechanism

(defzkhelp cases-mechanism extra-help
  ((:newline)
   (:string "The CASES mechanism allows you to work on
cases of the current formula individually. You may break the current
subformula into separate cases using the")
   (:command-name cases)
   (:string "command. Each case may then be worked on individually.
You can move among the cases using the")
   (:command-name next)
   (:string "command. The movement is restricted (always
move to the next non-trivial case). If there are no more cases, the")
   (:command-name next)
   (:string "command completes the cases.")))

(defzkhelp cases modify
  ((:syntax (cases))))

(defzkhelp next proof-step
  ((:syntax (next))
   (:newline)
   (:newline)
   (:string "Proceed to the next non-trivial case or, if there is
no more non-trivial case, complete the proof. Note that some
non-trivial cases may be short-circuited.")))

(defzkhelp delete-hypotheses modify
  ((:syntax (delete-hypotheses |{expression}+|))))


;;; Normal Forms

(defzkhelp normal-forms extra-help
  ((:newline)
   (:string "The system provides you with commands to transform
the current subformula into conjunctive or disjunctive normal form.")))

(defzkhelp conjunctive modify
  ((:syntax (conjunctive))))

(defzkhelp disjunctive modify
  ((:syntax (disjunctive))))

;;; Quantifiers

(defzkhelp quantifiers extra-help
  ((:newline)
   (:string "In addition to the automatic quantifier manipulation
performed during reduction, there are commands that allow you to
perform quantifier manipulation manually.")))

(defzkhelp prenex modify
  ((:syntax (prenex |[variables]|))))

(defzkhelp instantiate proof-step
  ((:syntax (instantiate |{(identifier expression)}+|))
   (:newline) (:newline)
   (:string "The")
   (:command-name instantiate)
   (:string "command performs instantiations on the current
subformula. The instantiations to be performed is given by")
   (:command-argument |{(identifier expression)}+|)
   (:punctuation ".")
   (:string "To allow the instantiations to occur, the scopes of
quantifiers in the formula may be extended or contracted. Logical
equivalence is maintained by keeping the uninstantiated
subexpression(s) as extra conjunct(s) or disjunct(s). The requested
instantiations may be disallowed, in which case the command has no
effect.")
   (:newline) (:newline)
   (:string "Example:") (:newline) (:newline)
   (:string "Beginning proof of ...") (:newline)
   (:formula (implies (all (i j k) (p i j k)) (all (l n) (p l m n))))
   (:newline) (:newline)
   (:command (instantiate '((= i l) (= j m) (= k n))))
   (:newline) (:newline)
   (:string "Instantiating")
   (:formula-list ((= i l) (= j m) (= k n)))
   (:string "gives ...")
   (:newline)
   (:formula (implies (and (p l m n) (all (i j k) (p i j k))) (p l m n)))))


;;; Induction

(defzkhelp induction extra-help
  ((:newline)
   (:string "The theorem prover performs induction using the
technique of Boyer-Moore. Normally, induction schemes are
heuristically chosen based on calls to recursive functions
within the current formula. However, you may direct the prover
using the")
   (:command-name induct)
   (:string "command with an explicit term on which to induct.
The following is an example of a user directed induction.")
   (:paragraph)
   (:string "First, introduce a recursive function definition
for exponentiation.")
   (:newline) (:newline)
   (:event (function exp (i k) ((measure k))
		     (if (and (= (type-of i) (int))
			      (= (type-of k) (int)) (> k 0))
			 (* i (exp i (- k 1)))
		       0)))
   (:newline) (:newline)
   (:string "In the above definition, the second argument,")
   (:event-name k) (:punctuation ",")
   (:string "is a measured parameter. The recursive call to")
   (:event-name exp) (:string "is governed by the")
   (:event-name if) (:string "test,")
   (:formula (and (= (type-of i) (int)) (= (type-of k) (int)) (> k 0)))
   (:punctuation ".") (:paragraph)
   (:string "Next, we begin a proof of a conjecture involving")
   (:event-name exp) (:punctuation ".") (:newline) (:newline)
   (:command (try (implies (and (= (type-of i) (int))
				(= (type-of j) (int)) (>= i 0) (> j 0))
			   (> (exp i j) 0))))
   (:newline) (:newline)
   (:string "Beginning proof of ... ") (:newline)
   (:formula (implies (and (= (type-of i) (int))
			   (= (type-of j) (int)) (>= i 0) (> j 0))
		      (> (exp i j) 0)))
   (:paragraph)
   (:string "We now perform an explicit induction step, giving the
term on which to induct.")
   (:newline) (:newline) (:command (induct (exp i j)))
   (:newline) (:newline)
   (:string "Inducting using the following scheme ... ") (:newline)
   (:formula
    (AND (IMPLIES (AND (= (TYPE-OF I) (INT)) (= (TYPE-OF J) (INT))
		       (> J 0) (*P* I (- J 1)))
		  (*P* I J))
	 (IMPLIES (NOT (AND (= (TYPE-OF I) (INT))
			    (= (TYPE-OF J) (INT)) (> J 0)))
		  (*P* I J))))
   (:newline) (:newline) (:string "produces ... ") (:newline)
   (:formula
    (AND (IMPLIES
	  (AND (= (TYPE-OF I) (INT)) (= (TYPE-OF J) (INT)) (> J 0)
	       (IMPLIES (AND (= (TYPE-OF I) (INT))
			     (= (TYPE-OF (- J 1)) (INT))
			     (>= I 0) (> (- J 1) 0))
			(> (EXP I (- J 1)) 0)))
	  (IMPLIES (AND (= (TYPE-OF I) (INT)) (= (TYPE-OF J) (INT))
			(>= I 0) (> J 0))
		   (> (EXP I J) 0)))
	 (IMPLIES
	  (NOT (AND (= (TYPE-OF I) (INT)) (= (TYPE-OF J) (INT))
		    (> J 0)))
	  (IMPLIES (AND (= (TYPE-OF I) (INT)) (= (TYPE-OF J) (INT))
			(>= I 0) (> J 0))
		   (> (EXP I J) 0)))))
   (:paragraph)
   (:string "The above induction scheme consists of an inductive
case and a base case, and follows directly from the definition of")
   (:event-name exp)
   (:punctuation ".")
   (:string "The induction case follows from the recursive call
in the definition. Thus the conjecture, with")
   (:event-name j) (:string "replaced by") (:formula (minus j 1))
   (:punctuation ",")
   (:string "is assumed together with the condition governing the
recursion. In the base case, the governing condition is the negation
of the condition of the induction case.")
   (:paragraph)
   (:string "Note that for the above example the heuristic would
have chosen the same induction scheme, since there is only one call
to a recursive function in the conjecture, and that call is exactly
the term specified.")
   (:paragraph)
   (:string "A term that is a call to a recursive function will
not necessarily produce an induction scheme. A sufficient
condition to guarantee an induction scheme is if the measured
arguments of the call are distinct variables.")))

(defzkhelp induct modify
  ((:syntax (induct |[expression]|))))

;;; Macro Steps

(defzkhelp macro-steps extra-help
  ((:newline)
   (:string "The following subsections describe the macro proof steps
available. A macro proof step performs one or more basic proof steps,
according to some strategy. The strategy may include backtracking, i.e.,
undoing a previously applied proof step. The use of the macro proof step
is not recorded, instead only the basic proof steps appear in the
resulting proof.")))

(defzkhelp prove prover-command
  ((:syntax (prove))
   (:newline) (:newline)
   (:string "Call the default proof command.  Currently, this
is")
   (:command-name reduce) (:punctuation ".")))

(defzkhelp prove-by-cases modify
  ((:syntax (prove-by-cases))))

(defzkhelp prove-by-induction modify
  ((:syntax (prove-by-induction))))

(defzkhelp prove-by-rearrange modify
  ((:syntax (prove-by-rearrange))))

;;; Libraries

(defzkhelp libraries extra-help
  ((:newline)
   (:string "The library facility allows for the storage,
retrieval and deletion of units from libraries.  The main purpose
of this facility is to provide a modularization mechanism.  Libraries
may contain")
   (:event-name spec)
   (:string "(specification) units, which may be loaded into the
database using the") (:command-name load)
   (:string "command.  When loaded, declarations created by these
units are assumed to be proven elsewhere.  More specifically, they
must be proven in their corresponding")
   (:event-name model)
   (:string "(implementation) units.  By loading only the
specification (which may be somewhat abstract), the prover
will perform proofs at the specification level, which may
be less complex than if the proofs are done at the level of the
implementation.  You also may save an uncompleted session in a")
   (:event-name freeze)
   (:string "unit.")
   (:paragraph)
   (:string "You may store the contents of the database as a")
   (:event-name spec) (:punctuation ",") (:event-name model)
   (:punctuation ",") (:string "or") (:event-name freeze)
   (:string "unit in a library using the") (:command-name make)
   (:string "command. In the first case, stub declarations are
allowed, while in the second case, they are prohibited.  In any
case, a circularity check is performed and, if the unit's
counterpart is already in the library, a syntactic
consistency check is also performed. Only if these checks are
successful is the unit stored in the library.")
   (:paragraph)
   (:string "In addition to the above operations, you also may
edit a unit using the") (:command-name edit)
   (:string "command.  This has the effect of restoring the
database to the state when the unit was made.  You also
may delete units from libraries using the")
   (:command-name delete)
   (:string "command.  The command")
   (:command-name print-library-status)
   (:string "is also provided to show the status of a library or
library unit.")))

(defzkhelp load prover-command
  ((:syntax (load |identifier|))
   (:newline) (:newline)
   (:string "Load the library") (:event-name spec)
   (:string "unit specified by the identifier. The unit's
declarations are loaded into the database as subsidiary
declarations of the load.  If the library unit has
already been loaded, it is not reloaded and the operation is
not recorded. A library unit being loaded may in turn load
another library unit.")))

(defzkhelp make prover-command
  ((:syntax (make |identifier| |object_type|))
   (:newline) (:newline)
   (:string "Write the contents of the database as a library
unit specified by the identifier in the library specified by the
string. The object_type determines whether the unit is to
be a specification (if it is")
   (:event-name spec) (:punctuation "),")
   (:string "an implementation (if it is")
   (:event-name model) (:punctuation "),")
   (:string "or an incomplete development (if it is")
   (:event-name freeze) (:punctuation ").")
   (:string "For a specification unit, stubs are allowed and
procedures must be stubs.  For an implementation unit, stubs
are prohibited.")))

(defzkhelp edit modify
  ((:syntax (edit |identifier| |object_type|))))

(defzkhelp delete modify
  ((:syntax (delete |identifier| |object_type|))))

(defzkhelp print-library-status prover-command
  ((:syntax (print-library-status))
   (:newline) (:newline)
   (:string "Print the status of the current library.
The names of the units in the library are listed
with their types (e.g. spec, model, or freeze).")))

(defzkhelp set-library modify
  ((:syntax (set-library |string|))))

;;; Undoing

(defzkhelp undoing extra-help
  ((:newline)
   (:string "The undoing group of commands allows you to
reverse the effect of one or more previous commands. However,
the undoing commands cannot themselves be undone. All commands
are undone in a last-in-first-out basis.")
   (:paragraph)
   (:string "The")
   (:command-name back) (:punctuation ",")
   (:command-name back-thru) (:punctuation ",")
   (:command-name back-to) (:punctuation ",")
   (:string "and") (:command-name retry)
   (:string "commands undo proof steps, while the")
   (:command-name undo) (:punctuation ",")
   (:command-name undo-back-thru) (:punctuation ",")
   (:command-name undo-back-to) (:punctuation ",")
   (:string "and") (:command-name reset)
   (:string "commands undo declarations.")))

(defzkhelp back modify
  ((:syntax (back |[numeral]|))))

(defzkhelp back-thru modify
  ((:syntax (back-thru |identifier|))))

(defzkhelp back-to modify
  ((:syntax (back-to |identifier|))))

(defzkhelp retry prover-command
  ((:syntax (retry))
   (:newline) (:newline)
   (:string "Restart the current proof. Any previous partial
proof is discarded.")))

(defzkhelp undo prover-command
  ((:syntax (undo |[numeral]|))
   (:newline) (:newline)
   (:string "Undo the latest declaration.  Once undone, it
is as if the declaration had never been entered.  The name of the
undone declaration is displayed if the undo is successful.")))

(defzkhelp undo-back-thru prover-command
  ((:syntax (undo-back-thru |identifier|))
   (:newline) (:newline)
   (:string "Undo the effect of declarations entered since
the specified declaration inclusively. The effect is as though
all declarations from the specified declaration on were never
entered. The specified identifier is displayed if the command
is successful.")))

(defzkhelp undo-back-to prover-command
  ((:syntax (undo-back-to |identifier|))
   (:newline) (:newline)
   (:string "Undo the effect of declarations entered since
the specified declaration exclusively. The effect is as though
all declarations after the specified declaration were never
entered. The specified identifier is displayed if the command
is successful.")))

(defzkhelp reset prover-command
  ((:syntax (reset))
   (:newline) (:newline)
   (:string "Reset the current development to an initial state.
All declarations that you entered are undone.")))

;;; Printing

(defzkhelp printing extra-help
  ((:newline)
   (:string "The help and print commands allow all or part of the
on-line help and the information stored within the database
to be displayed.")))

(defzkhelp help modify
  ((:syntax (help |[identifier]|))))

(defzkhelp print-declaration prover-command
  ((:syntax (print-declaration |identifier|))
   (:newline) (:newline)
   (:string "Print the declaration for the identifier.")))

(defzkhelp print-recent-declarations prover-command
  ((:syntax (print-recent-declarations))
   (:newline) (:newline)
   (:string "Print the 8 most recent declarations that you
entered.")))

(defzkhelp print-proof prover-command
  ((:syntax (print-proof))
   (:newline) (:newline)
   (:string "Print the current proof. This includes the
intermediate results and the proof commands.")))

(defzkhelp print-proof-summary prover-command
  ((:syntax (print-proof-summary))
   (:newline) (:newline)
   (:string "Print the commands entered so far for the
current proof.")))

(defzkhelp print-rules-about prover-command
  ((:syntax (print-rules-about |expression|))
   (:newline) (:newline)
   (:string "Print all rules (rewrite, forward, and assumption)
that match the expression. If the expression is an identifier,
then all rules that have the identifier as their outermost
function in their pattern are printed.")))

(defzkhelp rules-about prover-command
  ((:syntax (rules-about |expression|))
   (:newline) (:newline)
   (:string "Print the names of all rules (rewrite, forward,
and assumption) that match the expression. If the expression is
an identifier, then the names of all rules that have the
identifier as their outermost function in their pattern are
printed.")))

(defzkhelp print-status prover-command
  ((:syntax (print-status))
   (:newline) (:newline)
   (:string "Print the proof status of all declarations that
have proof obligations. The declaration associated with the
current formula is printed as well as the list of proven
declarations and the list of unproven declarations.")))

(defzkhelp print-history prover-command
  ((:syntax (print-history))
   (:newline) (:newline)
   (:string "Print all declarations entered in the order
entered.")))




;;; Proof Logging

(defzkhelp proof-logging extra-help
  ((:newline)
   (:string "ZK has a proof-logging facility that enables proof steps
to be logged in terms of very low-level inferences that can be used
for the certification of proofs.  The proof checker is used to formally
certify proofs.  A proof whose proof log is accepted by the proof
checker has a high degree of assurance.  The proof browser is used to
informally certify proofs.  A proof log can be browsed by the user to
increase the credibility of a proof.")
   (:paragraph)
   (:string "Initially, proof logging is disabled.  It can be enabled
or disabled at any time.  This flexibility is useful for proof browsing
during the development of a proof.  For proof checking, it is usual to
redo a completed proof with proof logging enabled so it can be checked
by the proof checker.  Proof logs can be checked either by the integrated
proof checker, or dumped to a file for certification by an independent
proof checker.")
   (:paragraph)
   (:string "The")
   (:command-name log-on)
   (:string "command is used to enable proof logging, while the")
   (:command-name log-off)
   (:string "command is used to disable proof logging.  Proof logs can
be saved to a file using the")
   (:command-name dump-log)
   (:string "command.  The integrated proof checker can be invoked
using the")
   (:command-name check-proof)
   (:string "and")
   (:command-name check-all-proofs)
   (:string "commands.")))

(defzkhelp dump-log modify
  ((:syntax (dump-log |string|))))

(defzkhelp check-proof prover-command
  ((:syntax (check-proof |[identifier]|))
   (:newline) (:newline)
   (:string "The")
   (:command-name check-proof)
   (:string "command checks the proof associated with")
   (:event-name identifier)
   (:string "if specified or the proof associated with the current
formula if none was specified.  Proof logging must have been enabled
during the entire proof for the proof check to succeed.")))

(defzkhelp check-all-proofs prover-command
  ((:syntax (check-all-proofs))
   (:newline) (:newline)
   (:string "The")
   (:command-name check-all-proofs)
   (:string "command checks all proofs in the current development.
A report is displayed showing the results for each proof checked.
The proof check will fail for any proof whose proof log was not
fully recorded.")))



;;; Proof Browsing

(defzkhelp proof-browsing extra-help
  ((:newline)
   (:string "ZK has a proof browsing facility that enables proof steps
to be examined at levels of detail controlled by the user.  To enable
examination of detailed steps, proof logging must be enabled during
the proof.")
   (:paragraph)
   (:string "The")
   (:command-name browse-begin)
   (:string "command is used to initiate the browsing of a proof.
The forward-moving commands are")
   (:command-name browse-forward)
   (:punctuation ",")
   (:command-name browse-down)
   (:string "and")
   (:command-name browse-up)
   (:punctuation ".")
   (:string "The undo commands are")
   (:command-name browse-back)
   (:string "and")
   (:command-name rebrowse)
   (:punctuation ".")
   (:string "The")
   (:command-name browse-print-formula)
   (:string "command can be used to print the current browse formula.")
   (:paragraph)
   (:string "The command line interface to proof browsing provides
only a primitive proof browsing capability.  A graphical user
interface would enhance this capability.")))

(defzkhelp browse-begin proof-step
  ((:syntax (browse |[identifier]|))
   (:newline) (:newline)
   (:string "Start the browsing of a complete or partial proof.
If")
   (:command-argument |identifier|)
   (:string "is supplied,
then the proof associated with")
   (:command-argument |identifier|)
   (:string "is browsed.  Otherwise, the current proof is browsed.")))

(defzkhelp browse-back proof-step
  ((:syntax (browse-back |[numeral]|))
   (:newline) (:newline)
   (:string "Move the Proof Browser backwards")
   (:command-argument |numeral|)
   (:string "steps.")))


;;; Command Modifiers

(defzkhelp command-modifiers prover-command
  ((:newline)
   (:string "Command modifiers allow you to have finer control
over the commands. For example, you may use the")
   (:command-name without-instantiation)
   (:string "command modifier to disable automatic variable
instantiation for the duration of the command being modified.
You may nest command modifiers. Inner modifiers have precedence
over the outer modifiers.")))

(defzkhelp with-subexpression prover-command
  ((:syntax (with-subexpression |expression| |command|))
   (:newline) (:newline)
   (:string "Perform the command on all occurrences of the
expression in the current formula. For reduction commands, the
command is performed on the expression in context (i.e., the
context is available as assumptions).")))

(defzkhelp with-instantiation prover-command
  ((:syntax (with-instantiation |command|))
   (:newline) (:newline)
   (:string "Perform the command with automatic instantiation
enabled.")))

(defzkhelp without-instantiation prover-command
  ((:syntax (without-instantiation |command|))
   (:newline) (:newline)
   (:string "Perform the command with automatic instantiation
disabled.")))

(defzkhelp with-case-analysis prover-command
  ((:syntax (with-case-analysis |command|))
   (:newline) (:newline)
   (:string "Perform the command with case analysis
enabled during reduction.")))

(defzkhelp without-case-analysis prover-command
  ((:syntax (without-case-analysis |command|))
   (:newline) (:newline)
   (:string "Perform the command with case analysis
disabled during reduction.")))

(defzkhelp with-normalization prover-command
  ((:syntax (with-normalization |command|))
   (:newline) (:newline)
   (:string "Perform the command with normalization
enabled during reduction.  Normalization applies case analysis to Boolean
connectives, and is needed in order to recognize some tautologies.  Sometimes,
however, it can cause formulas to be duplicated and thus may lead to larger
formulas.")))

(defzkhelp without-normalization prover-command
  ((:syntax (without-normalization |command|))
   (:newline) (:newline)
   (:string "Performs the command with normalization
disabled during reduction.  Normalization applies case analysis to Boolean
connectives, and is needed in order to recognize some tautologies.  Sometimes,
however, it can cause formulas to be duplicated and thus may lead to larger
formulas.")))

;;; Enable-disable

(defzkhelp enable-disable extra-help
  ((:newline)
   (:string "The automatic part of the prover may use
declarations that carry heuristic information when reducing a
formula. However, it is sometimes desirable or even necessary
to prevent an automatic use of a declaration. This can be done
by making the declaration disabled by default using the")
   (:command-name disabled)
   (:string "modifier. The declaration remains disabled
unless it is specified in a")
   (:command-name with-enabled)
   (:string "modifier.")))

(defzkhelp disabled prover-command
  ((:syntax (disabled |command|))
   (:newline) (:newline)
   (:string "Disable the heuristics associated with the
declaration being introduced  by default.")))

(defzkhelp with-enabled prover-command
  ((:syntax (with-enabled (|identifier*|) |command|))
   (:newline) (:newline)
   (:string "Perform the command with the heuristics
associated with the identifiers enabled.")))

(defzkhelp with-disabled prover-command
  ((:syntax (with-disabled (|identifier*|) |command|))
   (:newline) (:newline)
   (:string "Perform the command with the heuristics
associated with the identifiers disabled.")))



;;; Miscellaneous

(defzkhelp miscellaneous extra-help
  ((:newline)
   (:string "There are commands that don't fit into
any of the other categories. These include commands for
scripting into a file and commands for reseting and
printing statistics gathered during reduction.")))

(defzkhelp script prover-command
  ((:syntax (script |string|))
   (:newline) (:newline)
   (:string "Start the scripting of the current session
into the specified file. Your input and the system output
are recorded.")))

(defzkhelp end-script prover-command
  ((:syntax (end-script))
   (:newline) (:newline)
   (:string "End the scripting of the current session and
closes the script file.")))

(defzkhelp print-stats prover-command
  ((:syntax (print-stats))
   (:newline) (:newline)
   (:string "Print the statistics associated with reduction
accumulated since the last")
   (:command-name clear-stats)
   (:punctuation ".")))

(defzkhelp read prover-command
  ((:syntax (read |string|))
   (:newline) (:newline)
   (:string "Redirect input to be from the file specified.")))

;;; Syntax

(defzkhelp syntax extra-help
  ((:newline)
   (:string "This section contains the collected syntax of prover
   declarations and commands. They are presented in alphabetic order.")
   (:newline)
   (:newline)
   (:syntax-list (:eval (get-sorted-syntax)))))

;;; Initial Theory

(defzkhelp initial-theory extra-help
  ((:newline)
   (:string "This section lists declarations that describe
the initial theory.")
   (:newline)
   (:newline)
   (:command-list (:eval (get-initial-database)))))

;;; Initial database

(defun get-initial-database ()
  (mapcar #'format-event
	  (mapcar #'group-event (system-history))))

;;; Error Codes

(defzkhelp error-codes extra-help
  ((:newline)
   (:string "Whenever an error is detected, a message is printed that describes
   the error and where it occurred. This message includes an error code. A")
   (:command-name help)
   (:string "on the error code will print an explanation on the cause of
the error. Help for each of the error codes is available.")))

;;; Bibliography

(defzkhelp bibliography extra-help
  ((:newline)
   (:string "Craigen, Dan.")
   (:newline)
   (:string "Reference Manual for the Language Verdi.")
   (:newline)
   (:string "Odyssey Research Associates Technical Report,
TR-90-5429-09, February 1990.")
   (:newline) (:newline)
   (:string "Saaltink, Mark.")
   (:newline)
   (:string "A Formal Description of Verdi.")
   (:newline)
   (:string "Odyssey Research Associates Technical Report,
TR-89-5429-10, October 1989.")   
   ))
