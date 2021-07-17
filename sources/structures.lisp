
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
;;; General structures that are independent of inference techniques.
;;; They are used in maintaining a current theory.
;;; =====================================================================

(in-package "ZK")

(defparameter *zk-package* *package*)

;;; The current version for the ZK system.

(defparameter *zk-version* "1.0")

;;; Compatible library versions.

(defparameter *compatible-zk-versions* '("1.0"))



;;; ---------------------------------------------------------------------
;;; ========================= Section for events ========================
;;; ---------------------------------------------------------------------

;;; The current theory is maintained in a history. Events are the
;;; main entries in the history.

;;; Common fields for all event types.

(defstruct (event :named :predicate)
  name     ; an event has a unique symbol as a name
  kind     ; there are various kinds of events: 'tag, 'axiom, etc.
  prop     ; property list for the event
  number   ; index for event indicates its relative position in history
  access   ; index of first inaccessible event (>= index inaccessible)
  proof    ; (partial) proof for the event
  proven   ; non-nil iff proof for the event is complete
  rawpo    ; "raw: proof obligation
  formula  ; simplified obligation
  details  ; initial proof log (rawpo -> formula)
  browse   ; this slot is used by the proof browser
  ponames  ; names of events in a group with POs (only for group events)
  )

;;; Get the event (structure) associated with the given event name.

(defmacro get-event (event-name)
  `(get ,event-name 'event))


;;; Structure for tag events.

(defstruct (tag (:include event) :named :predicate))

;;; Structure for axiom events.

(defstruct (axiom (:include event) :named :copier :predicate)
  args) ; axiom is implicitly universally quantified using args

;;; Structure for rule events.

(defstruct (rule (:include event) :named :copier :predicate)
  args              ; rewrite rule implicitly universally quantified using args
  renames           ; renaming used when the rewrite rule is applied
  subgoal           ; subgoal for a conditional rewrite rule
  pattern           ; LHS of rewrite rule
  value             ; RHS of rewrite rule
  internal-details  ; proof log for internal axiom
  subbound          ; bound variables in subgoal
  valbound          ; bound variables in RHS
  conditional       ; non-nil iff the rewrite rule is conditional
  permutative       ; non-nil iff the rewrite rule permutes arguments
  index             ; property list where the rule is stored
  enabled)          ; non-nil iff the rewrite rule is enabled

;;; Structure for frule events.

(defstruct (frule (:include event) :named :copier :predicate)
  args              ; frule implicitly universally quantified using args
  renames           ; renaming used when the frule is triggered
  pattern           ; pattern used for triggering the frule
  values            ; formulas asserted when frule is triggered
  negate            ; pattern is negated
  internal-details  ; proof log for internal axiom
  index             ; property list where the frule is stored
  enabled)          ; non-nil iff the frule is enabled

;;; Structure for grule events.

(defstruct (grule (:include event) :named :copier :predicate)
  args              ; grule implicitly universally quantified using args
  renames           ; renaming used when the grule is triggered
  subgoals          ; subgoal for a conditional grule
  pattern           ; pattern used for triggering the grule
  value             ; formula asserted when grule is triggered
  internal-details  ; log for internal axiom
  index             ; property list where the grule is stored
  enabled)          ; non-nil iff the grule is enabled

;;; Structure for function-stub events.

(defstruct (function-stub (:include event) :named :copier :predicate)
  args              ; formal parameters for the function
  type              ; return type (codomain)
  expand            ; non-nil if predefined and expandable
  computable        ; non-nil if potentially computable
  )

;;; Structure for ufunction events (functions).

(defstruct (ufunction (:include event) :named :copier :predicate)
  args              ; formal parameters for the function
  type              ; return type (codomain)
  measure           ; ordinal measure
  body              ; the function body in external form
  unchangeables     ; argument positions of unchangeables (for induction)
  measured-subset   ; measured argument positions (for induction)
  internal-measure  ; internal form of measure
  internal-body     ; the function body in internal form
  body-variables    ; bound variables in function body
  body-details      ; proof log for function body input conversion
  assume-details    ; proof log for assume input conversion
  machine           ; boyer-moore induction machine
  recursive         ; non-nil if function is recursive
  computable        ; non-nil if potentially computable
  enabled)          ; non-nil if function is enabled

;;; Structure for zf-function events.

(defstruct (zf-function (:include event) :named :copier :predicate)
  args              ; formal parameters for the zf-function
  body              ; body for the zf-function declration
  )

(defsubst function-event-p (event)
  (or (ufunction-p event) (function-stub-p event) (zf-function-p event)))

;;; Structure for load events (loading library units).

(defstruct (uload (:include event) :named :copier :predicate)
  unit)  ; name of library unit

;;; Function that determines type of event.

(defun event-type (event)
  (cond ((tag-p event) 'tag)
        ((axiom-p event) 'axiom)
        ((rule-p event) 'rule)
        ((frule-p event) 'frule)
        ((grule-p event) 'grule)
        ((ufunction-p event) 'ufunction)
	((function-stub-p event) 'function-stub)
	((zf-function-p event) 'zf-function)
        ((uload-p event) 'uload)))

;;; Function to access internal details (proof log for conversion
;;; of raw PO to simplified PO).

(defun event-internal-details (event)
  (cond ((ufunction-p event) (ufunction-body-details event))
        ((rule-p event) (rule-internal-details event))
        ((frule-p event) (frule-internal-details event))
        ((grule-p event) (grule-internal-details event))))

;;; NOTE: The following functions produce lists that are not copies.
;;; Altering the lists have serious consequences.

;;; Return a list of all rewrite rules making conclusions about index.

(defmacro get-rules-index (index)
  `(get ,index 'rules))

;;; Return a list of all rules making conclusions about formula.

(defmacro get-rules (formula)
  `(get-rules-index (index-of ,formula)))

;;; Return a list of all frules making conclusions about index.

(defmacro get-frules-index (index)
  `(get ,index 'frules))

;;; Return a list of all frules making conclusions about formula.

(defmacro get-frules (formula)
  `(get-frules-index (index-of ,formula)))

;;; Return a list of all grules making conclusions about index.

(defmacro get-grules-index (index)
  `(get ,index 'grules))

;;; Return a list of all grules making conclusions about formula.

(defmacro get-grules (formula)
  `(get-grules-index (index-of ,formula)))

;;; ========== End of section for events ==========


;;; ---------------------------------------------------------------------
;;; ========================= Section for reduce ========================
;;; ---------------------------------------------------------------------

;;; The prover's workhorse is called "reduce". The structures in
;;; this section are for collecting detailed statistics for reduce
;;; and for collecting top-level information for reduce.

;;; Structure for collecting detailed statistics for reduce.

(defstruct (stat :named (:print-function print-stat-struct))
  (call 0)               ; number of top level calls to reduce
  (effective 0)          ; number of calls that had effect
  (reduce-limit 0)       ; number of times depth limit reached
  (cache-hit 0)          ; number of cache hits
  (cache-miss 0)         ; number of cache misses
  (assume 0)             ; number of assumes
  (deny 0)               ; number of denies
  (lookup 0)             ; number of lookups
  (forward 0)            ; forwards actually performed
  (assumption 0)         ; assumptions actually performed
  (rewrite 0)            ; unconditional rewrites actually performed
  (crewrite 0)           ; conditional rewrites actually performed
  (match-success 0)      ; pattern matches that succeeded
  (match-fail 0)         ; pattern matches that failed
  (ordering 0)           ; number of times rule failed because of ordering
  (instantiate 0)        ; number of times rule failed when instantiating
  (subgoal-limit 0)      ; number of times subgoal limit was reached
  (subgoal-loop 0)       ; number of times subgoal loop was detected
  (subgoal-fail 0)       ; number of times rule failed on subgoal
  (invocation 0)         ; the invocations actually performed
  (suggest-fail 0)       ; number of discarded reduction of recursive call
  (case-analysis 0)      ; case analyses performed
  (normalization 0)      ; normalizations performed
  (apply-fail 0))        ; ineffective reductions of subexpressions

;;; Function to print out detailed statistics for reduce.

(defun print-stat-struct (stat stream depth)
  depth                                         ;avoid warnings
  (format stream "~%~D Reduce calls~
                  ~%~D Effective~
                  ~%~D Depth limits~
                  ~%~D Cache hits~
                  ~%~D Cache misses~
                  ~%~D Assumes~
                  ~%~D Denys~
                  ~%~D Database lookups~
                  ~%~D Forwards~
                  ~%~D Assumptions~
                  ~%~D Unconditional rewrites~
                  ~%~D Conditional rewrites~
                  ~%~D Match successes~
                  ~%~D Match failures~
                  ~%~D Ordering failures~
                  ~%~D Instantiate failures~
                  ~%~D Subgoal limits~
                  ~%~D Subgoal loops~
                  ~%~D Subgoal failures~
                  ~%~D Invoke functions~
                  ~%~D Suggestion failures~
                  ~%~D Case analysis~
                  ~%~D Forced normalizations~
                  ~%~D Apply failures"
          (stat-call stat)
          (stat-effective stat)
          (stat-reduce-limit stat)
          (stat-cache-hit stat)
          (stat-cache-miss stat)
          (stat-assume stat)
          (stat-deny stat)
          (stat-lookup stat)
          (stat-forward stat)
          (stat-assumption stat)
          (stat-rewrite stat)
          (stat-crewrite stat)
          (stat-match-success stat)
          (stat-match-fail stat)
          (stat-ordering stat)
          (stat-instantiate stat)
          (stat-subgoal-limit stat)
          (stat-subgoal-loop stat)
          (stat-subgoal-fail stat)
          (stat-invocation stat)
          (stat-suggest-fail stat)
          (stat-case-analysis stat)
          (stat-normalization stat)
          (stat-apply-fail stat)))


;;; Structure to collect top level information on a reduce.
;;; The structure is saved before each subgoal and restored after failures.
;;; That way anything performed in failed (irrelevant) subgoals are ignored.

(defstruct (proof :named :copier)
  functions          ; list of function names
  rules              ; list of rules
  frules             ; list of frules
  grules             ; list of grules
  instantiations)    ; alist of instantiations

;;; Variable to hold the proof structure.

(defvar *reduce-proof* nil)

;;; Produce a copy of the proof structure (for saving).

(defsubst save-proof ()
  (copy-proof *reduce-proof*))

;;; Restore a previously saved proof structure.

(defsubst restore-proof (proof)
  (setq *reduce-proof* proof))

;;; Add function event to the proof structure (when function is invoked).

(defsubst update-functions (fcn)
  (or (member-eq fcn (proof-functions *reduce-proof*))
      (push fcn (proof-functions *reduce-proof*))))

;;; Add rewrite rule event to the proof structure (when rule is applied).

(defsubst update-rules (rule)
  (or (member-eq rule (proof-rules *reduce-proof*))
      (push rule (proof-rules *reduce-proof*))))

;;; Add frule event to the proof structure (when frule is triggered).

(defsubst update-frules (frule)
  (or (member-eq frule (proof-frules *reduce-proof*))
      (push frule (proof-frules *reduce-proof*))))

;;; Add grule event to the proof structure (when grule is triggered).

(defsubst update-grules (grule)
  (or (member-eq grule (proof-grules *reduce-proof*))
      (push grule (proof-grules *reduce-proof*))))

;;; Execute body with the proof structure initially empty.
;;; Return what body returns plus an updated proof structure.

(defmacro with-proof (&body body)
  `(let ((*reduce-proof* (make-proof)))
     (clear-instantiations)
     (values (progn . ,body)
             (progn (setf (proof-instantiations *reduce-proof*)
                          (get-printable-instantiations))
                    *reduce-proof*))))

;;; ========== End of section for reduce ==========


;;; ---------------------------------------------------------------------
;;; ======================== Section for printer ========================
;;; ---------------------------------------------------------------------


;;; Different printers can be used. However they all work from
;;; s-expressions of the following form:
;;;      ((directive [data]) ...).

;;; The following variable is to be bound to a printer.

(defvar *printer* nil)

;;; List of printer directives.

(defparameter *printer-directives*
  '(
    :space                    ; extra whitespace
    :newline                  ; forced line break
    :paragraph                ; start new paragraph
    :punctuation              ; for !, ?, etc.
    :separator                ; forced line break & full width rule
    :string                   ; break string into words separated by whitespace
    :formula                  ;
    :formula-list             ; separate formulas using newlines
    :event-name
    :event-name-list          ; separate event names using commas and whitespace
    :event
    :command                            ;(prover command)
    :command-list                       ;separated by newlines
    :statement                          ;(Verdi command)
    :statement-list                     ;separate by newlines
    :help-name
    :help-name-list                     ;separate by commas and whitespace
    :syntax                             ;(lisp parameter list)
    :syntax-list                        ;(lisp parameter list)
    :command-name
    :command-name-list                  ;separate by commas and whitespace
    :command-argument
    :command-argument-list))  ;separate by commas and whitespace

;;; Function to check whether or not an s-expression is of the correct
;;; form for printing.

(defun explainp (sexpr)
  (and (not (atom sexpr))
       (every #'(lambda (u)
                  (and (not (atom u))
                       (member-eq (car u) *printer-directives*)))
              sexpr)))

;;; There is a special directive for help messages: :eval.
;;; If (:eval x) appears in a help message, x is evaluated and
;;; replaces (:eval x) before the message is printed.

;;; The following variable can be bound to a function that
;;; performs some conversion to an s-expression for printing.

(defvar *format-output* nil)

;;; ========== End of section for printer ==========


;;; ---------------------------------------------------------------------
;;; ======================== Section for display ========================
;;; ---------------------------------------------------------------------

;;; Structures used to represent the display

;;; At the top level, a proof is represented as a sequence of displays.

;;; Structure for a display.

(defstruct (display (:type vector) :named :copier :predicate)
  (event nil)               ; a display is associated with an event
  (number nil)              ; position in history (sequence of displays)
  (caseof nil)              ; display number and case (or nil or t)
  (command nil)             ; the user command that produced the display
  (explain nil)             ; explanation for the proof command
  (details nil)             ; the complete proof details (proof log)
  (changed nil)             ; status change indicator
  (formula nil)             ; displayed formula in output form
  (internal-aux nil)        ; formula in internal form
  (prover-flags nil))       ; prover flags setting (nil means default)

;;; Structure for proof browsing.

(defstruct (browse :named :copier :predicate)
  (event nil)          ; event associated with proof
  (base-index nil)     ; can be in a case, otherwise nil
  (current-display nil); the current display
  (display-list nil)   ; remaining proof displays
  (at-top-level nil)   ; indicates whether currently at proof command level
  (log nil)            ; remaining log for current display
  (formula nil))       ; current browse formula

;;; ========== End of section for display ==========


