
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


;;; =============== ZK Commands

;;; - Setup for proof commands are defined here.
;;; - The DEFCMD macro is defined in prover-macros.lisp.
;;; - The main objects of proof commands are displays.
;;; - Many of the ZK commands are defined here.
;;; - ZK commands defined elsewhere:
;;;   - Browsing commands are defined in browse.lisp.
;;;   - Cases commands are defined in cases.lisp.
;;;   - Proof checking commands are defined in checker.lisp.
;;;   - Event-related commands are defined in database.lisp.
;;;   - The DUMP-LOG command is defined in generate-log.lisp.
;;;   - The HELP command is defined in help.lisp.
;;;   - Induction commands are defined in induction.lisp.
;;;   - The INSTANTIATE command is defined in instantiate.lisp.
;;;   - The KNUTH-BENDIX command is defined in knuth-bendix.lisp.
;;;   - Library commands are defined in library.lisp.
;;;   - Proof logging commands except DUMP-LOG are defined in logging.lisp.
;;;   - Rearrange commands are defined in rearrange.lisp.
;;;   - Testing commands are defined in testing.lisp
;;; - Declarations are defined in parser.lisp.

;;; -----

;;; Globals and a structure for handling the display.

;;; Set to non-nil to make the prover print the result of a proof command.
(defvar *trace-prover-flag* t)

;;; The result of the last proof command is stored here.
(defvar *current-display* nil)

;;; List of display states representing a proof.
(defvar *display-history* nil)

;;; Clear the current display and the display history.
(defun reset-display ()
  (setq *current-display* nil *display-history* nil))

;;; Generate the internal form of the display's formula.
;;; The transformation of (display-formula display) to its
;;; internal form is logged. Called by simplify, rewrite and
;;; prove-by-cases.
(defun display-internal (display)
  (internal-form (display-formula display) (display-formula-index display)))

;;; Return t if the given event is inaccessible, nil otherwise.
;;; Event being proved and all those after it are inaccessible.
(defun event-inaccessible-p (event)
  (let ((current (and *current-display* (display-event *current-display*))))
    (cond ((null current) nil)		;not proving event, all accessible
	  ((eq event current) t)	;event being proved is inaccessible
	  ((not (< (event-number event) (event-access current))) t))))

;;; Return t if the given symbol is inaccessible, nil otherwise.
(defun symbol-inaccessible-p (symbol)
  (let ((event (get-event symbol)))
    (cond (event (event-inaccessible-p event)) ;inaccessible event
	  ((input-variable-p symbol) nil)      ;variables are accessible
	  (t t))))                             ;undeclared symbol

;;; Return t if any symbol in the formula is inaccessible, nil otherwise.
(defun formula-inaccessible-p (formula)
  (some #'symbol-inaccessible-p (list-of-symbols formula)))

;;; Return t if any subsitution in the substs is inaccessible, nil otherwise.
(defun substitutions-inaccessible-p (substitutions)
  (some #'(lambda (u) (formula-inaccessible-p (cdr u))) substitutions))

;;; Return t if the given event is unmentionable, nil otherwise.
(defun event-unmentionable-p (event)
  (let ((current (and *current-display* (display-event *current-display*))))
    (cond ((null current) nil)		;not proving event, all mentionable
          ((eq (group-event event)
               (group-event current))
           (let ((decl (get-event-property event 'zk-event)))
             (or (null decl)
		 (not (and (eq (car decl) 'function)
			   (ufunction-recursive event))))))
	  ((not (< (event-number event) (event-access current))) t))))

;;; Return t if the given symbol is unmentionable, nil otherwise.
(defun symbol-unmentionable-p (symbol)
  (let ((event (get-event symbol)))
    (cond (event (event-unmentionable-p event))	;unmentionable event
	  ((input-variable-p symbol) nil)
	  (t t))))				;undeclared symbol

;;; Return t if any symbol in the formula is unmentionable, nil otherwise.
(defun formula-unmentionable-p (formula)
  (some #'symbol-unmentionable-p (list-of-symbols formula)))

;;; Return t if any subsitution in the substs is unmentionable, nil otherwise.
(defun substitutions-unmentionable-p (substitutions)
  (some #'(lambda (u) (formula-unmentionable-p (cdr u))) substitutions))


;;; ========================= Displays ===========================


;;; Code for initializing and updating the display.

;;; Write out a display (default *current-display*) using the printer.
;;; When *trace-prover-flag* is nil (e.g., when executing under
;;; with-prover-muzzled), nothing is printed.
(defun write-display (&optional (explain nil) (display *current-display*))
  (when *trace-prover-flag*
    (when explain (printer explain))		;optional explain
    (printer (display-explain display))		;explanation string
    (printer (list (list :formula (display-formula display))))
    (force-output)
    t))

;;; Make the specified display the current display, updating the
;;; display history and clearing the browse of the event being proved.
;;; The display is then printed using write-display.
(defun update-display (display)
  (when (or (display-changed display)
	    (not (equal (display-formula display)
                        (display-formula *current-display*))))
    (push *current-display* *display-history*)	;save for undo and proof
    (setq *current-display* display)
    (write-display)
    (clear-browse (display-event display))
    t))

;;; Continue proof based on a display history.
(defun continue-display (display-history)
  (let ((display (car display-history)))
    (setq *current-display* display
	  *display-history* (cdr display-history))
    (write-display (list (list :string "Continuing proof of")
			 (list :event-name
                               (event-name (display-event display)))
			 (list :string ":")
			 (list :newline)))))

;;; Make the initial display for a proof.
(defun initialize-display (event formula internal)
  (setq *display-history* nil)
  (setq *current-display*
	(make-display :event event
		      :number 0
		      :caseof nil
		      :formula formula
		      :internal-aux internal
		      :details (and event
                                    (append *proof-log* (event-details event)))
		      :command (list 'try
                                     (if event (event-name event) formula))
		      :explain (append
                                (list (list :string "Beginning proof of"))
                                (and event
                                     (list (list :event-name
                                                 (event-name event))))
                                (list (list :string "...")))))
  (write-display))


;;; Additional functions for displays

;;; Return the display in *display-history* with a matching display number.
(defun search-display (display-number)
  (dolist (d (cons *current-display* *display-history*))
    (when (= (display-number d) display-number)
      (return d))))

;;; Return the subhistory with matching display.
(defun search-display-history (display-number history)
  (loop for h on history
        when (= (display-number (car h)) display-number) return h))

;;; ===== Handling of CASES in displays

;;; Given the parent display, return the case kind ('and or 'or)

(defun cases-kind (display)
  (cases-kind-aux (display-formula display)))

(defun cases-kind-aux (formula)
  (cond ((or (and-p formula) (if-p formula)) 'and)
	((or-p formula) 'or)
	((implies-p formula)
	 (cases-kind-aux (implies-right formula)))))

;;; Given the parent display, return the number of cases.

(defun cases-number (display)
  (cases-number-aux (display-formula display)))

(defun cases-number-aux (formula)
  (cond ((if-p formula) 2)
	((and-p formula) (1- (length formula)))
	((or-p formula) (1- (length formula)))
	((implies-p formula)
	 (cases-number-aux (implies-right formula)))))

;;; Given a display, return the index to its formula for the
;;; purpose of proof logging.  The formula has been stripped of
;;; leading universal quantifiers and may be a case instead of
;;; the entire conjecture.  Thus the index is an offset from
;;; the (fully quantified) entire conjecture, into the formula.
(defun display-formula-index (display)
  (display-formula-index-aux
   (unique (list-of-free-variables-unexpanded (display-formula display)))
   (display-base-index display)))

;;; Given that index is an index to a formula closed over vars,
;;; return the index to the "unclosed" formula.
(defun display-formula-index-aux (vars index)
  (if (null vars)
      index
      (display-formula-index-aux (cdr vars) (all-expr-index))))

;;; The base index points to the universal closure of the display's
;;; formula.
(defun display-base-index (display)
  (display-base-index-aux display (cons *current-display* *display-history*)))

(defun display-base-index-aux (display history)
  (let ((case (display-caseof display)))
    (cond
     ((atom case) nil)
     (t (let* ((next-history (search-display-history (first case) history))
               (parent-display (car next-history)))
          (cons (+ (- (cases-number parent-display)
                      (second case))
                   1)
                (display-base-index-aux parent-display next-history)))))))

;;; Given the parent display and the case number, return the formula
;;; for that case.
(defun cases-formula (display case-number)
  (cases-formula-aux (display-formula display) case-number nil))

(defun cases-formula-aux (formula case-number hypotheses)
  (cond ((and-p formula)
	 (let ((n (- (length formula) case-number)))
	   (when (>= n 1)
	     (cases-add-hypotheses (nth n formula) hypotheses))))
        ((or-p formula)
	 (let ((n (- (length formula) case-number)))
	   (when (>= n 1)
	     (cases-add-hypotheses (nth n formula) hypotheses))))
	((if-p formula)
	 (cond ((= case-number 2)
		(cases-add-hypotheses
		  (if-left formula)
		  (cons (if-test formula) hypotheses)))
	       ((= case-number 1)
		(cases-add-hypotheses
		  (if-right formula)
		  (cons (without-proof-logging
                         (negate (if-test formula) nil
				 (make-context-for-bool-p formula nil)))
                        hypotheses)))))
	((implies-p formula)
	 (cases-formula-aux
	   (implies-right formula)
	   case-number
	   (cons (implies-left formula) hypotheses)))))

(defun cases-add-hypotheses (formula hypotheses)
  (if (null hypotheses)
      (if (implies-p formula)
          (without-proof-logging
           (unexpand-formula
            (make-normalized-implies
             (expand-formula (implies-left formula) nil)
             (expand-formula (implies-right formula) nil)
             nil)
            nil))
        formula)
    (without-proof-logging
     (unexpand-formula
      (make-normalized-implies
       (expand-formula (make-conjunction (reverse hypotheses)) nil)
       (expand-formula formula nil)
       nil)
      nil))))

;;; Function to be used to create the initial bool-p context

(defun make-context-for-bool-p-from-parent-display (display)
  (unless (atom (display-caseof display))
    (let* ((caseof (display-caseof display))
	   (parent-display (search-display (first caseof))))
      (let ((num (cases-number parent-display))
	    (kind (cases-kind parent-display))
	    (index (display-base-index parent-display)))
	(list (cons kind
		    (loop for n from num downto 1
			  collect
			  (closed-form (cases-formula parent-display n))))
	      index)))))

(defun make-context-for-bool-p-from-display (display)
  (let* ((formula (display-formula display))
	 (vars (unique (list-of-free-variables-unexpanded formula))))
    (unless (null vars)
      (make-context-for-bool-p
       (make-all (last vars) *true*)
       (cdr (display-formula-index display))))))


;;; Functions for updating and begining a proof.

;;; Update proof status of an event based on *current-display* and
;;; *display-history*. If the current display is associated with an event
;;; then the event gets the entire display history as it proof
;;; and its proven status is set accordingly.
(defun update-proof-status ()
  (when (and *current-display* (display-event *current-display*))
    (let* ((display *current-display*)
	   (event (display-event display))
	   (proof (cons display *display-history*)))
      ;; need to clear any browsing of the event
      (clear-browse event)
      ;; save the proof status flag for the event
      (setf (event-proven event)
	    (and (true-p (display-formula display))	;proven and
		 (null (display-caseof display))))	; no other cases
      ;; save the proof description for the event
      (dolist (ds proof) (setf (display-internal-aux ds) nil))
      (setf (event-proof event) proof))))	;without internal

;;; Begin a new proof or continue a proof.
(defun begin-new-proof (event-or-formula continue-proof-flag)
  (update-proof-status)				;save current proof
  (let* ((event (and (symbolp event-or-formula)
		     (get-event event-or-formula)))
	 (proof (when event (event-proof event)))	;previous proof
	 (proven (when event (event-proven event)))	;already proven?
	 (formula-slot (when event (get (event-type event) 'formula)))
	 (formula (when formula-slot (funcall formula-slot event))))
    ;; events which are assumptions (proven but no proof) cannot be proven
    (cond ((and (null proof) proven) nil)
	  ;; if the flag is set and there is a partial proof just continue it
	  ((and continue-proof-flag (not (null proof)))
           (continue-display proof))
	  ;; if the event has a formula then try that formula
	  ((not (null formula))
           (clear-browse event)
           (let ((*proof-log* nil))
             (initialize-display
              event
              (strip-off-leading-universals
               formula
               (display-formula-index-aux
                (unique (list-of-free-variables-unexpanded formula))
                nil))
              nil)))
	  ((event-p event)
	   nil)
	  ;; otherwise just treat the input as a new unnamed formula
	  (t (reset-display)			;reset accessibility
             (clear-browse nil)
             (when (parse-formula event-or-formula)
               (initialize-display
                nil
                (without-proof-logging
                 (strip-off-leading-universals
                  event-or-formula
                  (display-formula-index-aux
                   (unique
                    (list-of-free-variables-unexpanded event-or-formula))
                   nil)))
                nil))))))


(defparameter *commands-operating-on-closed-form* '(instantiate))

;;; Strip off leading universals of the formula.
;;; For proof logging, record the change in the implicit universal
;;; quantifications.
(defun post-process-formula (display previous-display)
  (cond ((display-changed display)
         (let ((formula (display-formula display))
               (base-index (display-base-index display))
               (init-vars (unique (list-of-free-variables-unexpanded
                                   (display-formula display)))))
           (let ((result (strip-off-leading-universals
                          formula
                          (display-formula-index-aux init-vars base-index))))
             (log-permute-quantifiers
              (append init-vars (list-of-leading-universals formula))
              (unique (list-of-free-variables-unexpanded result))
              base-index)
             result)))
        (t
         (let ((formula (display-formula display))
               (initial-formula
                (cond ((member-eq (car (display-command display))
                                  *commands-operating-on-closed-form*)
                       (universally-quantify
                        (unique
                         (list-of-free-variables-unexpanded
                          (display-formula previous-display)))
                        (display-formula previous-display)))
                      (t (display-formula previous-display))))
               (base-index (display-base-index previous-display)))
           (let ((result (strip-off-leading-universals
                          formula
                          (display-formula-index-aux
                           (unique (list-of-free-variables-unexpanded formula))
                           base-index)))
                 (init-vars
                  (unique (list-of-free-variables-unexpanded initial-formula)))
                 (leading-vars (list-of-leading-universals formula))
                 (intermediate-vars
                  (unique (list-of-free-variables-unexpanded formula))))
             (log-delete-quantifiers
              (append init-vars leading-vars)
              (append intermediate-vars
                      (list-of-free-variables-unexpanded result))
              base-index)
             (when (> (length init-vars) (length intermediate-vars))
	       (cond
		(intermediate-vars nil)
		((bool-p formula)
		 (push-proof-log 'is-boolean base-index t))
		((not (null base-index))
		 (let ((bool-p (make-context-for-bool-p-from-parent-display
				previous-display)))
		   (log-remove-coercion-from-boolean-context
		    bool-p base-index)))
		(t (setq result (make-if result *true* *false*)))))
             (let* ((post-vars (unique (list-of-free-variables-unexpanded
                                        result)))
                    (pre-vars (remove-if-not
                               #'(lambda (u) (member-eq u post-vars))
                               (append init-vars leading-vars))))
               (unless (and (null (set-difference-eq pre-vars post-vars))
                            (null (set-difference-eq post-vars pre-vars)))
                 (format
                  *error-output*
                  "~%Free variable disagreement in post-process-formula.")
		 (format
		  *error-output*
		  "~%Pre: ~S, Post ~S" pre-vars post-vars)
		 (format
		  *error-output*
		  "~%Command: ~A" (display-command display))
		 )
               (log-permute-quantifiers pre-vars post-vars base-index))
             result)))))

;;; Logging the deletions of implicit quantifications (some free variables
;;; may have disappeared, which correspond to the deletions).

(defun log-delete-quantifiers (vars freevars index)
  (let ((current-vars vars))
    (dolist (var vars)
      (unless (member-eq var freevars)
	(log-flip-universals-reverse
	 (- (length current-vars) (length (member-eq var current-vars)))
	 index)
	(push-proof-log 'remove-universal index)
	(when (>= (length current-vars) 2)
          (push-proof-log 'is-boolean index t))
	(setq current-vars (remove-eq var current-vars))))))

;;; Logging the permutation of implicit quantifications.

(defun log-permute-quantifiers (init-vars final-vars index)
  (when final-vars
    (log-flip-universals-reverse
     (- (length final-vars)
	(length (member-eq (car final-vars) init-vars)))
     index)
    (log-permute-quantifiers
     (remove-eq (car final-vars) init-vars)
     (cdr final-vars)
     (all-expr-index))))


;;; ==================== Commands ====================


;;; ----- Commands to start, continue, restart and go back in proofs.

;;; Start or continue a proof.
(defcmd try (event-or-formula)
  ((:string "Start the proof of")
   (:command-argument event-or-formula)
   (:string "by making it current.  If")
   (:command-argument event-or-formula)
   (:string "is the name of some event, the event's")
   (:help-name proof-obligation)
   (:string "is made current.  Otherwise it must be a formula,
in which case it is made the current formula.  Should any
error occur, then")
   (:command-name try)
   (:string "will not have any
effect.  If a proof of an event is already in progress, its partial proof
will be saved so it may be continued later.  If an event is tried
which has previously been tried then its partial proof is resumed
from the point it was left.  If no")
   (:command-argument event-or-formula)
   (:string "is supplied to")
   (:command-name try)
   (:string "then the user is given a menu of unproven events."))
  (update-proof-status)				;need latest status
  (begin-new-proof event-or-formula
		   t))				;continue existing proof

(defcmd try-next-untried ()
  ((:string "Call")
   (:command-name try)
   (:string "on the oldest untried proof in the database."))
  (update-proof-status)				;need the latest status
  (try (first (select-noproof-events))))

;;; Go back 1 proof command.
(defcmd back (&optional number-of-steps)
  ((:string "Return the prover to the state prior to the last
proof step. You may give the command the number of steps you
want to be undone (which defaults to 1).  If the given number
is greater than the number of steps in the proof,")
   (:command-name back)
   (:string "returns to the beginning of the current proof.  If there was no
previous state then")
   (:command-name back)
   (:string "has no effect."))
  (when (null number-of-steps) (setq number-of-steps 1))
  (when (and *display-history*
             (integerp number-of-steps)
             (> number-of-steps 0))
    ;; if we have something to back up to then ...
    (do ((step 1 (1+ step)))
	((or (> step number-of-steps) (null *display-history*))
	 (write-display (list (list :newline)
			      (list :string "Returning to :"))))
      (setq *current-display* (pop *display-history*)))
    (clear-browse (display-event *current-display*))))

;;; Go back until just before the specified proof command.
(defcmd back-thru (command-name)
  ((:string "Return the prover to the state prior to the proof step
specified if the step exists."))
  (when (symbolp command-name)
    (loop for display-list on (if *current-display*
				  (cons *current-display* *display-history*)
				*display-history*)
	  when (eq (car (display-command (car display-list))) command-name)
	  do (setq *current-display* (cadr display-list)
		   *display-history* (cddr display-list))
          (clear-browse (display-event *current-display*))
          (unless (null *current-display*)
                  (write-display (list (list :newline)
                                       (list :string "Returning to :"))))
          (return command-name))))

;;; Go back until just after the specified proof command.
(defcmd back-to (command-name)
  ((:string "Return the prover to the state after the proof step
specified if the step exists."))
  (when (symbolp command-name)
    (loop for display-list on (if *current-display*
				  (cons *current-display* *display-history*)
				*display-history*)
	  when (eq (car (display-command (car display-list))) command-name)
	  do (setq *current-display* (car display-list)
		   *display-history* (cdr display-list))
          (clear-browse (display-event *current-display*))
          (write-display (list (list :newline)
                               (list :string "Returning to :")))
          (return command-name))))

;;; Go back to the beginning.
(defcmd retry (&optional event-or-formula)
  ((:string "Start the proof of")
   (:command-argument event-or-formula)
   (:string "by making it current. If")
   (:command-argument event-or-formula)
   (:string "is the name of some event, its formula is made
current.  Any previous partial proof associated with the event is
discarded, though confirmation is requested if the previous proof
had already been completed.  If no")
   (:command-argument event-or-formula)
   (:string "is supplied to")
   (:command-name retry)
   (:punctuation ",")
   (:string "
then the current proof is deleted.  Should any error occur, then")
   (:command-name retry)
   (:string "will not have any effect."))
  (cond ((null event-or-formula) (back (length *display-history*)))
	(t (update-proof-status)		;the latest status
	   (let* ((event (and (symbolp event-or-formula)
			      (get-event event-or-formula)))
		  (proven (when event (event-proven event))))
	     (when (or (not proven)		;not event or not proven
		       (yes-or-no-p
			"Do you really want to discard the completed proof? "))
	       (begin-new-proof event-or-formula nil)))))) ;discard old proof


;;; ----- Commands to print various information.


(defcmd get-formula ()
  ((:string "Return a copy of the current prover formula."))
  (unless (null *current-display*)
    (copy-tree (display-formula *current-display*))))

(defcmd print-formula ()
  ((:string "Print the current subformula, unless there is no
current subformula (which is the case immediately after you reset or
introduce a declaration that does not have a proof obligation)."))
  (unless (null *current-display*)
    (write-display (list (list :string "The current subformula is :")
			 (list :newline)))))

(defcmd clear-stats ()
  ((:string "Clear the statistic collection counters for the prover.
Normally, statistics are collected continuously from the time the
system is loaded."))
  (setq *reduce-statistics* (make-stat))
  nil)

(defcmd print-stats (&optional stream)
  ((:string "Display all of the statistic collection counters for the
prover. If")
   (:command-argument stream)
   (:string "is provided, then the statistics are
printed to that stream.  The counters run continuously from the
time the system is loaded; however, they may be cleared using
the")
   (:command-name clear-stats)
   (:string "command."))
  (print *reduce-statistics* stream)
  nil)


;;; bind this to your custom display struct to list converter
(defvar *format-display* nil)

;;; use this for converting commands to the sexpr representation
(defun format-display (display-struct)
  (funcall (or *format-display* #'lisp-format-display) display-struct))

;;; returns the printable form of display-struct
;;; this is the default for *format-display* in header

(defun lisp-format-display (display-struct)
  (let ((command (display-command display-struct)))
    (lisp-format-modifiers
     (reverse (display-prover-flags display-struct))
     (cons (car command)
	   (mapcar #'(lambda (x) (list 'quote x)) (cdr command))))))

(defun lisp-format-modifiers (modifiers expr)
  (cond ((null modifiers) expr)
	(t (let ((modifier (caar modifiers))
		 (value (cdar modifiers)))
	     (cond ((eq modifier :subexpression)
		    `(with-subexpression
		       (',value)
		       ,(lisp-format-modifiers (cdr modifiers) expr)))
		   ((eq modifier :instantiate)
		    (if (null value)
			`(without-instantiation
			   ,(lisp-format-modifiers (cdr modifiers) expr))
			`(with-instantiation
			   ,(lisp-format-modifiers (cdr modifiers) expr))))
		   ((eq modifier :case-analysis)
		    (if (null value)
			`(without-case-analysis
			   ,(lisp-format-modifiers (cdr modifiers) expr))
		      `(with-case-analysis
			,(lisp-format-modifiers (cdr modifiers) expr))))
		   ((eq modifier :disable)
		    `(with-disabled
		      (',value)
		      ,(lisp-format-modifiers (cdr modifiers) expr)))
		   ((eq modifier :enable)
		    `(with-enabled
		      (',value) ,(lisp-format-modifiers (cdr modifiers) expr)))
		   ((eq modifier :disabled)
		    `(disabled ,(lisp-format-modifiers (cdr modifiers) expr)))
		   ((eq modifier :normalization)
		    (if (null value)
			`(without-normalization
			   ,(lisp-format-modifiers (cdr modifiers) expr))
		      `(with-normalization
			,(lisp-format-modifiers (cdr modifiers) expr))))
		   (t (lisp-format-modifiers (cdr modifiers) expr)))))))

;;; print the given display with the requested level of detail
(defun print-proof-aux (display detail-level &optional indent)
  ;;(when (and (integerp detail-level) (> detail-level 0))
  ;;  (printer '((:newline))))
  (printer (list (list :command (format-display display)))
	   t indent)
  (when (integerp detail-level)
    (when (> detail-level 0)
      (printer (display-explain display) t indent))
    (when (> detail-level 1)
      (printer (list (list :formula (display-formula display))) t indent))))

(defcmd print-proof (&optional event-name detail-level)
  ((:string "Display a complete or partial proof.  If")
   (:command-argument event-name)
   (:string "is supplied,
it prints the proof associated with")
   (:command-argument event-name)
   (:punctuation ".")
   (:string "Otherwise, it
prints the current proof.  Normally, only the proof step commands
are printed.  This corresponds to a")
   (:command-argument detail-level)
   (:string "of 0.  If the
level is set to 1, then the commands and the proof explanations
are printed.  A")
   (:command-argument detail-level)
   (:string "of 2 prints the commands, the
explanation, and the resulting intermediate formulas."))
  (update-proof-status)				;save current proof
  (mapc #'(lambda (u) (print-proof-aux u detail-level))
	(if (null event-name)
	    (when *current-display*
	      (reverse (cons *current-display* *display-history*)))
	    (let ((event (when (symbolp event-name) (get-event event-name))))
	      (when event (reverse (event-proof event))))))
  (printer '((:newline)))
  nil)

(defun print-event-proof (event-name detail-level indent)
  (update-proof-status)				;save current proof
  (mapc #'(lambda (u) (print-proof-aux u detail-level indent))
	(if (null event-name)
	    (when *current-display*
	      (reverse (cons *current-display* *display-history*)))
	    (let* ((event (when (symbolp event-name) (get-event event-name))))
	      (when event (reverse (event-proof event))))))
  (printer '((:newline)))
  nil)

(defcmd print-status (&key (assumed nil) (proven t) (unproven t) (tried nil)
			   (untried nil))
  ((:string "Display the the name of the current formula being proven, and
lists all of the events in the current database which have the
given status.  By default, the")
   (:command-argument proven)
   (:string "and")
   (:command-argument unproven)
   (:string "events are
listed, but the")
   (:command-argument assumed)
   (:punctuation ",")
   (:command-argument tried)
   (:string "and")
   (:command-argument untried)
   (:string "events may also be
listed in any combination by using the appropriate keywords."))
  (update-proof-status)				;save current status
  (printer (list (list :newline)
		 (list :newline)
		 (list :string "Currently proving:")
		 (cond ((null *current-display*) (list :string "Nothing"))
		       (t (let ((event (display-event *current-display*)))
			    (if (null event)
				(list :string "An unnamed formula")
				(list :event-name (event-name event))))))))
  (when assumed
    (printer (list (list :newline)
		   (list :newline)
		   (list :string "Assumed formula list:")
		   (list :event-name-list
			 (intersection-eq (select-proven-events)
					  (select-noproof-events))))))
  (when proven
    (let ((proven-list (intersection-eq (select-proven-events)
					(select-proof-events))))
      (printer (list (list :newline)
		     (list :newline)
		     (list :string "Proven formula list:")
		     (if (null proven-list)
			 (list :string "Nothing")
			 (list :event-name-list proven-list))))))
  (when unproven
    (let ((unproven-list (select-unproven-events)))
      (printer (list (list :newline)
		     (list :newline)
		     (list :string "Unproven formula list:")
		     (if (null unproven-list)
			 (list :string "Nothing")
			 (list :event-name-list unproven-list))))))
  (when tried
    (printer (list (list :newline)
		   (list :newline)
		   (list :string "Tried formula list:")
		   (list :event-name-list
			 (intersection-eq (select-unproven-events)
					  (select-proof-events))))))
  (when untried
    (printer (list (list :newline)
		   (list :newline)
		   (list :string "Untried formula list:")
		   (list :event-name-list
			 (intersection-eq (select-unproven-events)
					  (select-noproof-events)))))))

;;; ----- Trivial Reduction Commands

(defcmd trivial-rewrite (:display)
  ((:string "Apply enabled and accessible unconditional rewrite rules
to the current subformula in addition to performing all the things that")
   (:command-name trivial-simplify)
   (:string "does."))
  (multiple-value-bind (result list-of-rules)
      (uc-rewrite-formula (internal-form (display-formula display) index)
                          nil index)
    (when (not (null list-of-rules))		;success
      (make-display :formula
		    (output-form
		     result index
		     (make-context-for-bool-p-from-display display))
		    :explain (list (list :string "Trivially rewrites using")
				   (list :event-name-list
                                         (mapcar #'rule-name list-of-rules))
				   (list :string "to ..."))))))

(defcmd trivial-simplify (:display)
  ((:string "Perform a simple tautology check and propositional
simplification on the current subformula. Neither equality reasoning
nor integer reasoning
is performed, nor does the theorem prover try variable instantiations.
No use of frules and grules."))
  (let* ((formula (internal-form (display-formula display) index))
	 (result (ls-simplify-formula
                  formula nil nil index
		  (when (not (null index))
		    (make-all
		     (unique (list-of-free-variables-unexpanded formula))
		     formula))
		  nil)))
    (when (not (equal result formula))
      (make-display :formula
		    (output-form
		     result index
		     (make-context-for-bool-p-from-display display))
		    :explain (list (list :string
                                         "Trivially simplifies to ..."))))))

(defcmd trivial-reduce (:display)
  ((:string "Replace function applications using the functions'
definitions for non-recursive functions that are enabled and accessible,
in addition to performing all the things that")
   (:command-name trivial-simplify)
   (:string "does."))
  (let ((formula (internal-form (display-formula display) index)))
    (multiple-value-bind (result list-of-names)
      (tr-reduce-formula formula index)
      (when (not (null list-of-names))
        (make-display :formula
		      (output-form
		       result index
		       (make-context-for-bool-p-from-display display))
                      :explain (list (list :string "Invoking")
                                     (list :event-name-list
                                           (mapcar #'name-name list-of-names))
                                     (list :string "gives ...")))))))


;;; ----- Full Reduction Commands


;;; given a proof as returned by reduce generate a suitable
;;; string to print out which describes how the proof was obtained
(defun make-display-explain (proof &optional extra-explain)
  (append (list (list :string "Which simplifies"))
	  (and (proof-functions proof)
	       (list (list :newline)
		     (list :string "with invocation of")
		     (list :event-name-list
                           (mapcar #'ufunction-name (proof-functions proof)))))
	  (and (proof-rules proof)
	       (list (list :newline)
		     (list :string "when rewriting with")
		     (list :event-name-list
                           (mapcar #'rule-name (proof-rules proof)))))
	  (and (proof-frules proof)
	       (list (list :newline)
		     (list :string "forward chaining using")
		     (list :event-name-list
                           (mapcar #'frule-name (proof-frules proof)))))
	  (and (proof-grules proof)
	       (list (list :newline)
		     (list :string "with the assumptions")
		     (list :event-name-list
                           (mapcar #'grule-name (proof-grules proof)))))
	  (and (proof-instantiations proof)
	       (list (list :newline)
		     (if (> (length (proof-instantiations proof)) 1)
			 (list :string "with the instantiations")
			 (list :string "with the instantiation"))
		     (list :formula-list
                           (mapcar #'(lambda (u) (list '= (car u) (cdr u)))
                                   (proof-instantiations proof)))))
	  extra-explain				;optional extra-explain
	  (list (list :string "to ..."))))


;;; The simplify command.
(defcmd simplify (:display)
  ((:string "Simplify the current formula.  This may perform the
substitution of equalities as well as trying to instantiate
variables in order to find a proof."))
  (multiple-value-bind (result success proof)
      (simplify-formula (display-formula display)
                        (display-internal display)
                        index)
      (when success (make-display :formula
				  (output-form
				   result index
				   (make-context-for-bool-p-from-display
				    display))
				:explain (make-display-explain proof)))))

;;; The rewrite command.
(defcmd rewrite (:display)
  ((:string "Perform simplification and rewriting on the current
subformula. This command applies rewrite rules that match and
whose conditions are satisfied."))
  (multiple-value-bind (result success proof)
      (rewrite-formula (display-formula display)
		       (display-internal display)
		       index)
      (when success (make-display :formula
				  (output-form
				   result index
				   (make-context-for-bool-p-from-display
				    display))
				:explain (make-display-explain proof)))))

;;; The most powerful of the reduction commands.
(defcmd reduce (:display)
  ((:string "Reduce the current subformula. The reduction
consists of simplification, rewriting, and replacement of
function applications using their definitions. The")
    (:command-name reduce)
    (:string "command is the most powerful of the automatic
proof commands."))
  (multiple-value-bind (result success proof)
      (let ((subexpression-modifier
             (get-subexpression-modifier *current-modifiers*)))
        (reduce-formula (display-formula display)
                        (internal-form (display-formula display) index)
                        index))
      (when success (make-display :formula
				  (output-form
				   result index
				   (make-context-for-bool-p-from-display
				    display))
                                :explain (make-display-explain proof)))))

;;; The default prove command.
(defvar *default-prove-command* 'reduce)

(defcmd prove (&optional event-or-formula)
  ((:string "Call the default proof command.  Currently, this is")
   (:command-name reduce)
   (:punctuation "."))
  (funcall *default-prove-command* event-or-formula))


;;; ----- Simple Transformation Commands.


;;; Label a subexprssion.
(defcmd label (label-expression :display)
  ((:string "Label the given expression with a label of the prover's
choosing. The label replaces the expression everywhere in the current
subformula and a hypothesis stating the equality between the label
and the expression is added to the current subformula.  This can be
useful for reducing the clutter caused by repeated large
subexpressions."))
  (when (and (not (atom label-expression))
             (not (intersection-eq
                   (list-of-free-variables-unexpanded label-expression)
                   (list-of-bound-variables-unexpanded
                    (display-formula display))))
             ;; label expression with bound vars of formula
	     (expr-occurs label-expression (display-formula display)))
    ;; in order to generate the label we create an internal variable of
    ;; the proper type, then convert it to output form avoiding used vars
    (let* ((label (ungenvar (genvar '|)X|)
			    (list-of-all-variables (display-formula display))))
	   (orig (display-formula display))
	   (formula (make-if (make-= label label-expression)
                             (subst-equal label label-expression orig)
                             *true*)))
      (log-label index label label-expression)
      ;; (if (some (var) (= var expr)) formula (true))
      (let ((bool-p (make-context-for-bool-p-from-display display)))
	(log-coerce-expr-for-boolean-or-bool-p orig (if-left-index) bool-p)
	(log-all-uncase-analysis-2
	 (make-if (make-some-single label (make-= label label-expression))
		  (make-if orig *true* *false*)
		  *true*)
	 index))
      (log-equality-substitute
       orig label-expression label (cons 2 (all-expr-index)))
      (make-display :formula
                    (output-form
                     (expand-formula (make-all-single label formula) index)
                     index
		     (make-context-for-bool-p-from-display display))
                    :explain (list (list :string "Labelling")
                                   (list :formula label-expression)
                                   (list :string "gives ..."))))))

;;; Transform formula to (IF predicate formula fornula).
(defcmd split (predicate :display)
  ((:string "Perform a case split on the current formula with the supplied")
   (:command-argument predicate)
   (:punctuation ".")
   (:string "This results in a new formula of the form")
   (:formula (if predicate formula formula))
   (:punctuation ",")
   (:string "
provided there are no references to the quantified variables of
the formula within the predicate.  If there are,")
   (:command-name split)
   (:string "performs
a case split on the largest subformulas within the scope of the
referenced quantified variables. In effect, a case split causes the current
formula to be worked on under the two cases: the first with the
predicate explicitly assumed; and the second with the predicate
explicitly denied.")
   (:paragraph)
   (:command-name split)
   (:string "may also be used for placing a specific hypothesis before
a subexpression. This proof step may be required because of
the sensitivity of the prover towards the ordering of subexpressions within
the formula being reduced (see")
   (:help-name reduction)
   (:punctuation ").") (:newline) (:newline)
   (:string "Example:") (:newline) (:newline)
   (:string "Beginning proof of ...") (:newline)
   (:formula (implies (all (i j k) (p i j k)) (all (l m n) (q l m n))))
   (:newline) (:newline)
   (:command (split '(= m 0))) (:newline) (:newline)
   (:string "Splitting on")
   (:formula (= m 0))
   (:string "generates ...")
   (:formula (implies (all (i j k) (p i j k))
		      (all (l m) (if (= m 0)
                                   (all (n) (q l m n))
                                 (all (n$0) (q l m n$0)))))))
  (let ((predicate (without-proof-logging (parse-formula-phase-1 predicate))))
    (unless (or (null predicate)
                (formula-unmentionable-p predicate))
      ;; we don't want the if form since we want to preserve the structure
      ;; but do need it expanded since the output-form routines depend on it
      (let* ((expanded (internal-form-phase-1 (display-formula display) index))
	     ;; attempt split
	     (result (split-formula predicate expanded index)))
	(unless (or (null result)
                    (equal result expanded))		;split failed?
	  (let ((*unnormalize-if-form-flag* nil)
		(*uncase-analysis-form-flag* nil))
	    (make-display :formula
			  (output-form
			   result index
			   (make-context-for-bool-p-from-display display))
			  :explain (list (list :string "Splitting on")
					 (list :formula predicate)
					 (list :string "generates ...")))))))))

(defun split-formula (test form index)
  (let ((quantified-vars (unique (list-of-bound-variables form)))
	(free-vars-in-test (unique (list-of-free-variables-unexpanded test))))
    (when (subset-p free-vars-in-test
                    (unique (list-of-all-variables form)))
      (let ((symbol-clash-list
             (intersection-eq quantified-vars free-vars-in-test)))
        (split-formula-recursively test form symbol-clash-list index)))))

(defun split-formula-recursively (test form clash-list index)
  (cond ((null clash-list)
	 (push-proof-log 'if-equal index test t)
	 (make-if (rename-quantified-variables test (if-test-index))
                  form
                  form))
	((all-p form)
	 (make-all (all-vars form)
		   (split-formula-recursively
                    test
                    (all-expr form)
                    (remove-eq (all-var form) clash-list)
                    (cons 2 index))))
	((some-p form)
	 (make-some (some-vars form)
		    (split-formula-recursively
                     test
                     (some-expr form)
                     (remove-eq (some-var form) clash-list)
                     (cons 2 index))))
	((consp form)
	 (loop for expr in form
	       for number = 0 then (+ 1 number)
	       collect (split-formula-recursively
                        test expr clash-list (cons number index))))
	(t form)))

;;; Transform formula to
;;; (AND (IMPLIES predicate formula) (OR predicate formula)).
(defcmd suppose (predicate :display)
  ((:string "Convert the current formula to a conjunction of two cases.
The first case is an implication with the")
   (:command-argument predicate)
   (:string "as a hypothesis and the current formula as a conclusion.
The second case is a disjunction of the")
   (:command-argument predicate)
   (:string "and the current formula."))
  (let ((predicate (without-proof-logging (parse-formula-phase-1 predicate))))
    (unless (or (null predicate)
                (formula-unmentionable-p predicate))
      ;; we don't want the if form since we want to preserve the structure
      ;; but do need it expanded since the output-form routines depend on it
      (let ((result (suppose-formula
		     predicate (display-formula display) index
		     (make-context-for-bool-p-from-display display))))
	(unless (null result)
          (make-display :formula result
                        :explain (list (list :string "Supposing")
                                       (list :formula predicate)
                                       (list :string "generates ..."))))))))

(defun suppose-formula (predicate formula index bool-p)
  (when (and (subset-p (unique (list-of-free-variables-unexpanded predicate))
                       (unique (list-of-free-variables-unexpanded formula)))
             (or (bool-p formula) bool-p))
    (when *record-proof-logs-flag*
      (let ((result (make-and (make-implies predicate formula)
                              (make-or predicate formula))))
	(cond ((bool-p formula) (log-convert-boolean-to-coerced formula index))
	      (t
	       (let ((vars (last (unique (list-of-free-variables-unexpanded
					  formula)))))
		 (log-coerce-all-expr-to-bool vars (cdr index)))))
        (push-proof-log
	 'if-equal index `(= (if ,formula (true) (false)) ,result) t)
        (push-proof-log 'look-up (if-left-index) result)
        ;; (if (= (if formula (true) (false))
        ;;        (and (implies predicate formula) (or predicate formula)))
        ;;     (and (implies predicate formula) (or predicate formula))
        ;;     formula)
        (log-suppose-formula-aux predicate formula (cons 2 (if-test-index)))
        ;; (if (= (if formula (true) (false)) (if formula (true) (false)))
        ;;     (and (implies predicate formula) (or predicate formula))
        ;;     formula)
        (push-proof-log 'compute (if-test-index))
        (push-proof-log 'if-true index)))
    (make-and (make-implies predicate formula)
              (make-or predicate formula))))

;;; Log transformation of
;;; (and (implies predicate formula) (or predicate formula)) to
;;; (if formula (true) (false))

(defun log-suppose-formula-aux (predicate formula index)
  predicate formula
  (push-proof-log 'syntax (cons 1 index))
  (push-proof-log 'syntax (cons 2 index))
  (push-proof-log 'syntax index)
  ;; (if (if predicate (if formula (true) (false)) (true))
  ;;     (if (if predicate (true) (if formula (true) (false)))
  ;;         (true)
  ;;         (false))
  ;;     (false))
  (push-proof-log 'case-analysis index 1)
  (push-proof-log 'look-up (list* 1 1 2 (if-left-index)) *true*)
  (push-proof-log 'if-true (list* 1 2 (if-left-index)))
  (push-proof-log 'if-true (cons 2 (if-left-index)))
  (push-proof-log 'if-true (if-right-index))
  ;; (if predicate
  ;;     (if (if formula (true) (false)) (true) (false))
  ;;     (if (if predicate (true) (if formula (true) (false)))
  ;;         (true)
  ;;         (false))
  (push-proof-log 'case-analysis (if-left-index) 1)
  (push-proof-log 'if-true (cons 2 (if-left-index)))
  (push-proof-log 'if-false (cons 3 (if-left-index)))
  ;; (if predicate
  ;;     (if formula (true) (false))
  ;;     (if (if predicate (true) (if formula (true) (false)))
  ;;         (true)
  ;;         (false))
  (push-proof-log 'case-analysis (if-right-index) 1)
  (push-proof-log 'if-true (cons 2 (if-right-index)))
  (push-proof-log 'case-analysis (cons 3 (if-right-index)) 1)
  (push-proof-log 'if-true (list* 2 3 (if-right-index)))
  (push-proof-log 'if-false (list* 3 3 (if-right-index)))
  ;; (if predicate
  ;;     (if formula (true) (false))
  ;;     (if predicate (true) (if formula (true) (false))))
  (log-double-negate-test '(true) `(if ,formula (true) (false))
                          (if-right-index))
  ;; (if predicate
  ;;     (if formula (true) (false))
  ;;     (if (if (if predicate (false) (true)) (false) (true))
  ;;         (true)
  ;;         (if formula (true) (false))))
  (push-proof-log 'look-up (list* 1 1 (if-right-index)) *true*)
  (push-proof-log 'if-true (cons 1 (if-right-index)))
  (push-proof-log 'if-false (if-right-index))
  ;; (if predicate
  ;;     (if formula (true) (false))
  ;;     (if formula (true) (false)))
  (push-proof-log 'if-equal index)
  )

;;; Transform (IMPLIES h c) to (OR (NOT h) c).
(defcmd contradict (:display)
  ((:string "Transform an implication to a disjunction of the negated
hypothesis and the conclusion.  We can then use the")
   (:command-name cases)
   (:string "command so that we can work on the negated hypothesis
separately.  This may be useful if we have a contradictory hypothesis.
For example, if we have an existentially quantified conclusion, after an")
   (:command-name instantiate)
   (:punctuation ",")
   (:string "the instantiated conclusion is typically negated and moved to
the hypothesis part.  A")
   (:command-name contradict)
   (:string "followed by")
   (:command-name cases)
   (:string "will allow us to ignore the uninstantiated conclusion."))
  (let ((formula (display-formula display)))
    (when (implies-p formula)
      (let ((hyp (implies-left formula))
            (conc (implies-right formula)))
        (push-proof-log 'syntax index)
        ;; (if hyp (if conc (true) (false)) (true))
        (log-double-negate-test `(if ,conc (true) (false))
                                '(true) index)
        (push-proof-log 'case-analysis index 1)
        ;; (if (if hyp (false) (true))
        ;;     (if (false) (if conc (true) (false)) (true))
        ;;     (if (true) (if conc (true) (false)) (true)))
        (push-proof-log 'if-false (if-left-index))
        (push-proof-log 'if-true (if-right-index))
        (push-proof-log 'syntax (if-test-index) t)
        (push-proof-log 'syntax index t)
        ;; (or (not hyp) conc)
        (make-display :formula `(or (not ,hyp) ,conc)
                      :explain
                      (list (list :string "Concluding")
                            (list :formula hyp)
                            (list :string "generates ...")))))))

;;; Move universals out.
(defcmd prenex (&optional variables :display)
  ((:string "Move quantifiers out if they become universal at the top level.
If the optional list")
   (:command-argument variables)
   (:string "is given, then only quantifications on")
   (:command-argument variables)
   (:string "are moved out."))
  (let* ((internal (internal-form (display-formula display) index))
	 (outside-vars (unique (list-of-free-variables-unexpanded internal)))
	 (bool-p (when outside-vars
		   (make-context-for-bool-p
		    (make-all-single (car (reverse outside-vars)) *true*)
		    (cdr index))))
	 (result (prenex-all internal variables bool-p index)))
    (when (not (equal result internal))
      (make-display :formula
		    (output-form
		     result index
		     (make-context-for-bool-p-from-display display))
		    :explain (list (list :string "Prenexing produces ..."))))))


;;; ----- Commands that bring axioms manually.

;;; Transform formula to (IMPLIES axiom formula).
(defcmd assume (event-name &optional instantiations :display)
  ((:string "Add the axiom associated with")
   (:command-argument event-name)
   (:string "to the current subformula as
a hypothesis.  This results in a new subformula of the form")
   (:newline)
   (:formula (implies |assumption| |subformula|))
   (:newline) (:newline)
   (:string "You may optionally supply an instantiation list, in
which case the axiom is instantiated before assumed. The")
   (:command-name assume)
   (:string "command is most often used to bring in axioms
declared without any heuristics. You also may use it to
bring in axioms declared using")
   (:command-name rule) (:punctuation ",")
   (:command-name frule) (:string "or") (:command-name grule)
   (:string "explicitly.")
   (:newline) (:newline)
   (:string "Example:") (:newline) (:newline)
   (:command (axiom 'lemma-1 '(i j k) '(p i j k))) (:newline) (:newline)
   (:command (try '(p 0 m 1))) (:newline) (:newline)
   (:string "Beginning proof of ...") (:newline)
   (:formula (p 0 m 1)) (:newline) (:newline)
   (:command (assume 'lemma-1 '((= i 0) (= j m)))) (:newline) (:newline)
   (:string "Assuming")
   (:event-name lemma-1)
   (:string "with the instantiations:")
   (:formula-list ((= i 0) (= j m)))
   (:string "generates ...")
   (:formula (implies (all (k) (p 0 m k)) (p 0 m 1))))
  (let* ((name (car (true-name event-name)))
         (kind (cdr (true-name event-name)))
         (event (when (symbolp name) (get-event name)))
         (assumption
          (and event
               (cond ((eq kind 'po)
                      (and (not (event-inaccessible-p event))
                           (or (eq name 'div) (eq name 'rem) (eq name 'mod)
                               (eq name 'epsilon-induction)
                               (ufunction-p event)
                               (not (null (event-rawpo event))))
                           (list
                            (unique
                             (list-of-free-variables-unexpanded
                              (event-formula event)))
                            (event-formula event))))
                     ((and (get-event-property event 'zk-event)
                           (not (event-inaccessible-p event))
                           (or (axiom-p event) (rule-p event)
                               (frule-p event) (grule-p event))
                           (not (equal (zk-internal-variables
                                         (fourth (get-event-property
                                                  event 'zk-event)))
                                       (event-formula event))))
                      (setq name
                            (intern (string-append (string name) ".PO")
				    *zk-package*))
                      (list (unique (list-of-free-variables-unexpanded
                                     (event-formula event)))
                            (event-formula event)))
                     (t (let ((assume-slot (get (event-type event)
                                                'assume)))
                          (and (not (null assume-slot)) ;assumable?
                               (not (event-inaccessible-p event))
                               (or (axiom-p event) (rule-p event)
                                   (frule-p event) (grule-p event)
				   (ufunction-p event))
                               (funcall assume-slot event)))))))
         (subexpression-modifier
          (get-subexpression-modifier *current-modifiers*)))
    (when assumption
      (let ((args (car assumption)) (formula (cadr assumption))
            (expr (if (and subexpression-modifier
                           (eq (car subexpression-modifier) :subexpression))
                      (cdr subexpression-modifier)
                    (display-formula display))))
        (unless (null assumption)
          (cond ((null instantiations)  ;nothing to instantiate
                 (let ((result (assume-recursively
                                args formula nil nil
                                (display-formula display)
                                expr event-name index
				(make-context-for-bool-p-from-display
				 display))))
                   (when (not (equal result (display-formula display)))
		     (make-display :formula result
				   :explain
                                       (explain-assume event-name nil)))))

                ;; here we have some instantiations to perform
                ;; but first we have to check them for any possible errors
                (t (let ((substs (assume-parse-instantiations
                                  instantiations args))
                         (vars-in-instantiations
                          (unique
                           (loop for equality in instantiations
                                 append (list-of-free-variables-unexpanded
                                         (=-right equality)))))
                         (vars-in-formula
                          (unique (list-of-free-variables-unexpanded
                                   (display-formula display)))))
                     (when (and substs
                                (not (substitutions-unmentionable-p substs)))
                       (let ((result (assume-recursively
                                      args formula substs
                                      (set-difference-eq
                                       vars-in-instantiations
                                       vars-in-formula)
                                      (display-formula display)
                                      expr event-name index
				      (make-context-for-bool-p-from-display
				       display))))
                         (when (not (equal result (display-formula display)))
			   (make-display :formula result
					 :explain
					 (explain-assume
                                              event-name
                                              instantiations)))))))))))))

(defun assume-recursively
    (args assumed substs out-vars formula expr event-name index bool-p)
  (cond ((equal formula expr)
         (if (null out-vars)
             (let ((internal (internal-form formula index)))
               (assume-formula args assumed substs internal event-name index
			       bool-p))
           formula))
        ((atom formula) formula)
        ((all-p formula)
         (make-all (all-vars formula)
                   (assume-recursively
                     args assumed substs
                     (set-difference-eq out-vars (all-vars formula))
                     (all-expr formula)
                     expr event-name (all-expr-index)
		     (make-context-for-bool-p formula index))))
        ((some-p formula)
         (make-some (some-vars formula)
                    (assume-recursively
                      args assumed substs
                      (set-difference-eq out-vars (some-vars formula))
                      (some-expr formula)
                      expr event-name (some-expr-index)
		      (make-context-for-bool-p formula index))))
	((if-p formula)
	 (make-if (assume-recursively
		   args assumed substs (if-test formula) out-vars expr
		   event-name (if-test-index)
		   (make-context-for-bool-p formula index))
		  (assume-recursively
		   args assumed substs (if-left formula) out-vars expr
		   event-name (if-left-index) bool-p)
		  (assume-recursively
		   args assumed substs (if-right formula) out-vars expr
		   event-name (if-right-index) bool-p)))
	(t
	 (let ((bool-p (make-context-for-bool-p formula index)))
	   (cons (car formula)
                 (loop for subformula in (cdr formula)
                     for number = 1 then (+ number 1)
                     collect (assume-recursively
                              args assumed substs out-vars subformula expr
                              event-name (cons number index) bool-p)))))))

(defun explain-assume (event-name instantiations)
  (append `((:string "Assuming") (:event-name ,event-name))
	  (when instantiations
	    `((:string "with the instantiations:")
              (:formula-list ,instantiations)))
	  `((:string "generates ..."))))

(defun assume-formula (args assumed substs current event-name index bool-p)
  (let ((name (car (true-name event-name)))
        (kind (cdr (true-name event-name)))
        (event (get-event event-name)))
    (let ((assume-name
           (cond ((eq kind 'po) event-name)
                 ((ufunction-p event)
		  (intern (string-append (string name) ".DEFINITION")
			  *zk-package*))
                 (t event-name))))
      (log-use-axiom index assume-name)
      (let* ((quantified (universally-quantify args assumed))
             (expanded (expand-formula quantified (if-test-index)))
             (renamed (rename-quantified-variables expanded (if-test-index))))
        (cond ((null substs)
               (output-form (make-if renamed current *true*) index bool-p))
              (t (let* ((renamed-substs
                         (renamed-substitutions args substs renamed))
                        (rearranged
                         (move-out-vars (mapcar #'car renamed-substs)
                                        renamed bool-p (if-test-index))))
                   (linearize-and-log-universal-instantiations
                    (mapcar #'(lambda (u) (make-= (car u) (cdr u)))
                            renamed-substs)
                    (if-test-index))
                   (move-out-vars (list-of-leading-universals renamed)
                                  rearranged bool-p
				  (cons 2 (if-test-index)))
                   (log-unrenames expanded renamed (cons 2 (if-test-index)))
                   (log-unexpands quantified (cons 2 (if-test-index)))
                   (push-proof-log
                    'use-axiom (cons 2 (if-test-index)) assume-name t)
		   (log-remove-bool-coercion-from-if-test index)
                   (output-form
                    (make-if
                     (sublis-eq renamed-substs
                                (remove-instantiated-quantifiers
                                 args substs renamed))
                     current
                     *true*)
                    index bool-p))))))))

(defun remove-instantiated-quantifiers (args substs formula)
  (cond ((null args) formula)
        ((assoc-eq (car args) substs)
         (remove-instantiated-quantifiers
          (cdr args) substs (all-expr formula)))
        (t (make-all (all-vars formula)
                     (remove-instantiated-quantifiers
                      (cdr args) substs (all-expr formula))))))

(defun renamed-substitutions (args substs formula)
  (let ((arg-substs (argument-substitutions args formula)))
    (mapcar #'(lambda (u) (cons (sublis-eq arg-substs (car u)) (cdr u)))
            substs)))

(defun argument-substitutions (args formula)
  (cond ((null args) nil)
        (t (cons (cons (car args) (all-var formula))
                 (argument-substitutions (cdr args) (all-expr formula))))))

(defun assume-parse-instantiations (instantiations arglist)
  (when (without-errors (nil)
	  (cond ((atom instantiations)
		 (parse-error 'instantiations-ill-formed instantiations))
		((not (every #'(lambda (u)
                                 (and (=-p u)
                                      (variable-p (=-left u))
                                      (member-eq (=-left u) arglist)))
			     instantiations))
		 (parse-error 'instantiations-ill-formed instantiations))
		((not (= (length (unique (mapcar #'=-left instantiations)))
			 (length instantiations)))
		 (parse-error 'instantiations-has-duplicates instantiations))))
    (let ((internal-instantiations
           (mapcar #'(lambda  (u) (parse-formula (=-right u)))
                   instantiations)))
      (unless (some #'null internal-instantiations)
        (without-proof-logging
         (mapcar #'(lambda (u v)
                     (cons (=-left u) (rename-quantified-variables v nil)))
                 instantiations internal-instantiations))))))

;;; Transform formula to (AND axiom formula).
(defcmd add (event-name &optional instantiations :display)
  ((:string "Add the axiom associated with")
   (:command-argument event-name)
   (:string "to the current subformula as
a conjunct.  This results in a new subformula of the form")
   (:newline)
   (:formula (and |assumption| |formula|))
   (:newline) (:newline)
   (:string "You may optionally supply an instantiation list, in
which case the axiom is instantiated before added. The")
   (:command-name add)
   (:string "command is the dual of the")
   (:command-name assume)
   (:string "command."))
  (let* ((name (car (true-name event-name)))
         (kind (cdr (true-name event-name)))
         (event (when (symbolp name) (get-event name)))
         (assumption
          (and event
               (cond ((eq kind 'po)
                      (and (not (event-inaccessible-p event))
                           (or (eq name 'div) (eq name 'rem) (eq name 'mod)
                               (eq name 'epsilon-induction)
                               (ufunction-p event)
                               (not (null (event-rawpo event))))
                           (list
                            (unique
                             (list-of-free-variables-unexpanded
                              (event-formula event)))
                            (event-formula event))))
                     ((and (get-event-property event 'zk-event)
                           (not (event-inaccessible-p event))
                           (or (axiom-p event) (rule-p event)
                               (frule-p event) (grule-p event))
                           (not (equal (zk-internal-variables
                                         (fourth (get-event-property
                                                  event 'zk-event)))
                                       (event-formula event))))
                      (setq name
                            (intern (string-append (string name) ".PO")
				    *zk-package*))
                      (list (unique (list-of-free-variables-unexpanded
                                     (event-formula event)))
                            (event-formula event)))
                     (t (let ((assume-slot (get (event-type event)
                                                'assume)))
                          (and (not (null assume-slot)) ;assumable?
                               (not (event-inaccessible-p event))
                               (or (axiom-p event) (rule-p event)
                                   (frule-p event) (grule-p event)
                                   (ufunction-p event))
                               (funcall assume-slot event)))))))
         (subexpression-modifier
          (get-subexpression-modifier *current-modifiers*)))
    (when assumption
      (let ((args (car assumption)) (formula (cadr assumption))
            (expr (if (and subexpression-modifier
                           (eq (car subexpression-modifier) :subexpression))
                      (cdr subexpression-modifier)
                    (display-formula display))))
        (unless (null assumption)
          (cond ((null instantiations)  ;nothing to instantiate
                 (let ((result (add-recursively
                                args formula nil nil
                                (display-formula display)
                                expr event-name index)))
                   (when (not (equal result (display-formula display)))
		     (make-display :formula
				   (output-form
				    result index
				    (make-context-for-bool-p-from-display
				     display))
				   :explain
                                       (explain-add event-name nil)))))

                ;; here we have some instantiations to perform
                ;; but first we have to check them for any possible errors
                (t (let ((substs (assume-parse-instantiations
                                  instantiations args))
                         (vars-in-instantiations
                          (unique
                           (loop for equality in instantiations
                                 append (list-of-free-variables-unexpanded
                                         (=-right equality)))))
                         (vars-in-formula
                          (unique (list-of-free-variables-unexpanded
                                   (display-formula display)))))
                     (when (and substs
                                (not (substitutions-unmentionable-p substs)))
                       (let ((result (add-recursively
                                      args formula substs
                                      (set-difference-eq
                                       vars-in-instantiations
                                       vars-in-formula)
                                      (display-formula display)
                                      expr event-name index)))
                         (when (not (equal result (display-formula display)))
			   (make-display :formula
					 (output-form
					  result index
					  (make-context-for-bool-p-from-display
					   display))
					 :explain
                                             (explain-add
                                              event-name
                                              instantiations)))))))))))))

(defun add-recursively
  (args assumed substs out-vars formula expr event-name index)
  (cond ((equal formula expr)
         (if (null out-vars)
             (let ((internal (internal-form formula index)))
               (add-formula args assumed substs internal event-name index))
           formula))
        ((atom formula) formula)
        ((all-p formula)
         (make-all (all-vars formula)
                   (add-recursively
                     args assumed substs
                     (set-difference-eq out-vars (all-vars formula))
                     (all-expr formula)
                     expr event-name (all-expr-index))))
        ((some-p formula)
         (make-some (some-vars formula)
                    (add-recursively
                      args assumed substs
                      (set-difference-eq out-vars (some-vars formula))
                      (some-expr formula)
                      expr event-name (some-expr-index))))
        (t (cons (car formula)
                 (loop for subformula in (cdr formula)
                     for number = 1 then (+ number 1)
                     collect (add-recursively
                              args assumed substs out-vars subformula expr
                              event-name (cons number index)))))))

(defun explain-add (event-name instantiations)
  (append `((:string "Adding") (:event-name ,event-name))
	  (when instantiations
	    `((:string "with the instantiations:")
              (:formula-list ,instantiations)))
	  `((:string "generates ..."))))

(defun add-formula (args assumed substs current event-name index)
  (let ((name (car (true-name event-name)))
        (kind (cdr (true-name event-name)))
        (event (get-event event-name)))
    (let ((assume-name
           (cond ((eq kind 'po) event-name)
                 ((ufunction-p event)
		  (intern (string-append (string name) ".DEFINITION")
			  *zk-package*))
                 (t event-name))))
      (let ((quantified (universally-quantify args assumed)))
        (push-proof-log 'if-true index *false* t)
	;; (if (true) formula (false))
        (push-proof-log 'use-axiom (if-test-index) assume-name)
	;; (if axiom formula (false))
        (let* ((expanded (expand-formula quantified (if-test-index)))
               (renamed (rename-quantified-variables
                         expanded (if-test-index))))
          (cond ((null substs)
                 (output-form (make-if renamed current *false*) index))
                (t (let* ((renamed-substs
                           (renamed-substitutions args substs renamed))
                          (rearranged
                           (move-out-vars (mapcar #'car renamed-substs)
                                          renamed nil
					  (if-test-index))))
                     (linearize-and-log-universal-instantiations
                      (mapcar #'(lambda (u) (make-= (car u) (cdr u)))
                              renamed-substs)
                      (if-test-index))
                     (move-out-vars (list-of-leading-universals renamed)
                                    rearranged nil (cons 2 (if-test-index)))
                     (log-unrenames expanded renamed (cons 2 (if-test-index)))
                     (log-unexpands quantified (cons 2 (if-test-index)))
                     (push-proof-log
                      'use-axiom (cons 2 (if-test-index)) assume-name t)
		     (log-remove-bool-coercion-from-if-test index)
                     (output-form
                      (make-if
                       (sublis-eq renamed-substs
                                  (remove-instantiated-quantifiers
                                   args substs renamed))
                       current
                       *false*)
                      index)))))))))


;;; Replace function application in formula with the appropriate instance
;;; of the function's definition.
(defcmd invoke (function-or-expression :display)
  ((:string "Replace function applications wherever it occurs
within the current subformula.  The replacement used for")
   (:command-name invoke)
   (:string "is always the original
definition, not some normalized form of it.")
   (:command-name invoke)
   (:string "works for functions which have
been disabled. ")
   (:command-name invoke)
   (:string "may be applied to an expression
rather than to a function, in which case it works like a selective
invoke in that occurrences of the expression in the formula are
replaced using the function's definition.") (:newline) (:newline)
   (:string "Example:") (:newline) (:newline)
   (:command (name 'plus-abs '(i j) 'int nil nil '(+ (abs i) (abs j))))
   (:newline) (:newline)
   (:command (try '(= k (* (plus-abs i 3) (plus-abs j 4)))))
   (:newline) (:newline)
   (:string "Beginning proof of ...") (:newline)
   (:formula (= k (* (plus-abs i 3) (plus-abs j 4)))) (:newline) (:newline)
   (:command (invoke '(plus-abs j 4))) (:newline) (:newline)
   (:string "Invoking")
   (:formula (plus-abs j 4))
   (:string "gives ...") (:newline)
   (:formula (= k (* (plus-abs i 3) (+ (abs j) (abs 4))))) (:newline) (:newline)
   (:command (invoke 'plus-abs)) (:newline) (:newline)
   (:string "Invoking")
   (:event-name plus-abs)
   (:string "gives ...") (:newline)
   (:formula (= k (* (+ (abs i) (abs 3)) (+ (abs j) (abs 4))))))
  (let ((result (invoke-formula function-or-expression
                                (internal-form (display-formula display) index)
                                index)))
    (when result (make-display
		  :formula
		  (output-form
		   result index
		   (make-context-for-bool-p-from-display display))
		  :explain
		  (list (list :string "Invoking")
			(list (if (symbolp function-or-expression)
				  :event-name
				:formula)
			      function-or-expression)
			(list :string "gives ..."))))))


(defun invoke-formula (function-or-expression formula index)
  (let ((event (when (symbolp function-or-expression)
                 (get-event function-or-expression))))
    ;; must be a defined name which is called
    (cond ((and (ufunction-p event)
		(not (event-inaccessible-p event))
		(calls-p function-or-expression formula))
	   (push-proof-log 'marker index '(point 1))
	   (let ((res
		  (invoke-formula-recursively event formula index)
		  ))
	     (push-proof-log 'marker index '(point 2))
	     res)
	   )
	  (t (expand-expr-in-formula function-or-expression formula index)))))

;;; recursively invoke the name event in the formula
(defun invoke-formula-recursively (event formula index)
  (cond ((atom formula) formula)
	(t (let ((formula
                  (loop for expr in formula
                      for number = 0 then (+ 1 number)
                      collect
                        (invoke-formula-recursively event expr
                                                    (cons number index)))))
	     (invoke-single-name event formula index)))))

(defun invoke-single-name (name formula index)
  (cond ((neq (ufunction-name name) (car formula)) formula)
	(t (log-use-axiom index (internal-name (ufunction-name name)))
           (let* ((right-index (cons 2 (repeat-all-expr-index
                                        (length (ufunction-args name))
                                        (if-test-index))))
                  (renamed (conditionally-rename-quantified-variables
                            (ufunction-body-variables name)
                            (ufunction-internal-body name)
                            right-index)))
             (log-rewrite (make-if (make-series-of-quantification
                                    'all
                                    (ufunction-args name)
                                    (make-= (cons (ufunction-name name)
                                                  (ufunction-args name))
                                            renamed))
                                   formula
                                   *true*)
                          (mapcar #'make-= (ufunction-args name) (cdr formula))
                          index)
             (log-unrenames (ufunction-internal-body name) renamed right-index)
             (push-proof-log 'use-axiom (if-test-index)
                             (internal-name (ufunction-name name)) t)
             (push-proof-log 'if-true index)
             (sublis-eq (pairlis (ufunction-args name) (cdr formula))
                        renamed)))))

(defun expand-expr-in-formula (expr formula index)
  (let ((event (and (consp expr)
                    (symbolp (first expr))
                    (get-event (first expr)))))
    (when (and (ufunction-p event)
	       (not (event-inaccessible-p event))
	       (ufunction-internal-body event))
      (let ((parsed-expr (parse-formula expr)))
	(when (and parsed-expr (expr-occurs parsed-expr formula))
          (expand-expr-in-formula-recursively
           event parsed-expr formula index))))))

(defun expand-expr-in-formula-recursively (name expression formula index)
  (cond ((equal expression formula)
         (invoke-single-name name expression index))
        ((atom formula) formula)
        (t (loop for expr in formula
               for number = 0 then (+ 1 number)
               collect
                 (expand-expr-in-formula-recursively name expression expr
                                                     (cons number index))))))

;;; Manually apply the specified rewrite rule.
(defcmd applyf (rule &optional expr :display)
  ((:string "Apply a rewrite rule to the current subformula.
All subexpressions that match the rule's pattern are rewritten using
the rule.  If the rewrite rule is conditional, the rule is applied
as though it was an unconditional rule, but with the replacing
expression being an")
   (:event-name if)
   (:string "expression with the condition as the test,
the actual replacing expression of the rule as the")
   (:event-name left)
   (:string "part, and the pattern of the rule as the")
   (:event-name right)
   (:string "part.")
   (:paragraph)
   (:command-name applyf)
   (:string "can be used on rewrite rules that have
been disabled.  An optional expression may be supplied to the")
   (:command-name applyf)
   (:string "command, in which case only occurrences of the
expression in the subformula are rewritten.  The expression must
match the rewrite rule.") (:newline) (:newline)
   (:string "Example:") (:newline) (:newline)
   (:command (rule 'plus-abs-definition '(i j)
	       '(= (plus-abs i j) (+ (abs i) (abs j)))))
   (:newline) (:newline)
   (:command (try '(= k (* (plus-abs i 3) (plus-abs j 4)))))
   (:newline) (:newline)
   (:string "Beginning proof of ...") (:newline)
   (:formula (= k (* (plus-abs i 3) (plus-abs j 4)))) (:newline) (:newline)
   (:command (applyf 'plus-abs-definition '(plus-abs j 4)))
   (:newline) (:newline)
   (:string "Applying")
   (:event-name plus-abs-definition)
   (:string "to") (:newline)
   (:formula (plus-abs j 4))
   (:string "gives ...") (:newline)
   (:formula (= k (* (plus-abs i 3) (+ (abs j) (abs 4))))) (:newline) (:newline)
   (:command (applyf 'plus-abs-definition)) (:newline) (:newline)
   (:string "Applying")
   (:event-name plus-abs-definition)
   (:string "gives ...") (:newline)
   (:formula (= k (* (+ (abs i) (abs 3)) (+ (abs j) (abs 4))))))
  (let ((result
         (apply-rule-formula rule expr
                             (internal-form (display-formula display) index)
                             index)))
    (when result (make-display
		  :formula
		  (output-form
		   result index
		   (make-context-for-bool-p-from-display display))
		  :explain `((:string "Applying")
			     (:event-name ,rule)
			     ,@(unless (null expr)
				 `((:string "to") (:newline)
				   (:formula ,expr)))
			     (:string "gives ..."))))))

(defun apply-rule-formula (rule-name expr formula index)
  (let ((event (and (symbolp rule-name) (get-event rule-name))))
    (when (and (rule-p event)
	       (not (event-inaccessible-p event))
               (atom (rule-conditional event))
	       (calls-p (car (rule-pattern event)) formula))	; optimization
      (apply-rule-formula-recursively event formula expr index))))

(defun apply-rule-formula-recursively (event formula expr index)
  (cond ((atom formula) formula)
        ((equal formula expr)
         (apply-single-rule-formula event formula index))
	(t (let ((formula
                  (loop for subformula in formula
                      for number = 0 then (+ 1 number)
                      collect
                        (apply-rule-formula-recursively event subformula expr
                                                        (cons number index)))))
             (cond ((or (null expr) (equal formula expr))
                    (apply-single-rule-formula event formula index))
                   (t formula))))))

(defun apply-single-rule-formula (rule formula index)
  (multiple-value-bind
      (substitutions match-success)
      (match-pattern-formula (rule-pattern rule) formula) ;perform match
    (if match-success
        (cond ((not (rule-conditional rule))
               (log-use-axiom index (internal-name (rule-name rule)))
               (let* ((right-index (cons 2 (repeat-all-expr-index
                                            (length (rule-args rule))
                                            (if-test-index))))
                      (renamed (conditionally-rename-quantified-variables
                                (rule-valbound rule)
                                (rule-value rule)
                                right-index))
                      (unrenames (mapcar #'(lambda (x)
                                             (cons (cdr x) (car x)))
                                         (rule-renames rule)))
                      (unrenamed-substitutions
                       (mapcar #'(lambda (x)
                                   (make-= (binding-of (car x) unrenames)
                                           (cdr x)))
                               (reorder-substitutions
                                substitutions
                                ;;(sublis-eq (rule-renames rule)
                                ;;           (rule-args rule))
				(mapcar #'cdr (rule-renames rule))
				))))
                 (log-rewrite
                  (make-if (make-series-of-quantification
                            'all
                            (mapcar #'=-left unrenamed-substitutions)
                            (sublis-eq unrenames
                                       (make-= (rule-pattern rule) renamed)))
                           formula
                           *true*)
                  unrenamed-substitutions
                  index)
                 (log-unrenames (rule-value rule) renamed right-index)
                 (push-proof-log 'use-axiom (if-test-index)
                                 (internal-name (rule-name rule)) t)
                 (push-proof-log 'if-true index)
                 (sublis-eq substitutions renamed)))
              (t (let ((right-index (cons 2 (repeat-all-expr-index
                                             (length (rule-args rule))
                                             (if-test-index)))))
                   (log-use-axiom index (internal-name (rule-name rule)))
                   (let* ((renamed-subgoal
                           (conditionally-rename-quantified-variables
                            (rule-subbound rule)
                            (rule-subgoal rule)
                            (cons 1 right-index)))
                          (renamed-value
                           (conditionally-rename-quantified-variables
                            (rule-valbound rule)
                            (rule-value rule)
                            (cons 2 right-index)))
                          (unrenames (mapcar #'(lambda (x)
                                                 (cons (cdr x) (car x)))
                                             (rule-renames rule)))
                          (unrenamed-substitutions
                           (mapcar #'(lambda (x)
                                       (make-= (binding-of (car x) unrenames)
                                               (cdr x)))
                                   (reorder-substitutions
                                    substitutions
                                    ;;(sublis-eq (rule-renames rule)
                                    ;;           (rule-args rule))
				    (mapcar #'cdr (rule-renames rule))
				    ))))
                     (log-rewrite
                      (make-if (make-series-of-quantification
                                'all
                                (mapcar #'=-left unrenamed-substitutions)
                                (sublis-eq
                                 unrenames
                                 (make-= (rule-pattern rule)
                                         (make-if renamed-subgoal
                                                  renamed-value
                                                  (rule-pattern rule)))))
                               formula
                               *true*)
                      unrenamed-substitutions
                      index)
                     (log-unrenames (rule-value rule)
                                    renamed-value
                                    (cons 2 right-index))
                     (log-unrenames (rule-subgoal rule)
                                    renamed-subgoal
                                    (cons 1 right-index))
                     (push-proof-log 'use-axiom (if-test-index)
                                     (internal-name (rule-name rule)) t)
                     (push-proof-log 'if-true index)
                     (make-if (sublis-eq substitutions renamed-subgoal)
                              (sublis-eq substitutions renamed-value)
                              formula)))))
      formula)))

;;; ----- Command for simple equality reasoning.

(defvar *substitution* nil)

(defcmd equality-substitute (&optional expression :display)
  ((:string "Substitute, for")
   (:command-argument expression)
   (:punctuation ",")
   (:string "its equal in appropriate contexts of the current
subformula. The expression must appear as the left or right side
of an equality within the current subformula. The resulting
subformula is equivalent to the original. You may use the")
   (:command-name equality-substitute)
   (:string "command without supplying a value for")
   (:command-argument expression)
   (:punctuation ",")
   (:string "in which case a heuristic is used to
substitute equalities automatically.")
   (:newline) (:newline)
   (:string "Example:") (:newline) (:newline)
   (:command (try '(implies (all (i j k) (p i j k))
		    (all (l m) (if (= m 0)
				 (all (n) (q l m n))
			       (all (n0) (q l m n0)))))))
   (:newline) (:newline)
   (:command (equality-substitute 'm)) (:newline) (:newline)
   (:string "Substituting")
   (:formula (= m 0))
   (:string "produces ...") (:newline)
   (:formula (implies (all (i j k) (p i j k))
		      (all (l m) (if (= m 0)
				   (all (n) (q l 0 n))
				 (all (n0) (q l m n0)))))))
  (let* ((internal (internal-form (display-formula display) index))
         (result (equality-substitute-formula expression internal index)))
    (when (not (equal result internal))
      (make-display :formula
		    (output-form
		     result index
		     (make-context-for-bool-p-from-display display))
		    :explain
		    `((:string "Substituting")
		      (:formula-list ,(reverse (unique *substitution*)))
		      (:string "produces ..."))))))

(defun equality-substitute-formula (expression formula index)
  (let ((normalized-formula
         (ls-simplify-formula
	  formula nil nil index
	  (when (not (null index))
	    (make-context-for-bool-p
	     (make-all (last (unique (list-of-free-variables-unexpanded
				      formula)))
		       *true*)
	     (cdr index)))
	  nil)))
    (setq *substitution* nil)
    (if (null expression)
	(equality-substitute-heuristically normalized-formula index)
	(equality-substitute-recursively
         expression normalized-formula index))))

;;; The next three routines heuristically substitute equalities in a formula.
;;; The substitutions are done outermost first.

;;; The top level for heuristically substituting equalities.

(defun equality-substitute-heuristically (formula index)
  (cond ((atom formula) formula)
	((if-p formula)
	 (let ((test (equality-substitute-heuristically
                      (if-test formula) (if-test-index))))
	   (make-if test
		    (equality-substitute-heuristically-left
                     test (if-left formula) index)
		    (equality-substitute-heuristically
                     (if-right formula) (if-right-index)))))
	(t (loop for expr in formula
               for number = 0 then (+ 1 number)
               collect (equality-substitute-heuristically
                        expr (cons number index))))))

;;; If the test is an equality, choose the side to be substituted for,
;;; perform the substitutions on left, and traverse it.  Otherwise, just
;;; traverse left.

(defun equality-substitute-heuristically-left (test left index)
  (if (=-p test)
      (let* ((test-left (=-left test))
	     (test-right (=-right test))
	     (expression (equality-substitute-heuristically-choose
                          test-left test-right)))
        (cond ((and expression (expr-occurs expression left))
               (log-equality-substitute left
                                        expression
                                        (if (equal expression test-left)
                                            test-right
                                          test-left)
                                        (if-left-index))
               (push (make-= expression
                             (if (equal test-left expression)
                                 test-right
                                 test-left))
		*substitution*)
               (equality-substitute-heuristically
                (if (equal test-left expression)
                    (subst-equal test-right test-left left)
                    (subst-equal test-left test-right left))
                (if-left-index)))
              (t (equality-substitute-heuristically left (if-left-index)))))
      (equality-substitute-heuristically left (if-left-index))))

;;; Decide whether to substitute left for right or right for left.

(defun equality-substitute-heuristically-choose (left right)
  (cond ((literal-p right) left)
	((literal-p left) right)
	((constant-p right) left)
	((constant-p left) right)
	(t (let ((left-size (size-of left))
		 (right-size (size-of right)))
	     (cond ((< right-size left-size)
		    (if (expr-occurs right left) left right))
		   ((< left-size right-size)
		    (if (expr-occurs left right) right left))
		   (t nil))))))

;;; Top level to substitute for expression in appropriate contexts of formula.

(defun equality-substitute-recursively (expression formula index)
  (cond ((atom formula) formula)
	((if-p formula)
	 (let ((test (equality-substitute-recursively
                      expression (if-test formula) (if-test-index))))
	   (make-if test
		    (equality-substitute-recursively-left
                     expression test (if-left formula) index)
		    (equality-substitute-recursively
                     expression (if-right formula) (if-right-index)))))
	(t (loop for expr in formula
               for number = 0 then (+ 1 number)
               collect (equality-substitute-recursively
                        expression expr (cons number index))))))

;;; If the test is an equality involving the expression on one side, then
;;; substitute for all occurrences of the expression in left, the other side
;;; of the equality.  Otherwise, left must be traversed.

(defun equality-substitute-recursively-left (expression test left index)
  (if (=-p test)
      (let ((test-left (=-left test))
	    (test-right (=-right test)))
	(cond ((equal test-left expression)
               (cond ((expr-occurs expression left)
                      (log-equality-substitute left
                                               expression
                                               test-right
                                               (if-left-index))
                      (push test *substitution*)
                      (subst-equal test-right test-left left))
                     (t left)))
	      ((equal test-right expression)
               (cond ((expr-occurs expression left)
                      (log-equality-substitute left
                                               expression
                                               test-left
                                               (if-left-index))
                      (push (make-= expression test-left) *substitution*)
                      (subst-equal test-left test-right left))
                     (t left)))
	      (t (equality-substitute-recursively
                  expression left (if-left-index)))))
      (equality-substitute-recursively expression left (if-left-index))))


;;; ----- Feature combining command.

(defcmd prove-by-cases (:display)
  ((:string "Try to prove the current subformula by proving each
of its cases. If the subformula is a conjunction or disjunction then
each case is attempted independently.
The final result is a conjunction or disjunction of the results.
No information is shared among the cases.  If the subformula is
neither a conjunction nor a disjunction then")
   (:command-name prove-by-cases)
   (:string "is
equivalent to")
   (:command-name prove)
   (:punctuation "."))
  (let ((formula (display-formula display)))
    (cond ((or (or-p formula) (and-p formula))
	   (multiple-value-bind
	    (result success proof)
	    (prove-by-cases-loop formula index)
	     (when success
	       (make-display
                :formula result
                :explain (make-display-explain
                          proof
                          (list (list :string
                                      "thus prove-by-cases reduces")))))))
	  (t (multiple-value-bind
	      (result success proof)
	      (reduce-formula (display-formula display)
			      (display-internal display)
			      index)
	      (when success
		(make-display
		 :formula
		 (output-form result index
			      (make-context-for-bool-p-from-display display))
		 :explain (make-display-explain proof))))))))

(defun prove-by-cases-loop (formula index)
  (let ((type (car formula))
	(cases (cdr formula)))
    (loop with (final-result final-success final-proof)
	  for case in cases
	  for n = 1 then (1+ n)
	  do (multiple-value-bind (result success proof)
		 (prove-by-cases-single-case n case (cons n index))
	       (setq final-result (cons result final-result)
		     final-success (or success final-success)
		     final-proof (join-proofs proof final-proof)))
	     (printer '((:string "--------")))
	  finally
	    (return				;return collected result
	      (values (prove-by-cases-result type (reverse final-result) index)
		      final-success
		      final-proof)))))

(defun prove-by-cases-single-case (number formula index)
  (printer `((:string ,(format nil "Case ~D :" number))))
  (printer (list (list :formula formula)))
  (let ((pre-proof-log (save-proof-log)))
    (multiple-value-bind (result success proof)
        (reduce-formula formula (internal-form formula index) index)
      (cond ((not success)
             (restore-proof-log pre-proof-log)
             (values formula nil nil))
            (t (let ((output-formula (output-form result index)))
                 (cond ((equal formula output-formula)
                        (restore-proof-log pre-proof-log)
                        (values formula nil nil))
                       (t (printer (make-display-explain proof))
                          (printer (list (list :formula output-formula)))
                          (values output-formula t proof)))))))))

(defun prove-by-cases-result (type results index)
  (case type					;conjunction/disjuction
    (or (loop with tmp = nil
	      with i = 1
	      with n = (length results)
            for expr in results
            do (cond ((true-p expr)
		      (log-or-true i n index)
                      (return *true*))
                     ((false-p expr)
		      (log-or-false i n index)
		      (decf n))
                     (t (incf i) (push expr tmp)))
            finally (cond ((null tmp)
                           (log-or-0 index)
                           (return *false*))
                          ((null (cdr tmp))
                           (log-or-1 index)
                           (return (coerce-to-bool (car tmp) index)))
                          (t (return (cons 'or (reverse tmp)))))))
    (and (loop with tmp = nil
	       with i = 1
	       with n = (length results)
             for expr in results
             do (cond ((false-p expr)
		       (log-and-false i n index)
                       (return *false*))
                      ((true-p expr)
		       (log-and-true i n index)
		       (decf n))
                      (t (incf i) (push expr tmp)))
             finally (cond ((null tmp)
                            (log-and-0 index)
                            (return *true*))
                           ((null (cdr tmp))
                            (log-and-1 index)
                            (return (coerce-to-bool (car tmp) index)))
                           (t (return (cons 'and (reverse tmp)))))))))

;;; given any two proofs return a proof containing both
;;; in the case of instantiations the result could be ambiguous
(defun join-proofs (proof-1 proof-2)
  (make-proof :functions
	      (unique (append (and proof-1 (proof-functions proof-1))
			      (and proof-2 (proof-functions proof-2))))
	      :rules (unique (append (and proof-1 (proof-rules proof-1))
				     (and proof-2 (proof-rules proof-2))))
	      :frules (unique (append (and proof-1 (proof-frules proof-1))
				      (and proof-2 (proof-frules proof-2))))
	      :grules (unique (append (and proof-1 (proof-grules proof-1))
				      (and proof-2 (proof-grules proof-2))))
	      :instantiations
	      (unique (append (and proof-1 (proof-instantiations proof-1))
			      (and proof-2 (proof-instantiations proof-2))))))

;;; ----- Normal Form Commands.

;;; Convert formulas into conjunctive/disjunctive normal form.

(defcmd conjunctive (:display)
  ((:string "Transform the current subformula into conjunctive
normal form. You might find this useful in conjunction with the
CASES mechanism."))
  (let ((result (conjunctive-normal-form
		 (display-formula display) index
		 (make-context-for-bool-p-from-display display))))
    (unless (equal result (display-formula display))
      (make-display :formula result
		    :explain
                    (list (list :string "The conjunctive normal form ..."))))))

(defcmd disjunctive (:display)
  ((:string "Transform the current subformula into disjunctive
normal form. You might find this useful in conjunction with the
CASES mechanism."))
  (let ((result (disjunctive-normal-form
		 (display-formula display) index
		 (make-context-for-bool-p-from-display display))))
    (unless (equal result (display-formula display))
      (make-display :formula result
		    :explain
		    (list (list :string "The disjunctive normal form ..."))))))

;;; ----- Working Directory.

(defcmd print-working-directory ()
  ((:string "Display the current working directory."))
  (printer
   `((:string "Current working directory is")
     (:string ,(format nil "\"~A\""
		       (namestring (truename *default-pathname-defaults*))))
     (:newline)))
  nil)

(defcmd set-working-directory (directory-name)
  ((:string "Set the current working directory to the specified directory
if it exists."))
  (cond ((stringp directory-name)
	 (let* ((dirname
		 (if (equal (aref directory-name
				  (- (string-length directory-name) 1))
			    #\/)
		     directory-name
		   (string-append directory-name "/")))
		(path (car (directory (merge-pathnames dirname)))))
	   (cond (path
		  (setf *default-pathname-defaults* path)
		  t)
		 (t
		  (print-error 'directory-does-not-exist dirname)
		  nil))))
	(t
	 (print-error 'filename-not-string directory-name)
	 nil)))
