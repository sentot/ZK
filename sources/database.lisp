
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

(proclaim '(special *initial-database*))

;;;
;;; The system maintains declarations (also called events) in a
;;; database. The structures for events are defined in structures.lisp.
;;; Here the basic functions that manipulate the database are defined.
;;; ____________________________________________________________________



;;; Variables and constants used by the database.

;;; All events (declarations) are recorded in a history list.
;;; The list is a list of events and groups of events with the
;;; first being the most recent. A group is represented as a list
;;; with the most recent last.

(defvar *history* nil)

;;; Variables that have been "seen" are kept in a list.

(defvar *variables* nil)

;;; The entire database is represented by the following:

(defparameter *database-globals* '(*history* *variables*))

;;; Part of the database is represented using property lists
;;; using the following indicators:

(defparameter *database-indicators* '(event rules frules grules rename))

;;; Functions for accessing the database.

;;; The system portion of the history are those that are predeclared.
;;; The last event in the system history is (tag nil)

(defun system-history ()
  (car (last *history*)))

;;; The user portion of the history contains events declared by the user.
;;; The events follow (tag nil).

(defun user-history ()
  (butlast *history*))

;;; This function returns just top level user events. In the case of
;;; a group, the top level event is the representative event.

(defun group-user-history ()
  (mapcar #'group-event (user-history)))

;;; Binding for custom event struct to list converter.

(defvar *format-event* nil)

;;; Binding for custom printing of event names.

(defvar *format-event-name* nil)

;;; Function for converting events to their external representations
;;; using the binding of *format-event*.

(defun format-event (event-struct)
  (funcall (or *format-event* #'lisp-format-event) event-struct))

;;; Function for printing event names using the binding of
;;; *format-event-name*.

(defun format-event-name (event-struct)
  (funcall (or *format-event-name* #'lisp-format-event-name) event-struct))

;;; The default function for *format-event*.

(defun lisp-format-event (event-struct)
  (funcall (or (get (event-kind event-struct) 'print)
	       (get (event-type event-struct) 'print))
	   event-struct))

;;; Function for printing an event-struct.

(defun print-event-struct (event-struct indent)
  (printer (list (list :event (format-event event-struct))) t indent))

;;; Function that returns the name of an event.

(defun lisp-format-event-name (event)
  (event-name event))

;;; Internal command for printing an event.

(defcmd print-event (event-name)
  ((:string "Displays the event denoted by")
   (:command-argument event-name)
   (:punctuation ".")
   (:string "The event is printed in exactly the form it was input."))
  (cond ((and (symbolp event-name) (get-event event-name))
         (print-event-struct (get-event event-name) 0))
        (t (let ((name (car (true-name event-name)))
                 (kind (cdr (true-name event-name))))
	     ;; Pseudo events (axioms).
             (when (and kind (get-event name))
               (let ((formula (event-formula (get-event name))))
                 (print-event-struct
                  (make-axiom :name event-name
			      :kind 'axiom
			      :args nil
			      :formula (closed-form formula))
                  0))))))
  nil)

;;; Auxiliary function for print-history.

(defun print-history-aux (event depth detail-level indent)
  (cond ((or (atom event)
	     (zerop depth))
	 (let ((event (group-event event)))
	   (print-event-struct event indent)
	   (and (integerp detail-level)
		(not (minusp detail-level))
		(if (eq event (get-event nil))	;check (tag nil)
		    (printer '((:newline)))
		  (print-event-proof
		   (event-name event) detail-level indent)))))
	(t (let ((depth (1- depth)))
	     (print-history-aux (car event) depth detail-level indent)
	     (let ((indent (+ indent 4)))
	       (mapcar #'(lambda (u)
			   (print-history-aux u depth detail-level indent))
		       (cdr event)))))))

;;; Command to print events in the user history.

(defcmd print-history (&key from to first last depth detail-level)
  ((:string "Displays some portion of the history.  Each
event is printed in the form it was input, regardless of any
normalization.  The keywords")
   (:command-argument :from)
   (:string "(defaults to the first user
event) and")
   (:command-argument :to)
   (:string "(defaults to the last event) may be supplied with
event names to select a subsequence of the history to be
printed.  The keywords")
   (:command-argument :first)
   (:string "and")
   (:command-argument :last)
   (:string "may also be supplied
with integers, in which case the first and last number, respectively, of
events in the specified subsequence will be printed.  The keyword")
   (:command-argument :depth)
   (:string "(defaults to 0) is an integer specifying how many levels of
nested definitions are printed, with 0 meaning
only the top level is printed, while a negative number means all levels
are printed.  The keyword")
   (:command-argument :detail-level)
   (:punctuation ",")
   (:string "which defaults to -1, specifies the level of
detail for the proofs of the events.  A level of
-1 inhibits printing of proofs.  Also see")
   (:command-name print-proof)
   (:string "for
further information."))
  (let* ((user-history (user-history))
	 (tmp (reverse (if (null to)
			   user-history
			   (group-member (get-event to) user-history))))
	 (subsequence (if (null from)
			  tmp
			  (group-member (get-event from) tmp)))
	 (head (and (integerp first)
		    (butlast subsequence
			     (max 0 (- (length subsequence) first)))))
	 (tail (and (integerp last)
		    (reverse (butlast (reverse subsequence)
				      (max 0 (- (length subsequence) last))))))
	 (depth (if (integerp depth) depth 0)))
    (mapc #'(lambda (u) (print-history-aux u depth detail-level 0))
	  (if (or (and (null head) (null tail)) (intersection-eq head tail))
	      subsequence
	      (append head tail)))
    nil))

;;; Function for finding rules/frules/grules that match a given expression.

(defun rules-matching (sexpr)
  (let ((formula (parse-formula sexpr)))
    (when (and formula (index-of formula))
      (append
	(remove-if-not
	  #'(lambda (rule) (multiple-value-bind (substitutions match-success)
			       (match-pattern-formula
				 (rule-pattern rule) formula)
			     substitutions match-success))
	  (get-rules formula))
	(get-frules formula)
	(get-grules formula)))))

;;; Command for displaying all the rules/frules/grules that match
;;; a function name or a given expression.

(defcmd print-rules (event-name-or-expression &optional print-event)
  ((:string "Displays all rules, frules and grules that
match a function name or a given expression.  If")
   (:command-argument event-name-or-expression)
   (:string "is an expression then all rules, frules and grules
whose pattern match it are displayed.  If")
   (:command-argument event-name-or-expression)
   (:string "is a function name, then all rules, frules and grules
that match any application of the function are displayed.
Normally, only the names of the rules, frules and grules are printed.
However, if a value is supplied for")
   (:command-argument print-event)
   (:punctuation ",")
   (:string "then the rules, frules and grules are printed in
their entirety."))
  (mapc #'(lambda (u) (if print-event
			  (print-event-struct u 0)
			(printer (list (list :newline)
				       (list :event-name (event-name u))))))
	(if (symbolp event-name-or-expression)
	    (append (get-rules-index event-name-or-expression)
		    (get-frules-index event-name-or-expression)
		    (get-grules-index event-name-or-expression))
	    (rules-matching event-name-or-expression)))
  nil)

;;; Command to undo the most recent declaration(s).

(defcmd undo (&optional number-of-events)
  ((:string "Undoes the latest user declaration(s).  Once undone, it
is as if the declaration(s) had never been entered.  The name of the
(earliest entered) undone event is displayed if")
   (:command-name undo)
   (:string "is successful."))
  (when (null number-of-events) (setq number-of-events 1))
  (when (and (user-history) (integerp number-of-events) (> number-of-events 0))
    (do ((event-name nil)
	 (step 1 (1+ step)))
	((or (> step number-of-events) (null (user-history)))
	 event-name)
      (setq event-name (undo-event)))))

;;; Function that actually performs the undo of a declaration.

(defun undo-event ()
  (prog1 (format-event-name (group-event (car *history*)))
	 (if (atom (car *history*))
	     ;; need to clear *current-display* if it is part of a proof
	     ;; about the undone event or if it is part of an anonymous
	     ;; proof
	     (progn (when (and *current-display*
			       (or (null (display-event *current-display*))
				   (eq (display-event *current-display*)
				       (car *history*))))
		      (reset-display))		;may reference it
                    (clear-browse nil)
		    (funcall (get (event-type (car *history*)) 'del)
			     (car *history*)))	;database delete
	     (dotimes (i (unfold-events)) (undo-event)))))

;;; Command to undo back to and including the specified event.

(defcmd undo-back-thru (event-name)
  ((:string "Undoes the effect of user declarations entered since")
   (:command-argument event-name)
   (:string "was declared inclusively.  The effect is as though
all declarations from")
   (:command-argument event-name)
   (:string "on were never entered.")
   (:command-argument event-name)
   (:string "is displayed if the")
   (:command-name undo-back-thru)
   (:string "was successful."))
  (when (and (symbolp event-name)
             (get-event event-name)
             (member-eq event-name (mapcar #'format-event-name
					   (group-user-history))))
    (loop until (let ((group-name (format-event-name
				   (group-event (car *history*)))))
		  (or (null *history*)
		      (null (undo-event))
		      (eq group-name event-name))))
    event-name))

;;; Command to undo back to but not including the specified event.

(defcmd undo-back-to (event-name)
  ((:string "Undoes the effect of user declarations entered since")
   (:command-argument event-name)
   (:string "was declared exclusively.  The effect is as though
all declarations after")
   (:command-argument event-name)
   (:string "were never entered.")
   (:command-argument event-name)
   (:string "is displayed if the")
   (:command-name undo-back-to)
   (:string "was successful."))
  (when (and (symbolp event-name)
             (get-event event-name)
             (member-eq event-name
			(mapcar #'format-event-name (group-user-history))))
    (loop until (let ((group-name (format-event-name
				   (group-event (car *history*)))))
		  (or (null *history*)
		      (eq group-name event-name)
		      (null (undo-event)))))
    event-name))

;;; Function that produces the representative event in the case of
;;; a group. Otherwise the representative is the event itself.

(defun group-event (event)
  (cond ((atom event) event)
        (t (group-event (car event)))))

;;; Function that produces the last event in a group. For a non-group,
;;; it is just the event itself.

(defun last-event (event)
  (cond ((atom event) event)
	(t (last-event (car (last event))))))

;;; Function that produces the name of the representative event.

(defun group-name (event)
  (event-name (group-event event)))

;;; Function that determines if an event is a representative event
;;; in the given history sequence.

(defun group-member (event history)
  (cond ((null history) nil)
        ((eq event (group-event (car history))) history)
        (t (group-member event (cdr history)))))

;;; Function that produces the list of events belonging to the
;;; top level group in which the specified event resides (the
;;; specified event may reside several levels down the
;;; group structure.

(defun group-event-list (event)
  (flatten (event-group-group event (event-top-level-group event *history*))))

(defun event-group-group (event group)
  (cond ((eq (group-event group) event) group)
	((atom group) nil)
	(t (some #'(lambda (u) (event-group-group event u)) group))))

(defun event-top-level-group (event history)
  (dolist (e history)
    (when (member-eq event (flatten e))
      (return e))))

(defun group-event-name-list (event)
  (mapcar #'event-name (group-event-list event)))

;;; Function to fold the n most recent events or groups in
;;; *history* into a group.

(defun fold-events (n)
  (loop with (group)
        for i from 1 to n
        do (push (pop *history*) group)
        finally (push group *history*)))

;;; Function to unfold the most recent group in *history*.

(defun unfold-events ()
  (let ((group (pop *history*)))
    (loop for event in group
          do (push event *history*))
    (length group)))

;;; Function to enable a group.  If the group is just an event,
;;; enable the event. Otherwise enable all events in the group.

(defun enable-group (group)
  (if (atom group)
      (let ((enabled-slot (get (event-type group) 'enabled)))
        (when (and enabled-slot
		   (not (or (function-stub-p group)
			    (zf-function-p group))))
          (funcall enabled-slot group t)))
      (mapcar #'enable-group group)))

;;; Function to add a list of events to the database.
;;; This is intended only for initializing the database.

(defun add-to-database (event-list)
  (with-prover-muzzled				;no warnings
   (mapc #'eval event-list))
  (make-group-assumption *history*)
  (fold-events (length *history*))
  nil)

;;; Function to zap the database.

(defun zap-database ()
  (mapc #'(lambda (u) (set u nil)) *database-globals*)
  ;(clear-type)
  (do-symbols (u) (mapc #'(lambda (v) (remprop u v)) *database-indicators*))
  nil)

;;; To prevent compiler warning messages.

(proclaim '(special *initial-database*))

;;; Function to reset the system.

(defun reset-prover (&optional hard-reset-p inhibit-init-p)
  (reset-display)
  (reset-deductive-database)
  (reset-browse)
  (when (or hard-reset-p
	    ;; try to do a soft reset by undoing to (tag nil)
	    (progn (dolist (event (user-history)) (undo))
		   (dolist (var *variables*) (setf (get-rename var) nil))
		   (setq *variables* nil)
		   ;; hard reset if the undo to (tag nil) failed
		   (or (null *history*)
		       (not (eq (car (last (system-history)))
				(get-event nil))))))
    (zap-database)
    (unless inhibit-init-p
      (add-to-database *initial-database*)
      (setq *variables* nil)))
  nil)

;;; The command to reset the system.

(defcmd reset (&optional hard-reset-p)
  ((:string "Restores the prover to its initial state, which it had
at the time of loading.  Normally this happens by undoing back to the
initial state; however, if this fails or if")
   (:command-argument hard-reset-p)
   (:string "is non-nil, then")
   (:command-name reset)
   (:string "completely clears the prover database and
restores it from the initial state description."))
  (reset-prover hard-reset-p nil)
  t)

;;; Generic functions for dealing with event proerties.

;;; Get event property specified by the indicator.

(defun get-event-property (event indicator)
  (getf (event-prop event) indicator))

;;; Remove event property specified by the indicator.

(defun rem-event-property (event indicator)
  (remf (event-prop event) indicator))

;;; Set event property specified by the indicator to the
;;; value specified.

(defun put-event-property (event indicator value)
  (setf (getf (event-prop event) indicator) value))

;;; Initialize event number and access fields.

(defun init-access (event)
  (let ((number (if (null *history*) 1
		    (1+ (event-number (last-event (car *history*)))))))
    (setf (event-number event) number)
    (setf (event-access event) number)))

;;; Make status of event to be proven without giving any proof.
;;; This is intended for events in *initial-database*.

(defun make-event-assumption (event)
  (setf (event-proven event) t)
  (setf (event-proof event) nil))

;;; Make status of events in a group  to be proven without giving any proof.
;;; This is for initialization of events in *initial-database*.

(defun make-group-assumption (group)
  (cond ((atom group) (make-event-assumption group))
	(t (mapc #'make-group-assumption group))))

;;; Functions for freezing/thawing displays
;;; and functions for listing names of events that have some property.

(defun freeze-display (display-struct)
  (let ((struct (copy-display display-struct)))
    (setf (display-event struct) nil)
    (liststruct struct)))

(defun freeze-display-without-details (display-struct)
  (let ((struct (copy-display display-struct)))
    (setf (display-event struct) nil)
    (setf (display-details struct) nil)
    (liststruct struct)))

(defun thaw-display (event display-description)
  ;; when thawing there is no current display or event hence the nil
  (let ((struct (fillstruct (make-display) display-description)))
    (setf (display-event struct) event)
    struct))

;;; Return names of events whose pred property is t.

(defun select-events
    (pred &optional (event-list (nreverse (flatten *history*))))
  (mapcar #'event-name (remove-if-not pred event-list)))

;;; This version for user events only.

(defun select-user-events
    (pred &optional (event-list (nreverse (flatten (user-history)))))
  (mapcar #'event-name (remove-if-not pred event-list)))

(defun select-proof-events ()
  (select-user-events #'event-proof))

(defun select-noproof-events ()
  (select-user-events #'(lambda (x) (null (event-proof x)))))

(defun select-proven-events ()
  (select-user-events #'event-proven))

(defun select-unproven-events ()
  (select-user-events #'(lambda (x) (not (event-proven x)))))

;;; The functions for the handling of events in the database.
;;;
;;; For each type of event (namely tag, axiom, rule, frule, grule, name
;;; and uload), there is a set of functions for performing operations on
;;; that event within the database.  Each of these functions takes a
;;; single argument, a struct of for that event, except for thaw whose
;;; argument represents the form used as the frozen state of that event.
;;; Some of the functions defined for only some events also takes
;;; different arguments. For the most part these functions tend to look
;;; the same for the various events, however this is not a restriction
;;; of the database but simply a result the conventions used for events.
;;;
;;; The types of events now allowed are:
;;;     tag  - history list label
;;; 	axiom - defines a lemma for manual use
;;; 	rule - sets up a lemma to be used for rewriting
;;; 	frule - a lemma to be used for forward chaining
;;;     grule - a lemma to be used as an assumption
;;; 	name - declares a function
;;; 	uload - declares an object to load
;;;
;;; Currently the functions for each event are:
;;; 	add - add it to the database
;;; 	del - remove it from the database
;;; 	name - the name of the event
;;; 	kind - the kind field of event
;;;	prop - the property list for event
;;;	copy - return a new copy of the event
;;; 	print - something suitable to print out
;;;
;;; The following functions are defined for some events:
;;;     proof - set or return the (partial) proof
;;;             (axiom/rule/frule/grule/name)
;;; 	proven - set or return the proven flag
;;;              (axiom/rule/frule/grule/name)
;;;     assume - returns the args/formula to assume
;;;              (axiom/rule/frule/grule/name)
;;; 	enabled - set or return enabled/disabled flag
;;;               (rule/frule/grule/name)


;;; ============================ tag =============================

(setf (get 'tag 'copy) #'copy-tag)

(defpropfun (tag add) (tag)
  (init-access tag)
  (push tag *history*)
  (setf (get-event (tag-name tag)) tag))

(defpropfun (tag del) (tag)
  (remprop (tag-name tag) 'event)
  (pop *history*))

(defpropfun (tag print) (tag)
  `(,(tag-kind tag) ',(tag-name tag)))

(defpropfun (tag formula) (tag &optional (formula-flag nil supplied-p))
  (if supplied-p (setf (tag-formula tag) formula-flag) (tag-formula tag)))

(defpropfun (tag details) (tag)
  (tag-details tag))


;;; ============================ axiom =============================

(setf (get 'axiom 'copy) #'copy-axiom)

(defpropfun (axiom add) (axiom)
  (init-access axiom)
  (push axiom *history*)
  (setf (get-event (axiom-name axiom)) axiom))

(defpropfun (axiom del) (axiom)
  (remprop (axiom-name axiom) 'event)
  (pop *history*))

(defpropfun (axiom assume) (axiom)
  (list (unique (list-of-free-variables-unexpanded (axiom-formula axiom)))
	(axiom-formula axiom)))

(defpropfun (axiom print) (axiom)
  `(,(axiom-kind axiom) ',(axiom-name axiom)
    ',(axiom-args axiom) ',(axiom-formula axiom)))

(defpropfun (axiom formula) (axiom &optional (formula-flag nil supplied-p))
  (if supplied-p
      (setf (axiom-formula axiom) formula-flag)
    (axiom-formula axiom)))

(defpropfun (axiom details) (axiom)
  (axiom-details axiom))

;;; ============================ rule =============================

(setf (get 'rule 'copy) #'copy-rule)

(defpropfun (rule add) (rule)
  (init-access rule)
  (push rule *history*)
  (setf (get-event (rule-name rule)) rule)
  (push rule (get-rules-index (rule-index rule)))
  rule)

(defpropfun (rule del) (rule)
  (setf (get-rules-index (rule-index rule))
	(delete-eq rule (get-rules-index (rule-index rule)) 1))
  (remprop (rule-name rule) 'event)
  (pop *history*))

(defpropfun (rule assume) (rule)
  (list (unique (list-of-free-variables-unexpanded (rule-formula rule)))
	(rule-formula rule)))

(defpropfun (rule print) (rule)
  `(,(rule-kind rule) ',(rule-name rule)
    ',(rule-args rule) ',(rule-formula rule)))

(defpropfun (rule formula) (rule &optional (formula-flag nil supplied-p))
  (if supplied-p
      (setf (rule-formula rule) formula-flag)
    (rule-formula rule)))

(defpropfun (rule details) (rule)
  (rule-details rule))

(defpropfun (rule enabled) (rule &optional (enabled-flag nil supplied-p))
  (if supplied-p (setf (rule-enabled rule) enabled-flag)) (rule-enabled rule))

;;; ============================ frule =============================

(setf (get 'frule 'copy) #'copy-frule)

(defpropfun (frule add) (frule)
  (init-access frule)
  (push frule *history*)
  (setf (get-event (frule-name frule)) frule)
  (push frule (get-frules-index (frule-index frule)))
  frule)

(defpropfun (frule del) (frule)
  (setf (get-frules-index (frule-index frule))
	(delete-eq frule (get-frules-index (frule-index frule))))
  (remprop (frule-name frule) 'event)
  (pop *history*))

(defpropfun (frule assume) (frule)
  (list (unique (list-of-free-variables-unexpanded (frule-formula frule)))
	(frule-formula frule)))

(defpropfun (frule print) (frule)
  `(,(frule-kind frule) ',(frule-name frule) ',(frule-args frule)
    ',(frule-formula frule)))

(defpropfun (frule formula) (frule &optional (formula-flag nil supplied-p))
  (if supplied-p
      (setf (frule-formula frule) formula-flag)
    (frule-formula frule)))

(defpropfun (frule details) (frule)
  (frule-details frule))

(defpropfun (frule enabled) (frule &optional (enabled-flag nil supplied-p))
  (if supplied-p
      (setf (frule-enabled frule) enabled-flag)
    ) (frule-enabled frule))

;;; ============================ grule =============================

(setf (get 'grule 'copy) #'copy-grule)

(defpropfun (grule add) (grule)
  (init-access grule)
  (push grule *history*)
  (setf (get-event (grule-name grule)) grule)
  (push grule (get-grules-index (grule-index grule)))
  grule)

(defpropfun (grule del) (grule)
  (setf (get-grules-index (grule-index grule))
	(delete-eq grule (get-grules-index (grule-index grule))))
  (remprop (grule-name grule) 'event)
  (pop *history*))

(defpropfun (grule assume) (grule)
  (list (unique (list-of-free-variables-unexpanded (grule-formula grule)))
	(grule-formula grule)))

(defpropfun (grule print) (grule)
  `(,(grule-kind grule) ',(grule-name grule) ',(grule-args grule)
    ',(grule-formula grule)))

(defpropfun (grule formula) (grule &optional (formula-flag nil supplied-p))
  (if supplied-p
      (setf (grule-formula grule) formula-flag)
    (grule-formula grule)))

(defpropfun (grule details) (grule)
  (grule-details grule))

(defpropfun (grule enabled) (grule &optional (enabled-flag nil supplied-p))
  (if supplied-p
      (setf (grule-enabled grule) enabled-flag)
    ) (grule-enabled grule))

;;; ======================= function-stub ========================


(setf (get 'function-stub 'copy) #'copy-function-stub)

(defpropfun (function-stub add) (stub)
  (init-access stub)
  (push stub *history*)
  (setf (get-event (function-stub-name stub)) stub)
  stub)

(defpropfun (function-stub del) (stub)
  (remprop (function-stub-name stub) 'type)
  (remprop (function-stub-name stub) 'event)
  (pop *history*))

(defpropfun (function-stub assume) (stub)
  (let ((event (get-event
		(intern (string-append (string (function-stub-name stub))
				       ".DEFINITION")
			*zk-package*))))
    (when event
      (let ((formula (event-formula event)))
	(list (unique (list-of-free-variables-unexpanded formula)) formula)))))

(defpropfun (function-stub print) (stub)
  `(,(function-stub-kind stub) ',(function-stub-name stub)
    ',(function-stub-args stub) ',(function-stub-type stub)))

;;; ======================= zf-function ========================


(setf (get 'zf-function 'copy) #'copy-zf-function)

(defpropfun (zf-function add) (zf)
  (init-access zf)
  (push zf *history*)
  (setf (get-event (zf-function-name zf)) zf)
  zf)

(defpropfun (zf-function del) (zf)
  (remprop (zf-function-name zf) 'type)
  (remprop (zf-function-name zf) 'event)
  (pop *history*))

(defpropfun (zf-function formula) (zf &optional (formula-flag nil supplied-p))
  (if supplied-p
      (setf (zf-function-formula zf) formula-flag) (zf-function-formula zf)))

(defpropfun (zf-function details) (zf)
  (zf-function-details zf))

(defpropfun (zf-function assume) (zf)
  (let ((event (get-event
		(intern (string-append (string (zf-function-name zf))
				       ".DEFINITION")
			*zk-package*))))
    (when event
      (let ((formula (event-formula event)))
	(list (unique (list-of-free-variables-unexpanded formula)) formula)))))

(defpropfun (zf-function print) (zf)
  `(,(zf-function-kind zf) ',(zf-function-name zf)
    ',(zf-function-args zf)))


;;; ============================ ufunction =============================

(setf (get 'ufunction 'copy) #'copy-ufunction)

(defpropfun (ufunction add) (uf)
  (init-access uf)
  (push uf *history*)
  (setf (get-event (ufunction-name uf)) uf)
  uf)

(defpropfun (ufunction del) (uf)
  (remprop (ufunction-name uf) 'type)
  (remprop (ufunction-name uf) 'event)
  (pop *history*))

(defpropfun (ufunction formula) (uf &optional (formula-flag nil supplied-p))
  (if supplied-p
      (setf (ufunction-formula uf) formula-flag)
    (ufunction-formula uf)))

(defpropfun (ufunction details) (uf)
  (ufunction-details uf))

(defpropfun (ufunction enabled) (uf &optional (enabled-flag nil supplied-p))
  (if supplied-p
      (setf (ufunction-enabled uf) enabled-flag)
    (ufunction-enabled uf)))

(defpropfun (ufunction assume) (uf)
  (let ((formula (make-= (cons (ufunction-name uf) (ufunction-args uf))
			 (ufunction-body uf))))
    (list (unique (list-of-free-variables-unexpanded formula))
	  formula)))

(defpropfun (ufunction print) (uf)
  `(,(ufunction-kind uf) ',(ufunction-name uf)
    ',(ufunction-args uf) ',(ufunction-type uf)
	',(ufunction-measure uf) ',(ufunction-body uf)))


;;; ============================ uload =============================

(setf (get 'uload 'copy) #'copy-uload)

(defpropfun (uload add) (uload)
  (unless (get-event (uload-name uload))
    (init-access uload)
    (push uload *history*)
    (setf (get-event (uload-name uload)) uload)
    (load-library-unit uload)))

(defpropfun (uload del) (uload)
  (remprop (uload-name uload) 'event)
  (pop *history*))

(defpropfun (uload print) (uload)
  `(,(uload-kind uload) ',(uload-name uload)))

(defpropfun (uload formula) (uload &optional (formula-flag nil supplied-p))
  (if supplied-p
      (setf (uload-formula uload) formula-flag)
      (uload-formula uload)))

(defpropfun (uload details) (uload)
  (uload-details uload))


;;; These are functions that return the formulas associated with events.
;;; get-po-axiom and get-internal-axiom returns formulas associated with
;;; pseudo events.

(defun get-axiom (event-name)
  (or (and (symbolp event-name)
           (get-event event-name)
           (get (event-type (get-event event-name)) 'assume)
           (let ((event (get-event event-name)))
	     (when (or (axiom-p event) (rule-p event) (frule-p event)
		       (grule-p event) (ufunction-p event))
	       (let ((assumption
		      (funcall (get (event-type event) 'assume)
			       (get-event event-name))))
		 (closed-form (cadr assumption))))))
      ;; eventless axioms
      (get-definition-axiom event-name)
      (get-rawpo-axiom event-name)
      (get-po-axiom event-name)
      (get-internal-axiom event-name)
      (get-type-of-axiom event-name)))

(defun get-po-axiom (name)
  (let (index event axiom)
    (and (symbolp name)
         (setq index (string-search= ".PO" name))
         (= (string-length name) (+ index 3))
         (setq event (get-event (intern (substring name 0 index)
					*zk-package*)))
         (or (eq (event-name event) 'div)
             (eq (event-name event) 'rem)
             (eq (event-name event) 'mod)
             (eq (event-name event) 'epsilon-induction)
             (ufunction-p event)
             (not (null (event-rawpo event))))
         (setq axiom (event-formula event))
	 (closed-form axiom))))

(defun get-rawpo-axiom (name)
  (let (index event axiom)
    (and (symbolp name)
         (setq index (string-search= ".RAWPO" name))
         (= (string-length name) (+ index 6))
         (setq event (get-event (intern (substring name 0 index)
					*zk-package*)))
         (setq axiom (event-rawpo event))
	 (closed-form axiom))))

(defun get-definition-axiom (name)
  (let (index event)
    (and (symbolp name)
         (setq index (string-search= ".DEFINITION" name))
         (= (string-length name) (+ index 11))
         (setq event (get-event (intern (substring name 0 index)
					*zk-package*)))
	 (or (axiom-p event) (rule-p event) (frule-p event)
	     (grule-p event) (ufunction-p event))
	 (let ((assumption
		(funcall (get (event-type event) 'assume) event)))
	   (closed-form (cadr assumption))))))

(defun get-internal-axiom (name)
  (let (index event axiom)
    (and
     (symbolp name)
     (setq index (string-search= ".INTERNAL" name))
     (= (string-length name) (+ index 9))
     (setq event (get-event (intern (substring name 0 index)
				    *zk-package*)))
     (setq axiom
           (cond ((rule-p event)
                  (let ((unrenames
                         (mapcar #'(lambda (x)
                                     (cons (cdr x) (car x)))
                                 (rule-renames event))))
                    (sublis-eq
                     unrenames
                     (if (rule-conditional event)
                         (make-= (rule-pattern event)
                                 (make-if (rule-subgoal event)
                                          (rule-value event)
                                          (rule-pattern event)))
                       (make-= (rule-pattern event)
                               (rule-value event))))))
                 ((ufunction-p event)
		  (make-= (cons (ufunction-name event) (ufunction-args event))
			  (ufunction-internal-body event)))
                 ((frule-p event) (make-frule-internal-axiom event))
                 ((grule-p event) (make-grule-internal-axiom event))
                 ))
     (closed-form axiom))))


;;; Generate the ``internal axiom'' for frule.
;;; It is of the form:
;;; (if cond concl (true))
;;; where cond is of the form expr or (if expr (false) (true)),
;;; and concl is of the form:
;;; C, (if c (false) (true)), or
;;; (if C1 (if C2 ... (if Ci (true) (false)) ... (false)) (false))
;;; where each of the Ci's is either ci or (if ci (false) (true)).

(defun make-frule-internal-axiom (event)
  (let ((unrenames (mapcar #'(lambda (x) (cons (cdr x) (car x)))
                           (frule-renames event))))
    (sublis-eq
     unrenames
     (make-if (if (frule-negate event)
                  (make-if (frule-pattern event) *false* *true*)
                (frule-pattern event))
              (if (and (= (length (frule-values event)) 1)
                       (cdar (frule-values event)))
                  (make-if (caar (frule-values event)) *false* *true*)
                (make-frule-internal-axiom-aux (frule-values event)))
              *true*))))

(defun make-frule-internal-axiom-aux (values)
  (cond ((null values) *true*)
        (t (let ((v (car values)))
             (make-if (if (cdr v) (make-if (car v) *false* *true*) (car v))
                      (make-frule-internal-axiom-aux (cdr values))
                      *false*)))))


(defun make-grule-internal-axiom (event)
  (let ((unrenames (mapcar #'(lambda (x) (cons (cdr x) (car x)))
                           (grule-renames event))))
    (sublis-eq
     unrenames
     (cond ((null (grule-subgoals event))
            (if (cdr (grule-value event))
                (make-if (car (grule-value event)) *false* *true*)
              (car (grule-value event))))
           (t (make-if
               (let ((subgoals (grule-subgoals event)))
                 (if (= (length subgoals) 1)
                     (if (second (first subgoals))
                         (make-if (first (first subgoals)) *false* *true*)
                       (first (first subgoals)))
                   (make-grule-internal-axiom-aux subgoals)))
               (if (cdr (grule-value event))
                   (make-if (car (grule-value event)) *false* *true*)
                 (make-if (car (grule-value event)) *true* *false*))
               *true*))))))

(defun make-grule-internal-axiom-aux (subgoals)
  (cond ((null subgoals) *true*)
        (t (let ((s (car subgoals)))
             (make-if (if (second s)
                          (make-if (first s) *false* *true*)
                        (first s))
                      (make-grule-internal-axiom-aux (cdr subgoals))
                      *false*)))))

(defun get-type-of-axiom (name)
  (let (index event axiom)
    (and
     (symbolp name)
     (setq index (string-search= ".TYPE-OF-AXIOM" name))
     (= (string-length name) (+ index 14))
     (setq event (get-event (intern (substring name 0 index)
				    *zk-package*)))
     (or
      (and
       (ufunction-p event)
       (ufunction-type event)
       (not (univ-type-p (ufunction-type event)))
       (setq axiom
	     (make-= `(type-of ,(cons (ufunction-name event)
				      (ufunction-args event)))
		     (ufunction-type event)))
       (universally-quantify (ufunction-args event) axiom))
      (and
       (function-stub-p event)
       (function-stub-type event)
       (not (univ-type-p (function-stub-type event)))
       (setq axiom
	     (make-= `(type-of
		       ,(cons (function-stub-name event)
			      (function-stub-args event)))
		     (function-stub-type event)))
       (universally-quantify (function-stub-args event) axiom))))))
