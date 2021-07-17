
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


;;; ================= Rudimentary Proof Browsing ===============


;;; Navigate a proof without changing the proof.

;;; Note: Update of proof status invalidates a browse.

;;; The proof browsing facility allows one to navigate through a
;;; proof down to a very detailed level. It requires proof logging
;;; to be turned on during the proof.

;;; A snapshot of a browse is stored in a browse struct.

;;; The current snapshot of current browse.
(defvar *browse-snapshot* nil)

;;; A browse is represented by a browse history: a sequence of
;;; browse snapshots in the form of a list. It can be saved in the
;;; browse slot of an event struct. In such a case, the browse
;;; is that of a proof associated with the event.

;;; The current browse (history).
(defvar *browse-history* nil)

;;; Reset the current browse.
(defun reset-browse ()
  (setq *browse-snapshot* nil *browse-history* nil))



;;; Update the current browse snapshot by pushing it into the
;;; current browse history and replacing it with a new snapshot.
(defun update-browse (snapshot)
  (push *browse-snapshot* *browse-history*)
  (setq *browse-snapshot* snapshot))

;;; Continue a browse from a previously saved history.
(defun continue-browse (browse-history)
  (setq *browse-snapshot* (car browse-history)
        *browse-history* (cdr browse-history))
  t)

;;; Initialize the browsing of a proof of the  event:
;;; - start with empty history,
;;; - snapshot is at the beginning of the proof.
(defun initialize-browse (event)
  (clear-browse event)
  (setq *browse-history* nil)
  (setq *browse-snapshot*
	(make-browse :event event
                     :display-list
                     (cond ((null event)
                            (reverse (cons *current-display*
                                           *display-history*)))
                           (t (reverse (event-proof event))))))
  (setf (browse-current-display *browse-snapshot*)
        (pop (browse-display-list *browse-snapshot*)))
  (setf (browse-at-top-level *browse-snapshot*) t)
  (let ((formula
         (cond ((null event)
                (display-formula (browse-current-display *browse-snapshot*)))
               (t (event-formula event)))))
    (setf (browse-formula *browse-snapshot*)
          (universally-quantify
           (unique (list-of-free-variables-unexpanded formula))
           formula)))
  t)

;;; Function to clear the browse of an event.
(defun clear-browse (event)
  (when (and *browse-snapshot*
             (eq (browse-event *browse-snapshot*) event))
    (reset-browse))
  (unless (null event) (setf (event-browse event) nil)))




;;; Save the current browse in the event structure if the
;;; current browse is associated with an event.
(defun update-browse-status ()
  (when (and *browse-snapshot* (browse-event *browse-snapshot*))
    (setf (event-browse (browse-event *browse-snapshot*))
          (cons *browse-snapshot* *browse-history*))))

;;; Begin or continue the browse of the proof of an event.
;;; The current browse is first saved.
(defun begin-new-browse (event-name continue-browse-flag)
  (update-browse-status) ; Save current browse
  (let* ((event (and event-name (symbolp event-name)
                     (get-event event-name)))
         (browse (when event (event-browse event))))
    (cond
     ;; continue partial browse
     ((and continue-browse-flag (not (null browse)))
      (continue-browse browse))
     ;; begin new browse for proof of an event
     ((and event (event-proof event))
      (initialize-browse event))
     ;; or otherwise browse current proof
     ((and (null event-name) *current-display*)
      (initialize-browse nil)))))




;;; ==================== Browsing Commands ====================


;;; Command to begin a new browse.
(defcmd browse-begin (&optional event-name)
  ((:string "Starts the browsing of a complete or partial proof.
If")
   (:command-argument event-name)
   (:string "is supplied,
then the proof associated with")
   (:command-argument event-name)
   (:string "is browsed.  Otherwise, the current proof is browsed."))
  (update-proof-status)
  (begin-new-browse event-name t))

(defun next-browse (browse)
  (let ((result (copy-browse browse)))
    (when (and (null (browse-at-top-level result))
               (null (browse-log result))
               (not (null (browse-display-list result))))
      (let* ((display (pop (browse-display-list result)))
             (form
              (cond ((null (browse-current-display result))
                     (display-formula display))
                    (t (display-formula (browse-current-display result))))))
        (setf (browse-formula result)
              (universally-quantify
               (unique (list-of-free-variables-unexpanded form))
               form))
        (setf (browse-current-display result) display)
        (setf (browse-base-index result) (display-base-index display))
        (setf (browse-at-top-level result) t)
        (setf (browse-log result) (reverse (display-details display))))
      result)))



;;; Command to move forward at the same level of the proof.
(defcmd browse-forward ()
  ((:string "Advance the proof browser at the current browser
level.  The browse level can be changed using the")
   (:command-name browse-down)
   (:string "and")
   (:command-name browse-up)
   (:string "commands."))
  (unless (null *browse-snapshot*)
    (let ((next (copy-browse *browse-snapshot*)))
      (setq next (browse-forward-aux next))
      (when next
        (update-browse next)
        t))))

(defun browse-forward-aux (browse)
  (cond ((browse-at-top-level browse)
         (setf (browse-at-top-level browse) nil)
         ;; do entire proof command
         (let* ((display (browse-current-display browse))
                (form (display-formula display)))
           (setf (browse-formula browse)
                 (universally-quantify
                  (unique (list-of-free-variables-unexpanded form))
                  form))
           (setf (browse-log browse) nil)
           (setf (browse-base-index browse) (display-base-index display)))
         browse)
        ((null (browse-log browse)) (next-browse browse))
        ((end-marker-p (car (browse-log browse)))
         (loop while (end-marker-p (car (browse-log browse)))
               do (pop (browse-log browse)))
         browse)
        (t (browse-forward-formula browse))))

(defparameter markers-with-saved-result '(simplify match-true match-false
                                                  rewrite invoke))

(defun browse-forward-formula (browse)
  (let ((entry (pop (browse-log browse))))
    (cond ((start-marker-p entry)
           (let ((i (second entry))
                 (kind (first (third entry))))
             (cond ((member-eq kind markers-with-saved-result)
                    (loop while
                          (progn (setq entry (pop (browse-log browse)))
                                 (not (and (end-marker-p entry)
                                      (eq (first (third entry)) kind)
                                      (equal (second entry) i)))))
                    (setf (browse-formula browse)
                          (replace-index
                           (get-relative-index i (browse-base-index browse))
                           (browse-formula browse)
                           (third (third entry)))))
                   (t
                    (loop while (not (end-marker-p (car (browse-log browse))))
                          do (setq browse (browse-forward-formula browse)))
                    (pop (browse-log browse))))))
          (t
           ;; need to apply inference rule here
           (setf (browse-formula browse)
                 (apply-log-entry entry
                                  (browse-base-index browse)
                                  (browse-formula browse))))))
  browse)

(defun apply-log-entry (entry base-index formula)
  (unless (marker-p entry)
    (let* ((infer (car entry))
           (index (get-relative-index (cadr entry) base-index))
           (args (cddr entry))
           (inference (and (symbolp infer) (get-infer infer))))
      (multiple-value-bind (subformula assume)
        (select-index index formula)
        (cond ((null inference)
               *infer-code*)            ;no such inference
              ((null subformula)
               *index-code*)            ;index not in formula
              (t
               (let ((result
                      (apply inference subformula assume args)))
                 (cond ((null result)
                        *apply-code*)   ;inference failed
                       ;; success, return the updated formula
                       (t (setq formula
                                (replace-index index formula result))))))))))
  formula)

(defun get-relative-index (index base-index)
  (cond ((null base-index) index)
        (t
         (loop for i from 1 to (- (length index) (length base-index))
               for l in index
               collect l))))



;;; Command to restart the current browsing of a proof.
(defcmd rebrowse ()
  ((:string "Restart current browse of a complete or partial proof."))
  (update-proof-status)
  (let ((event-name (and *browse-snapshot*
                         (browse-event *browse-snapshot*)
                         (event-name (browse-event *browse-snapshot*)))))
    (begin-new-browse event-name nil)))

;;; Command to undo a browse navigation command.
(defcmd browse-back (&optional n)
  ((:string "Move the Proof Browser backwards")
   (:command-argument n)
   (:string "steps."))
  (when (null n) (setq n 1))
  (when (and *browse-history*
             (integerp n)
             (> n 0))
    ;; if we have something to back up to then ...
    (do ((step 1 (1+ step)))
	((or (> step n) (null *browse-history*)))
      (setq *browse-snapshot* (pop *browse-history*)))
    t))

;;; Command to move forward at next level down in the current proof.
(defcmd browse-down ()
  ((:string "Advance the proof browser to the next point
that is at a lower browse level."))
  (unless (null *browse-snapshot*)
    (let ((next (copy-browse *browse-snapshot*)))
      (cond ((browse-at-top-level next)
             (setf (browse-at-top-level next) nil)
             (update-browse next)
             t)
            ((not (null (browse-log next)))
             (loop while (not (or (null (browse-log next))
                                  (start-marker-p (car (browse-log next)))
                                  (end-marker-p (car (browse-log next)))))
                   do (setq next (browse-forward-aux next)))
             (cond ((null (browse-log next)) nil)
                   ((start-marker-p (car (browse-log next)))
                    (pop (browse-log next))
                    (update-browse next)
                    t)))))))

;;; Command to move forward to next level up in the current proof.
(defcmd browse-up ()
  ((:string "Advance the proof browser to the next point
that is at a greater browse level."))
  (unless (null *browse-snapshot*)
    (let ((next (copy-browse *browse-snapshot*)))
      (when (and (not (browse-at-top-level next))
                 (not (null (browse-log next))))
        (loop while (not (or (null (browse-log next))
                             (end-marker-p (car (browse-log next)))))
              do (setq next (browse-forward-aux next)))
        (unless (null (browse-log next)) (pop (browse-log next)))
        (update-browse next)
        t))))



;;; Command to move forward to some marker in the proof.
;;; This command does not make it to the ZK level.
(defcmd browse-forward-to (kind &optional axiom-name)
  ((:string "Advance the proof browser to the start of
a block described by")
   (:command-argument kind)
   (:string "and (optionally)")
   (:command-argument axiom-name)
   (:punctuation "."))
  (when (and *browse-snapshot*
             (in-log-p kind (browse-log *browse-snapshot*) axiom-name))
    (let ((next (copy-browse *browse-snapshot*)))
      (loop do
            (cond ((and (start-marker-p (car (browse-log next)))
                        (eq (first (third (car (browse-log next)))) kind)
                        (or (null axiom-name)
                            (eq axiom-name
                                (third (second (browse-log next))))))
                   (return))
                  ((or (and (start-marker-p (car (browse-log next)))
                            (let ((k (first (third (car (browse-log next))))))
                              (and (not (eq k 'simplify))
                                   (not (eq k 'match-true))
                                   (not (eq k 'match-false)))))
                       (end-marker-p (car (browse-log next))))
                   (pop (browse-log next)))
                  (t (setq next (browse-forward-aux next)))))
      (update-browse next)
      t)))

;;; Command to print the corresponding formula for the current snapshot.
(defcmd browse-print-formula ()
  ((:string "Prints the current browse formula, unless there is no
current browse (which is the case immediately after you reset)."))
  (unless (null *browse-snapshot*)
    (printer (list (list :string "The current formula is :")
                   (list :newline)))
    (printer (list (list :formula (browse-formula *browse-snapshot*))))))


;;; ========== Utility functions

(defun browse-level ()
  (and *browse-snapshot*
       (cond ((browse-at-top-level *browse-snapshot*) 0)
             (t (+ 1 (number-of-unmatched-end-markers
                      (browse-log *browse-snapshot*)))))))

(defun number-of-unmatched-end-markers (log)
  (let ((n 0))
    (loop for entry in log
          do (cond ((start-marker-p entry) (decf n))
                   ((end-marker-p entry) (incf n))))
    n))

;;; Return information about where we are in the browse.

(defun browse-where ()
  (and *browse-snapshot*
       (let ((command (display-command
                       (browse-current-display *browse-snapshot*))))
         (cond ((browse-at-top-level *browse-snapshot*)
                (list command 'start))
               ((null (browse-log *browse-snapshot*))
                (list command 'end))
               ((start-marker-p (car (browse-log *browse-snapshot*)))
                (list command
                      'enter-level
                      (+ 2 (number-of-unmatched-end-markers
                            (browse-log *browse-snapshot*)))
                      (first (third (car (browse-log *browse-snapshot*))))))
               ((end-marker-p (car (browse-log *browse-snapshot*)))
                (list command
                      'exit-level
                      (+ 1 (number-of-unmatched-end-markers
                            (browse-log *browse-snapshot*)))
                      (first (third (car (browse-log *browse-snapshot*))))))
               (t (list command
                        'at-level
                        (+ 1 (number-of-unmatched-end-markers
                              (browse-log *browse-snapshot*)))))))))

(defun browse-info ()
  (and *browse-snapshot*
       (cond ((browse-at-top-level *browse-snapshot*)
              (list 'begin (browse-formula *browse-snapshot*)))
             ((null (browse-log *browse-snapshot*))
              (list 'end (browse-formula *browse-snapshot*)))
             (t
              (let ((index (get-relative-index
                            (second (first (browse-log
                                            (car *browse-history*))))
                            (browse-base-index (car *browse-history*)))))
                (multiple-value-bind (expr assume)
                  (select-index index (browse-formula *browse-snapshot*))
                  assume
                  (format t "~%Result of step:")
                  (print expr)
                  (format t "~%indexed by ~A" index)))
              (let ((index (get-relative-index
                            (second (first (browse-log *browse-snapshot*)))
                            (browse-base-index *browse-snapshot*))))
                (multiple-value-bind (expr assume)
                  (select-index index (browse-formula *browse-snapshot*))
                  assume
                  (format t "~%Next step will be on:")
                  (print expr)
                  (format t "~%indexed by ~A" index)))))))

;;; Optional axiom-name only works for REWRITE and INVOKE.
(defun in-log-p (kind log &optional axiom-name)
  (loop for rest on log
        do (let ((entry (car rest)))
             (when (and (start-marker-p entry)
                        (eq (first (third entry)) kind)
                        (or (null axiom-name)
			    (and (or (eq kind 'rewrite)
				     (eq kind 'invoke))
				 (eq axiom-name (third (third entry))))))
               (return t)))))
