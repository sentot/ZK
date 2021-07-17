
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


(export '(zk-mode read-eval-zk-sexp evaluate-zk-sexp zk-read-all-examples
		  zk-read-all-examples-with-log-on
		  zk-read-all-examples-and-check
		  get-initial-theory-names get-subsidiary-declarations))

;;; Help string printed when starting up ZK.

(defparameter  *zk-help-string*
	      "
ZK command line interface.
Type \"(quit)\" to exit.
Type \"(help)\" for help.
")

;;; Commands for which aborts are disabled.
(defvar *abort-disabled-commands*
	(append *zk-declarations* '(RESET UNDO UNDO-BACK-TO UNDO-BACK-THRU)))

;;; Commands which return a declaration name to be printed.
(defvar *name-result-commands*
	(append *zk-declarations* '(UNDO UNDO-BACK-TO UNDO-BACK-THRU)))

;;; When non-nil, the (quit) command will ask for confirmation before
;;; exiting the ZK system.
(defvar *zk-confirm-quit* t)

;;; This flag is set to non-nil to exit from the main command loop.
(defvar *quit-command-loop*)

;;; When non-nil, we are scripting to a file.
(defvar *scripting* nil)

;;; When non-nil, it is a stream for scripting.
(defvar *script-stream* nil)

;;; Top-level function for entering the ZK command line interface.

(defun zk-mode (&optional directory-name)
  (when directory-name
    (when (eq (set-library-directory directory-name) :error)
      (format t "~%Current library is not set.")))
  (let ((*package* *zk-package*))
    (print-copyright)
    (zk-command-loop)))

;;; routine that prints the copyright notice

(defun print-copyright ()
  (format t "~%ZK version ~A" *zk-version*)
  (format t "~%~%======================================================================")
  (format t "~%|                                                                    |")
  (format t "~%| Copyright (c) 2021, Sentot Kromodimoeljo, William Pase,            |")
  (format t "~%|                     Mark Saaltink, Dan Craigen and Irwin Meisels.  |")
  (format t "~%|               All Rights Reserved.                                 |")
  (format t "~%|                                                                    |")
  (format t "~%|   Uses the following Common Lisp libraries:                        |")
  (format t "~%|    - trivial-gray-streams                                          |")
  (format t "~%|        Copyright (c) David Lichteblau (2005)                       |")
  (format t "~%|        Copyright (c) Anton Vodonosov (2013)                        |")
  (format t "~%|    - flexi-streams                                                 |")
  (format t "~%|        Copyright (c) Edmund Weitz (2005-2008)                      |")
  (format t "~%|    - salza2 (compression)                                          |")
  (format t "~%|        Copyright (c) Zachary Beane (2007)                          |")
  (format t "~%|    - chipz (decompression)                                         |")
  (format t "~%|        Copyright (c) Nathan Froyd (2004)                           |")
  (format t "~%|                                                                    |")
  (format t "~%======================================================================~%")
  (format t *zk-help-string*))

;;; Top-level function for entering the ZK system from an editor.

(defun zk-mode-for-editor ()
  (let ((*package* *zk-package*)
	(*zk-confirm-quit* nil))
    (zk-command-loop))
  (terpri))

;;; Top-level read and evaluation loop for ZK sexps.

(defun zk-command-loop ()
  (let ((*quit-command-loop* nil)
	status sexp)
    (with-zk-printer
      (loop until *quit-command-loop*
	  do (read-and-evaluate
	      *zk-help-string* "> "
	      (multiple-value-setq (status sexp)
		(parse-zk-sexp *standard-input*))
	      (when (eq status :OK)
		(evaluate-zk-sexp sexp))))))
  nil)

(defun zk-command-loop-for-scripting ()
  (loop with (status sexp)
	until (or *quit-command-loop*
		  (null *scripting*))
	do (read-and-evaluate
            *zk-help-string* "> "
	     (multiple-value-setq (status sexp)
	       (parse-zk-sexp *standard-input*))
	     (when (eq status :OK)
	       (evaluate-zk-sexp sexp)))))

;;; Read and evaluate a single ZK sexp.
;;; Does not evaluate script, end-script, and quit commands.
(defun read-eval-zk-sexp (&optional (input-stream *standard-input*))
  (let ((*package* *zk-package*)
	status sexp)
    (with-zk-printer
	(multiple-value-setq (status sexp) (parse-zk-sexp input-stream))
      (when (and (eq status :OK)
		 (not (member-eq (first sexp) '(script quit end-script))))
	(evaluate-zk-sexp sexp)))))

;;; Evaluate a ZK sexp. You can bound output-stream, for example if
;;; you are implementing an editor mode.

(defun evaluate-zk-sexp (sexp &optional (output-stream *standard-output*))
  (let (status prover-command-result)
    (with-zk-formatting
      (with-zk-help
	(when *scripting*
	  ;; Print the input sexp to the script file.
	  (let ((*standard-output* *script-stream*)
		(*format-output* nil))
	    (printer `((:command ,sexp)))))
	(setq status (wf-zk-sexp sexp))
	(unless (eq status :OK)
	  (return-from evaluate-zk-sexp nil))
	(let ((command (strip-modifiers sexp)))
	  (cond ((member-eq (first command) *abort-disabled-commands*)
		 ;; No aborts for uninterruptable commands.
		 (with-abort-disabled
		  (setq prover-command-result (zk-to-lisp sexp))
		  (unless prover-command-result
		    (return-from evaluate-zk-sexp nil))))
		(t
		 (setq prover-command-result (zk-to-lisp sexp))
		 (unless prover-command-result
		   (return-from evaluate-zk-sexp nil))))
	  ;; Print event name if required.
	  (when (member-eq (first command) *name-result-commands*)
	    (let ((*standard-output* output-stream))
	      (printer `((:event-name ,prover-command-result)))))
	  ;; For a declaration, immediately try it.
	  (when (member-eq (first command) *zk-declarations*)
	    (try (second command)))
	  prover-command-result)))))

;;; Functions for commands that modify the behaviour of the command loop.

(defpropfun (script zk-trans) (filename)
  (if *scripting*
      (format t "~%A script file is already open.")
    (let ((file (merge-pathnames filename)))
      (with-open-file (*script-stream* file :direction :output)
	(cond
	 (*script-stream*
	  (format t "~%Script file is open.")
	  (let ((*standard-output* (make-broadcast-stream *standard-output*
							  *script-stream*))
		(*scripting* t))
	    (zk-command-loop-for-scripting))
	  (format t "~%Script file is closed."))
	 (t
	  (file-error "create" file)))))))

(defpropfun (end-script zk-trans) ()
  (if *scripting*
      (setq *scripting* nil)
      (format t "~%No script file is open.")))

(defpropfun (quit zk-trans) ()
  (when (or (not *zk-confirm-quit*)
	    (yes-or-no-p "Exit ZK command processor? "))
    (setq *quit-command-loop* t)))

;;; Functions to read a ZK source file.

(defun zk-read (filename)
  (let ((file (merge-pathnames filename)))
    (with-open-file (x file :direction :input)
      (unless x
	(file-error "open" file)
	(return-from zk-read nil))
      (format t "~%Reading \"~A\"" filename)
      (read-file-loop x)
      (format t "~%Done."))))

;;; Useful to get timings without overhead of run-all-tests.
(defun zk-read-all-examples ()
  (let ((*package* *zk-package*))
    (set-library *zk-library-directory*)
    (loop for file in (files-in-test-directory
		       (merge-pathnames *zk-examples-files*))
	  do (progn (reset) (zk-read file)))))

;;; Useful to get timings without overhead of run-all-tests.
(defun zk-read-all-examples-with-log-on ()
  (let ((*package* *zk-package*))
    (set-library *zk-library-directory*)
    (log-on)
    (loop for file in (files-in-test-directory
		       (merge-pathnames *zk-examples-files*))
	  do (progn (reset) (zk-read file)))
    (log-off)))

;;; Useful to get timings without overhead of run-all-tests.
(defun zk-read-all-examples-and-check ()
  (let ((*package* *zk-package*))
    (set-library *zk-library-directory*)
    (log-on)
    (loop for file in (files-in-test-directory
		       (merge-pathnames *zk-examples-files*))
	  do (progn (reset) (zk-read file) (check-all-proofs)))
    (log-off)))

(defpropfun (read zk-trans) (filename)
  (zk-read filename))

(defun read-file-loop (stream)
  (loop with (status sexp)
	do (multiple-value-setq (status sexp) (parse-zk-sexp stream))
	when (eq status :OK) do (evaluate-zk-sexp sexp)
	until (eq status :EOF)))

;;; Function to be used for running tests.
(defun zk-loader (filename)
  (zk-fix-pos)
  (zk-read filename))

;;; Utility function for retrieving an axiom or function header.

(defun get-decl-header (name)
  (let ((event (get-event name)))
    (when event
      (let ((routine (get-event-property event 'zk-event)))
	(when routine
	  (case (first routine)
	    ((FUNCTION FUNCTION-STUB ZF-FUNCTION AXIOM RULE FRULE GRULE)
	     (list (first routine)
		   (second routine)
		   (zk-output-variables (third routine))))))))))


;;; Exported functions for front-end access to ZK data

;;; List of the names of events in the initial theory.
(defun get-initial-theory-names ()
  (mapcar #'event-name (system-history)))

;;; List of the names of events created along with event-name.
(defun get-subsidiary-declarations (event-name)
  (cdr (group-event-name-list (get-event event-name))))

;;; load-time initialization

(eval-when
 (:load-toplevel)
 (unless *compiling-zk*
   ;; Fix accessible POs for div, rem, etc.
   (zk-fix-pos))
)
