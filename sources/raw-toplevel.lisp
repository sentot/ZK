
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

(export 'raw-mode)

(defvar *raw-printer-output*)


;;; This flag is set to non-nil to exit from the main command loop.

(defvar *raw-quit-command-loop*)

;;; When this variable is non-nil, we are scripting to a file.

(defvar *raw-scripting* nil)

;;; When this variable is non-nil, it is a stream for scripting.

(defvar *raw-script-stream* nil)

;;; Just push printer directives to *raw-printer-output*. After
;;; evaluation, the list will be reversed and printed as is.
(defun raw-printer (x &optional indent max-line-width max-depth max-breadth)
  (declare (ignore indent max-line-width max-depth max-breadth))
  (push x *raw-printer-output*))

(defmacro with-raw-printer (&body body)
  `(let ((*printer* #'raw-printer)
	 (*raw-printer-output* nil))
     ,@body))

;;; Top-level function for raw ZK mode.
(defun raw-mode ()
  (let ((*package* *zk-package*))
    (raw-command-loop)))

;;; Top-level read and evaluation loop for raw mode.
(defun raw-command-loop ()
  (let ((*raw-quit-command-loop* nil)
	status sexp)
    (with-raw-printer
      (loop until *raw-quit-command-loop*
	  do (setq *raw-printer-output* nil)
	  do (read-and-evaluate
	      "" ""
	      (multiple-value-setq (status sexp)
		(parse-zk-sexp *standard-input*))
	      (when (eq status :OK)
		(raw-evaluate-sexp sexp)))
          do (print (apply #'append (reverse *raw-printer-output*))))))
  nil)

;;; Command loop for scripting.
(defun raw-command-loop-for-scripting ()
  (with-raw-printer
    (loop with (status sexp)
	until (or *raw-quit-command-loop*
		  (null *raw-scripting*))
	do (setq *raw-printer-output* nil)
	do (read-and-evaluate
	    "" ""
	    (multiple-value-setq (status sexp)
	      (parse-zk-sexp *standard-input*))
	    (when (eq status :OK)
	      (raw-evaluate-sexp sexp)))
        do (print (apply #'append (reverse *raw-printer-output*))))))

;;; Command loop for reading a file.
(defun raw-read-file-loop (stream)
  (loop with (status sexp)
      do (multiple-value-setq (status sexp) (parse-zk-sexp stream))
      when (eq status :OK) do (raw-evaluate-sexp sexp)
      until (eq status :EOF)))

;;; Evaluate a command that modifies the behaviour of the front-end directly,
;;; or pass it to ZK if it doesn't.
(defun raw-evaluate-sexp (sexp)
  (case (first sexp)
    (script
     (cond
      (*raw-scripting*
       (printer '((:string "A script file is already open."))))
      (t
       (with-open-file (*raw-script-stream* (merge-pathnames (second sexp))
			:direction :output)
	 (unless *raw-script-stream*
	   (file-error "create" (merge-pathnames (second sexp)))
	   (return-from raw-evaluate-sexp nil))
	 (print '((:string "Script file is open.")))
	 (let ((*standard-output* (make-broadcast-stream
				   *standard-output* *raw-script-stream*))
	       (*raw-scripting* t))
	   (raw-command-loop-for-scripting))
	 (print '((:string "Script file is closed.")))
	 ))))
    (end-script
     (if *raw-scripting*
	 (setq *raw-scripting* nil)
       (printer '((:string "No script file is open.")))))
    (quit
     (setq *raw-quit-command-loop* t))
    (read
     (with-open-file (x (merge-pathnames (second sexp)) :direction :input)
       (unless x
	 (file-error "open" (merge-pathnames (second sexp)))
	 (return-from raw-evaluate-sexp nil))
       (printer `((:string "Reading") (:string ,(second sexp))))
       (raw-read-file-loop x)
       (printer '((:string "Done.")))))
    (t
     (evaluate-zk-sexp sexp))))
