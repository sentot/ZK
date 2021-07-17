
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

;;; This file contains the prettyprinters for Lisp and ZK mode. It
;;; uses ANSI Common Lisp's pretty printing features (also in CLtL2).
;;;
;;; This file also contains the general error message printer.
;;;
;;; A prettyprinter is given a list of printer directives (defined in
;;; structures.lisp) with associated data.
;;;
;;; To use a prettyprinter, bind the variable *printer* (also defined
;;; in structures.lisp) to its function value, and then the function
;;; (printer) can be used to print. The macros with-lisp-printer and
;;; with-zk-printer are defined to do this.
;;;
;;; The (printer) function also allows the *format-output* variable
;;; to be bound to a function which does output formatting, if
;;; required.


;;; Allows echoing to stream.
(defvar *echo-stream* nil)

;;; Get the print function for a directive

(defmacro get-print (d)
  `(get ,d 'zk-print))

(defvar *pp-line-width* 79)

(defvar *pp-max-depth* nil)    ; depth limit for sexp printing
(defvar *pp-max-breadth* nil)  ; breadth limit for sexp printing
(defvar *pp-arg-indent* 2)     ; extra indent for argument lists
                               ; and annotations
(defvar *pp-printing-zk* nil)  ; t -> printing zk sexps

;;; Test and decrement a depth or breadth limit.

(defun opt-count-expiredp (x)
  (and x (<= x 0)))

(defun drop-opt-count (x &optional (n 1))
  (and x (- x n)))

;;; Return T if the argument character is a non-whitespace printing character,
;;; nil otherwise.

(defun word-char-p (c)
  (and (graphic-char-p c)
       (not (char-equal c #\space))))

;;; Break up a string into a list of words; each word is a string made up of
;;; nonblank graphic-char-p characters.

(defun word-list-from-string (s)
  (let ((start 0)
	(end 0)
	(length (string-length s)))
    (loop
       do (setq start end)
	  (loop until (or (>= start length)
			  (word-char-p (char s start)))
		do (incf start))
       when (>= start length) return words
       do (setq end start)
	  (loop until (or (>= end length)
			  (not (word-char-p (char s end))))
		do (incf end))
       collect (substring s start end) into words)))

;;; Print a number.

(defun pp-number (n)
  (pp-print-string (format nil "~D" n)))


;;; ===================================================================

;;; Top-level functions for printing in Lisp and ZK modes.

(defun lisp-printer (x &optional (nl t) indent max-width max-depth max-breadth)
  (let ((*print-right-margin* (or max-width (size-in-characters)))
        (*pp-max-depth* max-depth)
        (*pp-max-breadth* (drop-opt-count max-breadth))
	;; Not printing in ZK syntax
        (*pp-printing-zk* nil)
	(first t))
    (when nl (write-char #\Newline))
    (pprint-logical-block (nil x)
      (when indent
        (loop for i from 1 to indent
              do (write-char #\space))
        (pprint-indent :current 0))
      (loop do (progn (pprint-exit-if-list-exhausted)
		      (pp-directive (pprint-pop) first)
		      (setq first nil))))))

(defmacro with-lisp-printer (&body body)
  `(let ((*printer* #'lisp-printer))
     ,@body))

(defun zk-printer (x &optional (nl t) indent max-width max-depth max-breadth)
  (let ((*print-right-margin* (or max-width (size-in-characters)))
        (*pp-max-depth* max-depth)
        (*pp-max-breadth* (drop-opt-count max-breadth))
	;; Printing in ZK syntax.
        (*pp-printing-zk* t)
	(first t))
    (when nl (write-char #\Newline))
    (pprint-logical-block (nil x)
      (when indent
        (loop for i from 1 to indent
              do (write-char #\space))
        (pprint-indent :current 0))
      (loop do (progn (pprint-exit-if-list-exhausted)
		      (pp-directive (pprint-pop) first)
		      (setq first nil))))))

(defmacro with-zk-printer (&body body)
  `(let ((*printer* #'zk-printer))
     ,@body))

;;; Format for output and print a directive list, using the current printer.
;;; By default, the generic sexp printer is used, with no output formatting.

(defun printer (directives &optional (nl t) indent max-width max-depth
			   max-breadth)
  (funcall (or *printer* #'lisp-printer)
           (if *format-output*
               (funcall *format-output* directives)
             directives)
           nl indent max-width max-depth max-breadth)
  (when (and (streamp *echo-stream*) (output-stream-p *echo-stream*))
    (let ((*standard-output* *echo-stream*))
      (funcall (or *printer* #'lisp-printer)
	       (if *format-output*
		   (funcall *format-output* directives)
		 directives)
	       nl indent max-width max-depth max-breadth))))

(defmacro with-echo-printing (stream &body body)
  `(let ((*echo-stream* ,stream))
     ,@body))

;;; Function for printing error messages. All error reporting functions should
;;; use this function for printing the message, and then do their own extra
;;; stuff.  error-type is the name of the error, object is an object passed to
;;; the error, name is the name reported in the error message (it may be a
;;; list), and warning indicates the message is only a warning.

(defun print-error (error-type &optional object name warning)
  (unless (and warning (null *print-parser-warnings-flag*))
    (printer (append (list (list :string (if warning "Warning" "Error")))
		     (list (list :help-name error-type))
		     (and name
			  (list (list :string (if warning "for" "in"))))
		     (and name
			  (if (atom name)
			      (list (list :event-name name))
                            (list (list :event-name-list name))))
		     (list (list :punctuation ":"))
		     (list (list :newline))
		     (print-error-aux error-type object warning))))
  nil)

;;; Return the explanation for the given error-type with the objects supplied.
;;; If there is no such error then say so and print all of the objects as
;;; strings.

(defun print-error-aux (error-type object warning)
  (let ((error (get error-type 'error)))
    (cond (error (funcall error object))
          ;; it is always possible that an error was not defined
          (t `((:string "*** No message is available for this")
               (:string ,(if warning "warning ***:" "error ***:"))
               (:string ,(format nil "~A" object)))))))

(defun file-error (action file)
  (print-error 'file-error (cons action (namestring file))))

;;; Print data from the argument list using prfn, and separate the items using
;;; sepfn.

(defun pp-separated (data prfn sepfn)
  (funcall prfn (car data))
  (dolist (x (cdr data))
    (funcall sepfn)
    (funcall prfn x)))

(defun pp-print-string (str)
  (loop for i from 0 to (- (length str) 1)
	do (write-char (aref str i))))

(defun pp-print-strings (list)
  (unless (null list)
    (pp-print-string (car list))
    (loop for str in (cdr list)
	  do (progn (write-char #\space)
		    (pprint-newline :fill)
		    (pp-print-string str)))))

;;; Return true if the argument must be quoted on output.

(defun pp-quotable (x)
  (or (consp x)
      (and (symbolp x)
           (not (eq x t))
           (not (eq x nil)))))

;;; Apply a print function to a command argument, prefixing the output with a
;;; quote if we are not printing ZK commands, the argument is quoted, and
;;; the argument must be quoted on output.

(defun pp-quoted (prfn data)
  (cond
   ((and (not *pp-printing-zk*)
         (eq (car data) 'quote))
    (when (pp-quotable (second data))
      (write-char #\'))
    (funcall prfn (second data)))
   (t
    (funcall prfn data))))

;;; A space (or newline, if the first directive) is emitted before each
;;; directive except for those in this list.

(defvar *no-prefix-directives*
    '(:space :newline :paragraph :punctuation :separator))

;;; After a directive in the following list is processed, we are sure to be
;;; on a fresh line.

(defvar *fresh-line-directives*
    '(:newline :paragraph :separator :command-list :syntax-list))

;;; Interpret a printer directive, and print the result.

(defun pp-directive (directive first)
  (unless (or first (member-eq (car directive) *no-prefix-directives*))
    (write-char #\space))
  (apply (get-print (car directive)) (cdr directive)))


;;; Directive printing functions

(defpropfun (:space zk-print) ()
  (write-char #\space))

(defpropfun (:newline zk-print) ()
  (pprint-newline :mandatory)
  ;;(write-char #\Newline)
  )

(defpropfun (:paragraph zk-print) ()
  (pprint-newline :mandatory)
  (pprint-newline :mandatory))

(defpropfun (:punctuation zk-print) (x)
  (write-char (aref x 0)))

(defpropfun (:separator zk-print) ()
  (pprint-newline :mandatory)
  (pp-print-string (make-string *pp-line-width* :initial-element #\-))
  (pprint-newline :mandatory))

(defpropfun (:string zk-print) (x)
  (pp-print-strings (word-list-from-string x)))

(defpropfun ((:event :command) zk-print) (x)
  (pp-cmd x))

(defpropfun (:formula zk-print) (x)
  (pp-sexp x))

(defpropfun (:syntax zk-print) (x)
  (pp-syntax x))

(defpropfun (:formula-list zk-print) (x)
  (pprint-logical-block (nil x)
    (pprint-exit-if-list-exhausted)
    (pp-sexp (pprint-pop))
    (pprint-exit-if-list-exhausted)
    (loop do
	  (progn (write-char #\space)
		 (pprint-newline :fill)
		 (pp-sexp (pprint-pop))
		 (pprint-exit-if-list-exhausted)))))

(defpropfun (:command-list zk-print) (x)
  (pprint-logical-block (nil x)
    (pprint-exit-if-list-exhausted)
    (pp-cmd (pprint-pop))
    (pprint-newline :mandatory)
    (pprint-exit-if-list-exhausted)
    (loop do
	  (progn (pp-cmd (pprint-pop))
		 (pprint-newline :mandatory)
		 (pprint-exit-if-list-exhausted)))))

(defpropfun (:syntax-list zk-print) (x)
  (pprint-logical-block (nil x)
    (pprint-exit-if-list-exhausted)
    (pp-syntax (pprint-pop))
    (pprint-newline :mandatory)
    (pprint-exit-if-list-exhausted)
    (loop do
	  (progn (pp-syntax (pprint-pop))
		 (pprint-newline :mandatory)
		 (pprint-exit-if-list-exhausted)))))

(defpropfun ((:event-name :help-name :command-name) zk-print) (x)
  (pp-print-string (string x)))

(defpropfun (:command-argument zk-print) (x)
  (if *pp-printing-zk*
      (pp-print-string (string-downcase (string x)))
    (pp-print-string (string x))))

(defpropfun ((:event-name-list :help-name-list :command-name-list
			       :command-argument-list) zk-print)
  (x)
  (let ((sexp (car x)))
    (unless (null sexp) (pp-print-string (string sexp))))
  (loop for sexp in (cdr x)
	do
	(progn (write-char #\,)
	       (write-char #\space)
	       (pprint-newline :fill)
	       (pp-print-string (string sexp)))))

;;; Print a command or declaration.

(defun pp-cmd (cmd &aux fn)
  (cond
   ((setq fn (get-print (car cmd)))
    ;; special-cased command
    (funcall fn cmd))
   (t
    (pp-sexp cmd))))

;;; Print a syntax entry.

(defun pp-syntax (s)
  (cond
   ((symbolp s)
    (pp-print-string (string s)))
   (t
    (pprint-logical-block (nil s :prefix "(" :suffix ")")
      (pprint-exit-if-list-exhausted)
      (pp-print-string (string (pprint-pop)))
      (loop do (progn (pprint-exit-if-list-exhausted)
		      (write-char #\space)
		      (pprint-newline :fill)
		      (pp-syntax (pprint-pop))))))))

;;; General sexp printer. Should not be used for variable lists and other lists
;;; which start with a variable.

(defun pp-sexp (sexp &optional (depth *pp-max-depth*)
                               (quoted-arg-p (not *pp-printing-zk*)))
  (cond
   ((consp sexp)
    (cond
     ((opt-count-expiredp depth)
      (write-char #\#))                    ; depth cutoff
     ((and (eq (car sexp) 'quote) quoted-arg-p)
      (when (pp-quotable (second sexp))
        (write-char #\'))
      (pp-sexp (second sexp) depth nil))
     ((null (cdr sexp))                 ; no arguments
      (pprint-logical-block (nil sexp :prefix "(" :suffix ")")
			    (pp-sexp (pprint-pop) (drop-opt-count depth)
				     quoted-arg-p)
			    (pprint-exit-if-list-exhausted)))
     ((member-eq (car sexp) '(all some))
      (pp-quantification sexp))
     ((symbolp (car sexp))              ; function application
      (pprint-logical-block (nil sexp :prefix "(" :suffix ")")
        (pp-print-string (string (pprint-pop)))
        (let ((breadth *pp-max-breadth*)
	      (d (drop-opt-count depth))
	      (done nil))
          (loop for s = (pprint-pop)
		while (not done)
                do
                (progn (setq breadth (drop-opt-count breadth))
		       (cond ((opt-count-expiredp breadth)
			      (pp-print-string "...")
			      (setq done t))
			     (t (write-char #\space)
                                (pprint-newline :fill) ; was miser
                                (pp-sexp s d quoted-arg-p)))
		       (pprint-exit-if-list-exhausted))))))
     (t                                 ; non-trivial function expression
      (pprint-logical-block (nil sexp :prefix "(" :suffix ")")
        (pp-sexp (pprint-pop) (drop-opt-count depth) quoted-arg-p)
        (let ((breadth *pp-max-breadth*)
	      (d (drop-opt-count depth))
	      (done nil))
          (loop for s = (pprint-pop)
		while (not done)
                do
                (progn (setq breadth (drop-opt-count breadth))
		       (cond ((opt-count-expiredp breadth)
			      (pp-print-string "...")
			      (setq done t))
			     (t (write-char #\space)
                                (pprint-newline :fill) ; was miser
                                (pp-sexp s d quoted-arg-p)))
		       (pprint-exit-if-list-exhausted))))))))
   ((symbolp sexp)
    (pp-print-string (string sexp)))
   ((numberp sexp)
    (pp-number sexp))
   ((stringp sexp)
    (pp-print-string (format nil "~S" sexp)))
   (t
    (error "invalid sexp: ~A" sexp))))

;;; Print a quantification, in Lisp or ZK syntax.

(defun pp-quantification (sexp)
  (pprint-logical-block (nil sexp :prefix "(" :suffix ")")
    (pp-print-string (string (pprint-pop)))
    (write-char #\space)
    (let ((vars (pprint-pop)))
      (cond ((consp vars)
	     (pp-variables vars))
	    (t
	     (pp-variables (list vars)))))
    (write-char #\space)
    (pprint-newline :fill)
    (pp-sexp (pprint-pop))
    (pprint-exit-if-list-exhausted)))

;;; Print a list of variables.

(defun pp-variables (vars)
  (cond ((and (eq (first vars) 'quote) (not *pp-printing-zk*))
	 (pprint-logical-block (nil (second vars) :prefix "'(" :suffix ")")
	   (pprint-exit-if-list-exhausted)
	   (pp-print-string (string (pprint-pop)))
	   (loop do (progn (pprint-exit-if-list-exhausted)
			   (write-char #\space)
			   (pprint-newline :fill)
			   (pp-print-string (string (pprint-pop)))))))
	(t
	 (pprint-logical-block (nil vars :prefix "(" :suffix ")")
	   (pprint-exit-if-list-exhausted)
	   (pp-print-string (string (pprint-pop)))
	   (loop do (progn (pprint-exit-if-list-exhausted)
			   (write-char #\space)
			   (pprint-newline :fill)
			   (pp-print-string (string (pprint-pop)))))))))

;;; Prettyprinting functions for Lisp and ZK events and commands that
;;; require special treatment.

;;; function declarations

(defpropfun ((function function-stub) zk-print) (dcl)
  (pprint-logical-block
   (nil dcl :prefix "(" :suffix ")")
   (pp-print-string (string (pprint-pop)))
   (pprint-indent :block 1)
   (write-char #\space)
   (pprint-newline :fill)
   (pp-sexp (pprint-pop))
   (write-char #\space)
   (pprint-newline :fill)
   (pp-variables (pprint-pop))
   (write-char #\space)
   (pprint-newline :fill)
   (when (eq (first dcl) 'function)
     (pp-annotations (pprint-pop))
     (write-char #\space)
     (pprint-newline :linear)
     (pp-sexp (pprint-pop)))
   (pprint-exit-if-list-exhausted)))

(defpropfun (zf-function zk-print) (dcl)
  (pprint-logical-block
   (nil dcl :prefix "(" :suffix ")")
   (pp-print-string (string (pprint-pop)))
   (pprint-indent :block 1)
   (write-char #\space)
   (pprint-newline :fill)
   (pp-sexp (pprint-pop))
   (write-char #\space)
   (pprint-newline :fill)
   (pp-variables (pprint-pop))
   (write-char #\space)
   (pprint-newline :linear)
   (pp-zf-body (pprint-pop))
   (pprint-exit-if-list-exhausted)))

(defun pp-annotations (anns)
  (pprint-logical-block
   (nil anns :prefix "(" :suffix ")")
   (pprint-exit-if-list-exhausted)
   (pp-sexp (pprint-pop))
   (pprint-indent :block 0)
   (loop do (progn (pprint-exit-if-list-exhausted)
		   (write-char #\space)
		   (pprint-newline :mandatory)
		   (pp-sexp (pprint-pop))))))

(defun pp-zf-body (body)
  (pprint-logical-block (nil body :prefix "(" :suffix ")")
    (pp-print-string (string (pprint-pop)))
    (case (first body)
      (map
       (write-char #\space)
       (pprint-newline :fill)
       (pp-sexp (pprint-pop))
       (loop do (progn (pprint-exit-if-list-exhausted)
		       (let ((x (pprint-pop)))
			 (pprint-newline :mandatory)
			 (pprint-logical-block
			  (nil x :prefix "(" :suffix ")")
			  (pp-variables (pprint-pop))
			  (write-char #\space)
			  (pprint-newline :fill)
			  (pp-sexp (pprint-pop))
			  (pprint-exit-if-list-exhausted))))))
      (select
       (write-char #\space)
       (pprint-newline :miser)
       (let ((x (pprint-pop)))
	 (pprint-logical-block (nil x :prefix "(" :suffix ")")
	   (pp-print-string (string (pprint-pop)))
           (write-char #\space)
	   (pprint-newline :fill)
	   (pp-sexp (pprint-pop))
	   (pprint-exit-if-list-exhausted)))
       (write-char #\space)
       (pprint-newline :linear)
       (pp-sexp (pprint-pop)))
      (that
       (write-char #\space)
       (pprint-newline :miser)
       (pp-print-string (string (pprint-pop)))
       (write-char #\space)
       (pprint-newline :miser)
       (pp-sexp (pprint-pop)))
      (t
       (error "invalid zf function body: ~A" body)))
    (pprint-exit-if-list-exhausted)))

;;; axiom declarations

(defpropfun ((axiom rule frule grule) zk-print) (cmd)
  (pprint-logical-block
   (nil cmd :prefix "(" :suffix ")")
   (pp-print-string (string (pprint-pop)))
   (pprint-indent :block 1)
   (write-char #\space)
   (pprint-newline :fill)
   (pp-sexp (pprint-pop))
   (write-char #\space)
   (pprint-newline :fill)
   (pp-variables (pprint-pop))
   (pprint-indent :block 0)
   (write-char #\space)
   (pprint-newline :linear)
   (pp-sexp (pprint-pop))
   (pprint-exit-if-list-exhausted)))

(defpropfun (name zk-print) (cmd)
  (pprint-logical-block
   (nil (cdr cmd) :prefix "(" :suffix ")")
   (pp-print-string "NAME")
   (pprint-indent :block 1)
   (write-char #\space)
   (pprint-newline :fill)
   (pp-sexp (pprint-pop))
   (write-char #\space)
   (pprint-newline :fill)
   (pp-variables (pprint-pop))
   (pprint-exit-if-list-exhausted)
   (write-char #\space)
   (pprint-newline :linear)
   (pp-sexp (pprint-pop))
   (pprint-exit-if-list-exhausted)))

;;; system commands

(defpropfun (instantiate zk-print) (cmd)
  (pprint-logical-block (nil (cdr cmd) :prefix "(" :suffix ")")
    (pp-print-string "INSTANTIATE")
    (write-char #\space)
    (pprint-newline :miser)
    (cond 
     (*pp-printing-zk*
      (pp-instantiation (pprint-pop))
      (loop do (progn (pprint-exit-if-list-exhausted)
		      (write-char #\space)
		      (pprint-newline :miser)
		      (pp-instantiation (pprint-pop)))))
     (t
      (let ((i (pprint-pop)))
	(pprint-logical-block
	 (nil (second i) :prefix "'(" :suffix ")")
	 (pp-instantiations (second i))
	 (pprint-exit-if-list-exhausted))
	(pprint-exit-if-list-exhausted))))))

(defpropfun ((assume use) zk-print) (cmd)
  (pprint-logical-block
   (nil cmd :prefix "(" :suffix ")")
   (pp-sexp (pprint-pop))
   (write-char #\space)
   (pprint-newline :miser)
   (pp-sexp (pprint-pop))
   (pprint-exit-if-list-exhausted)
   (cond
    (*pp-printing-zk*
     (write-char #\space)
     (pprint-newline :linear)
     (pp-instantiation (pprint-pop))
     (loop do (progn (pprint-exit-if-list-exhausted)
		     (write-char #\space)
		     (pprint-newline :miser)
		     (pp-instantiation (pprint-pop)))))
     (t
      (write-char #\space)
      (pprint-newline :linear)
      (let ((i (pprint-pop)))
	(pprint-logical-block
	 (nil (second i) :prefix "'(" :suffix ")")
	 (pp-instantiations (second i))
	 (pprint-exit-if-list-exhausted)))))))

(defun pp-instantiations (inst)
  (pp-instantiation (car inst))
  (loop for i in (cdr inst)
	do
	(progn (write-char #\space)
               (pprint-newline :fill)
	       (pp-instantiation i))))

(defun pp-instantiation (x)
  (pprint-logical-block
   (nil x :prefix "(" :suffix ")")
   (pp-print-string (string (pprint-pop)))
   (write-char #\space)
   (pprint-newline :miser)
   (cond ((= (length x) 3) ; Lisp syntax
	  (pp-print-string (string (pprint-pop)))
	  (write-char #\space)
	  (pprint-newline :fill)
	  (pp-sexp (pprint-pop) *pp-max-depth* nil))
	 (t                ; ZK syntax
	  (pp-sexp (pprint-pop) *pp-max-depth* nil)))
   (pprint-exit-if-list-exhausted)))

;;; command modifiers

(defpropfun ((disabled with-case-analysis with-instantiation
		       without-case-analysis without-instantiation) zk-print)
  (cmd)
  (pprint-logical-block
   (nil cmd :prefix "(" :suffix ")")
   (pp-print-string (string (pprint-pop)))
   (pprint-indent :block 1)
   (pprint-newline :mandatory)
   (pp-cmd (pprint-pop))
   (pprint-exit-if-list-exhausted)))

(defpropfun ((with-disabled with-enabled) zk-print)
  (cmd)
  (pprint-logical-block
   (nil cmd :prefix "(" :suffix ")")
   (pp-print-string (string (pprint-pop)))
   (pprint-indent :block 1)
   (write-char #\space)
   (pprint-newline :fill)
   (cond
    (*pp-printing-zk*
     (pp-variables (pprint-pop)))
    (t
     (let ((i (pprint-pop)))
       (pprint-logical-block
	(nil (cdr i) :prefix "'(" :suffix ")")
	(pp-variables (pprint-pop))
	(pprint-exit-if-list-exhausted)))))
    (pprint-indent :block 0)
    (pprint-newline :mandatory)
    (pp-cmd (pprint-pop))
    (pprint-exit-if-list-exhausted)))

(defpropfun (with-subexpression zk-print)
  (cmd)
  (pprint-logical-block
   (nil cmd :prefix "(" :suffix ")")
   (pp-print-string (string (pprint-pop)))
   (pprint-indent :block 1)
   (write-char #\space)
   (pprint-newline :fill)
   (cond
    (*pp-printing-zk*
     (pp-sexp (pprint-pop) *pp-max-depth* nil))
    (t
     (let ((i (pprint-pop)))
       (pprint-logical-block
	(nil (cdr i) :prefix "'(" :suffix ")")
        (pp-sexp (pprint-pop) *pp-max-depth* nil)
	(pprint-exit-if-list-exhausted))))
    (pprint-indent :block 0)
    (pprint-newline :mandatory)
    (pp-cmd (pprint-pop))
    (pprint-exit-if-list-exhausted))))

(defun pp-test (x &optional max-width max-depth max-breadth)
  (let ((*pp-max-depth* max-depth)
        (*pp-max-breadth* (drop-opt-count max-breadth))
        (*pp-line-width* (or max-width (size-in-characters)))
        (*pp-printing-zk* t))
    (pp-cmd x)))
