
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


;;; ==================== The Help System ====================

;;; The HELP database consists of:
;;; 1. A topic list: a list of topics and topic lists (i.e., a tree
;;;    of topics), bound to the variable *help-topic-list*.
;;; 2. A list of alists bound to the variable *help-alists*.
;;;    Each alist entry is (topic . (type explain)), which is
;;;    equivalent to (topic type explain).
;;; Possible values of type are defined in *help-types*, currently:
;;; 'prover-command, 'error-code, 'extra-help and 'proof-step.
;;; The explain part contains printer directives.

;;; The variables *help-topic-list* and *help-alists* can be bound
;;; differently for different syntax modes. Of course, the printer
;;; can also be bound differently.

;;; Use the minimum of *help-maximum-print-width* and the width of
;;; *standard-output*.

(defun help-print-width ()
  (min *help-maximum-print-width* (size-in-characters)))

;;; Access functions for help system variables.

(defun help-topic-list ()
  (or *help-topic-list* *lisp-mode-help-topic-list*))

(defun help-alist ()
  (or *help-alists* (list *lisp-mode-help-alist*)))

;;; Look up a item in each alist of a list of alists. If successful
;;; it will return (item type explain)
(defun assoc-eq-list (item lists &aux x)
  (dolist (l lists)
    (when (setq x (assoc-eq item l))
      (return-from assoc-eq-list x))))

;;; Ensure that every help topic in the topic list for a mode has help.  This
;;; function should only be evaluated at load time after everything is
;;; defined. A topic that has help need not be in the topic list.
(defun check-help-database (topic-list help-alists)
  (let ((topic-list (flatten topic-list)))
    (dolist (topic topic-list)
      (unless (assoc-eq-list topic help-alists)
	(format t "~%Missing help for topic:  ~A" topic)))))

;;; Create a printer directive list for the header line of a help topic.
(defun help-header (topic section)
  `(,@(when section `((:string ,section)))
    (:help-name ,topic)))

;;; Evaluate data in a printer directive list which have the form (:eval ...).
(defun print-help-mapping (explain)
  (mapcar #'(lambda (u)
	      (let ((dir (first u))
		    (val (second u)))
		(if (and (not (atom val)) (eq (first val) :eval))
		  (if (atom (second val))
		      (list dir (symbol-value (second val)))
		    (list dir (apply (car (second val)) (cdr (second val)))))
		  u)))
	  explain))

;;; Print the help for the given topic, assuming help for the topic
;;; is available.
(defun print-help (topic &optional section)
  (let ((explain (third (assoc-eq-list topic (help-alist)))))
    ;; unless the help has been disabled, print
    (unless (null explain)
      (printer (append '((:newline))
		       (help-header topic section)
		       '((:newline))
		       (print-help-mapping explain)
		       (unless section
			 (let ((context (help-manual-refer topic)))
			   (append (when (neq (car context) 'manual)
				     `((:paragraph)
				       (:string "For an overview, see")
				       (:help-name ,(car context))
				       (:punctuation ".")))
				   (when (not (atom (cadr context)))
				     `((:paragraph)
				       (:string "For more detailed
information, see")
				       (:help-name-list ,(cdadr context))
				       (:punctuation "."))))))
		       '((:separator)))
	       t
	       0
	       (help-print-width)))))

(defun help-print-number (section)
  (cond ((null section) "")
	(t (string-append (help-print-number (cdr section))
			  (format nil "~A." (car section))))))

;;; Print all help topics as an on-line manual. If textp is nil then
;;; only the table of contents is printed. Otherwise the sections are
;;; printed as well.
(defun help-print-manual (textp)
  (help-print-manual-tail (help-topic-list) '(0) textp))

(defun help-print-manual-aux (topic section textp)
  (cond ((atom topic)
	 (when (and textp (null (cdr section))) (princ ""))
	 (if textp
	     (print-help topic (help-print-number section))
	     (printer (append (when (null (cdr section))
				'((:newline) (:newline)))
			      (help-header topic (help-print-number section)))
		      t
		      0
		      (help-print-width))))
	(t (help-print-manual-aux (car topic) section textp)
	   (help-print-manual-tail (cdr topic) (cons 0 section) textp))))

(defun help-print-manual-tail (topic-list section textp)
  (cond ((null topic-list) nil)
	(t (help-print-manual-aux (car topic-list)
				  (cons (1+ (car section)) (cdr section))
				  textp)
	   (help-print-manual-tail (cdr topic-list)
				   (cons (1+ (car section)) (cdr section))
				   textp))))

(defun help-print-contents ()
  (printer `((:string "Table of Contents")
	     (:newline))
	   t
	   0
	   (help-print-width))
  (help-print-manual nil)
  (printer '((:separator)) t 0 (help-print-width)))


;;; Print explanation on main topics.
(defun help-print-main-sections ()
  (printer `((:string "The main topics available are:")
	     (:help-name-list ,(mapcar #'(lambda (u) (if (atom u) u (car u)))
				       (help-topic-list)))
	     (:punctuation ".")
	     (:separator))
	   t
	   0
	   (help-print-width)))

;;; Return the context of a topic in the manual. The context includes
;;; the enclosing topic and the immediate subtopics.
(defun help-manual-refer (topic)
  (help-manual-refer-tail topic (help-topic-list) 'manual))

(defun help-manual-refer-aux (topic topic-list header)
  (cond ((eq topic topic-list) (list header topic))
	((atom topic-list) nil)			;no such topic
	((eq topic (car topic-list))
	 (list header (help-manual-refer-strip topic-list)))
	(t (help-manual-refer-tail topic (cdr topic-list) (car topic-list)))))

(defun help-manual-refer-tail (topic topic-list-tail header)
  (cond ((null topic-list-tail) nil)
	(t (or (help-manual-refer-aux topic (car topic-list-tail) header)
	       (help-manual-refer-tail topic (cdr topic-list-tail) header)))))

(defun help-manual-refer-strip (topic-list)
  (mapcar #'(lambda (u) (if (atom u) u (car u))) topic-list))

;;; The command for help.
(defcmd help (&optional help-name)
  ((:string "Prints documentation for various topics from the
on-line help. Documentation may be requested for a specific topic
by supplying the topic. The entire on-line manual may be printed
by supplying")
   (:help-name manual)
   (:string "as the topic. The table of contents for the manual
may be printed by supplying")
   (:help-name contents)
   (:string "as the topic. If the topic is not a topic name, then")
   (:command-name help)
   (:string "will print a list of topics that contain the specified
topic as a substring. If the topic is not supplied, then the help for")
   (:help-name help)
   (:string "is printed and the main topics are listed."))
  (cond
   ((or (null help-name) (not (symbolp help-name)))
    ;; help on help
    (print-help 'help)
    (help-print-main-sections))
   ((eq help-name 'contents)
    ;; table of contents
    (help-print-contents))
   ((eq help-name 'manual)
    ;; entire manual
    (help-print-contents)
    (help-print-manual t))
   ((and (assoc-eq-list help-name (help-alist))
	 (help-manual-refer help-name))
    (print-help help-name))
   (t
    (let ((help-list
	   (remove-if-not #'(lambda (u) (string-search-equal help-name u))
			  (mapcar #'(lambda (u) (intern (string u)
							*zk-package*))
				  (flatten (help-topic-list))))))
      ;; No help for speicified topic.
      (printer (append `((:string "The topic")
			 (:help-name ,help-name)
			 (:string "has no help."))
		       (when (not (null help-list))
			 `((:newline)
			   (:string "Suggest getting help on any of")
			   (:help-name-list ,help-list)
			   (:punctuation "."))))
	       t
	       0
	       (help-print-width)))))
  nil)

;;; More help utilities.

;;; Return a list of syntax for commands.
(defun get-syntax ()
  (let ((help-names (unique (flatten (help-topic-list)))))
    (loop for help-name in help-names
	  for help = (assoc-eq-list help-name (help-alist))
	  when (eq (caar (third help)) :syntax) collect (cadar (third help)))))

;;; Return a list of sorted syntax for commands
(defun get-sorted-syntax ()
  (sort (get-syntax)
	#'(lambda (u v) (alphalessp (string (car u)) (string (car v))))))


;;; ==================== Lisp Mode Help ====================

;;; Just help for running tests.

(defparameter *lisp-mode-help-topic-list*
  '(
    help
    (testing
     make-test-file
     run-test-file
     run-all-tests-directory
     run-all-tests)
    ))

(defmacro with-lisp-mode-help (&body body)
  `(let ((*help-topic-list* *lisp-mode-help-topic-list*)
	 (*help-alists* (list *lisp-mode-help-alist*)))
     ,@body))

;;; Testing

(defhelp testing extra-help
  ((:newline)
   (:string "The testing commands permit users, and especially developers
of the theorem prover and examples, to check the effects of changes to either
the prover or the examples. The commands report any differences between
the prover database resulting from an example when compared to the reference
version of the same example.")))
