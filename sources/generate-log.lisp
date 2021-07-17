
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

;;; Code to generate source and log files for the proof checker.

(defvar *paren-level* 0)

(defvar *ungenvar-base-for-log* (intern ")GV" *package*))

(defvar *ungenvar-base-string-for-log* "GV")

(defvar *ungenvar-index-for-log* 0)

(defun ungenvar-base-for-log ()
  (let ((st "GV"))
    (cond ((get-rename *ungenvar-base-for-log*)
           (loop for number = 0 then (1+ number)
                 for new = (intern (format nil ")~A~D" st number)
				   *zk-package*)
                 until (not (get-rename new))
                 finally (return new)))
          (t *ungenvar-base-for-log*))))

(defcmd dump-log (name)
  ((:string "The")
   (:command-name dump-log)
   (:string "command saves the declarations and proof logs from the
current theory into files for input to an independent proof checker.
The declarations are saved into a file with a \".src.gz\" extension, while
the proof logs are saved into a file with a \".plg.gz\" extension.
Both files are compressed using the gzip format."))
  (update-proof-status)
  (let* ((path (merge-pathnames name))
	 (*ungenvar-base-for-log* (ungenvar-base-for-log))
	 (srcpath (make-pathname :type "src.gz"
				 :version :newest
				 :defaults path))
	 (plgpath (make-pathname :type "plg.gz"
				 :version :newest
				 :defaults path)))
  (with-open-file
   (srcout srcpath :direction :output :if-exists :supersede
	   :element-type '(unsigned-byte 8))
   (salza2:with-compressor
    (srccomp 'salza2:gzip-compressor
	     :callback (salza2:make-stream-output-callback srcout))
    (with-open-file
     (plgout plgpath :direction :output :if-exists :supersede
	     :element-type '(unsigned-byte 8))
     (salza2:with-compressor
      (plgcomp 'salza2:gzip-compressor
	       :callback (salza2:make-stream-output-callback plgout))
      (let ((*paren-level* 0)
	    (*ugenvar-base-string-for-log*
	     (substring (string *ungenvar-base-for-log*) 1)))
	(loop for group in (reverse (user-history))
	      do (process-regular-extension group srccomp plgcomp))
	name)))))))

(defparameter *decls-with-internal-axioms*
  '(function rule frule grule))

;;; Syntax of regular extension:
;;;   (DECL ([rawpo po]) (theory-extension*) (additional-axioms*)) or
;;;   ((LOAD unit) (load-extension*))

(defun process-regular-extension (group srccomp plgcomp)
  (let ((decl (get-event-property (group-event group) 'zk-event)))
    (open-paren srccomp)
    (dump-decl decl srccomp)
    (cond
     ((eq (car decl) 'load)
      (open-paren srccomp)
      (loop for g in (cdar group)
	    do (process-load-extension g srccomp))
      (close-paren srccomp))
     (t
      (open-paren srccomp)
      ;; RAWPO
      (loop for name in (event-ponames (group-event group))
            do (dump-decl
		(zk-format-event
		 (make-axiom
		  :name (intern (format nil "~A.RAWPO" name) *zk-package*)
		  :kind 'axiom
		  :args nil
		  :formula (closed-form (event-rawpo (get-event name)))))
		srccomp))
      ;; PO
      (loop for name in (event-ponames (group-event group))
            do
	    (dump-decl
	     (zk-format-event
	      (make-axiom
	       :name (intern (format nil "~A.PO" name) *zk-package*)
	       :kind 'axiom
	       :args nil
	       :formula (closed-form (event-formula (get-event name)))))
	     srccomp)
	    ;; First proof log is for RAWPO -> PO
	    ;; Second proof if present is for discharging PO.
            (dump-proof-log-event (get-event name) plgcomp))
      (close-paren srccomp)
      ;; --- Theory Extension
      (open-paren srccomp)
      ;; implicit definition axiom
      (dump-definition-axiom decl (get-event (second decl)) srccomp)
      ;; explicit definition axiom
      (loop for event in (cdr group)
	    do (process-theory-extension event srccomp))
      (close-paren srccomp)
      ;; --- Additional Axioms
      (open-paren srccomp)
      ;; internal axioms
      (when (member-eq (car decl) *decls-with-internal-axioms*)
	(dump-internal-axiom decl (get-event (second decl)) srccomp plgcomp))
      ;; type axioms
      (let ((event (get-event (second decl))))
	(when (and (ufunction-p event)
		   (ufunction-type event)
		   (not (univ-type-p (ufunction-type event))))
	  (dump-type-axiom event srccomp plgcomp)))
      (close-paren srccomp)))
    (close-paren srccomp)))

;;; Syntax of load extension:
;;;   (DECL (theory-extension*) (additional-axioms*)) or
;;;   ((LOAD unit) (load-extension*))

(defun process-load-extension (group srccomp)
  (let* ((event (group-event group))
         (decl (get-event-property event 'zk-event)))
    (open-paren srccomp)
    (dump-decl decl srccomp)
    (cond
     ((eq (car decl) 'load)
      (open-paren srccomp)
      (loop for g in (cdar group)
	    do (process-load-extension g srccomp))
      (close-paren srccomp))
     (t (let ((proof-obligations nil))
	  (open-paren srccomp)
	  (when (eq (car decl) 'function)
	    (setq proof-obligations (generate-proof-obligations decl))
	    (loop
	     for (name access raw-obligation log simple-obligation)
	     in proof-obligations
	     do
	     (dump-decl
	      (zk-format-event
	       (make-axiom
		:name (intern (format nil "~A.PO" name) *zk-package*)
		:kind 'axiom
		:args nil
		:formula (closed-form simple-obligation)))
	      srccomp)))
	  ;; simplified pos for axioms
	  (when (or (eq (car decl) 'axiom)
		    (eq (car decl) 'rule)
		    (eq (car decl) 'frule)
		    (eq (car decl) 'grule))
	    (let ((event (get-event (second decl))))
	      (unless (equal (zk-internal-variables (fourth decl))
			     (event-formula event))
		(dump-decl (zk-format-event
			    (make-axiom
			     :name (intern
				    (format nil "~A.PO" (second decl))
				    *zk-package*)
			     :kind 'axiom
			     :args nil
			     :formula (closed-form (event-formula event))))
			   srccomp))))
	  ;; internal axioms
	  (cond
	   ((member-eq (car decl) *decls-with-internal-axioms*)
	    (dump-internal-axiom-aux decl event srccomp)))
	  ;; definition axioms
	  ;; implicit definition axiom
	  (dump-definition-axiom decl event srccomp)
	  ;; explicit definition axiom
	  (loop for event in (cdr group)
		do (process-theory-extension event srccomp))
	  ;; add derived type axiom here
	  (cond ((and (ufunction-p event)
		      (ufunction-type event)
		      (not (univ-type-p (ufunction-type event))))
		 (dump-type-axiom-aux event srccomp)))
	  (close-paren srccomp))))
    (close-paren srccomp)))

;;; Syntax of theory extension: (DECL [internal-axiom])

(defun process-theory-extension (event srccomp)
  (let ((decl (get-event-property event 'zk-event)))
    (unless (null decl)
      (dump-decl decl srccomp)
      (when (member-eq (car decl) *decls-with-internal-axioms*)
        (dump-internal-axiom-aux decl event srccomp))
      (when (and (ufunction-p event)
		 (ufunction-type event)
		 (not (univ-type-p (ufunction-type event))))
        (dump-type-axiom-aux event srccomp)))))

(defun dump-internal-axiom-aux (decl event srccomp)
  (let ((axiom
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
               ((frule-p event)
                (make-frule-internal-axiom event))
               ((grule-p event)
                (make-grule-internal-axiom event)))))
    (dump-decl
     (zk-format-event
      (make-axiom :name (intern (format nil "~A.INTERNAL" (second decl))
				*zk-package*)
		  :kind 'axiom
		  :args nil
		  :formula (closed-form axiom)))
     srccomp)))

(defun dump-internal-axiom (decl event srccomp plgcomp)
  (dump-internal-axiom-aux decl event srccomp)
  (let ((name (intern (format nil "~A.INTERNAL" (second decl)) *zk-package*)))
    (dump-proof-log-details
     (list 'marker nil (list name 'proof))
     (append '((if-equal ()) (look-up-true (2)))
	     (append-conversion-log
	      (event-internal-details event)
	      `((use-axiom (1) ,(second decl))
		(if-true () (true) t))
	      '(1)))
     plgcomp)))

(defun dump-definition-axiom (decl event srccomp)
  (unless (or (function-stub-p event) (zf-function-p event))
    (let ((assume-slot (get (event-type event) 'assume)))
      (when assume-slot
	(let ((assumption (second (funcall assume-slot event))))
	  (dump-decl
	   (zk-format-event
	    (make-axiom
	     :name (intern (format nil "~A.DEFINITION" (second decl))
			   *zk-package*)
	     :kind 'axiom
	     :args nil
	     :formula (closed-form assumption)))
	   srccomp))))))

(defun dump-type-axiom-aux (event srccomp)
  (let ((name (ufunction-name event)))
    (dump-decl
     (zk-format-event
      (make-axiom :name
		  (intern (format nil "~A.TYPE-OF-AXIOM" name) *zk-package*)
		  :kind 'axiom
		  :args nil
		  :formula
		  (closed-form
		   `(= (type-of ,(cons name (ufunction-args event)))
		       ,(ufunction-type event)))))
     srccomp)))

(defun dump-type-axiom (event srccomp plgcomp)
  (dump-type-axiom-aux event srccomp)
  (let ((name (intern (format nil "~A.TYPE-OF-AXIOM" (event-name event))
		      *zk-package*)))
    (dump-proof-log-details
     (list 'marker nil (list name 'proof))
     (and *record-proof-logs-flag*
	  (let ((*proof-log* nil))
	    (log-type-prescription event) *proof-log*))
     plgcomp)))

(defun dump-decl (decl comp)
  (with-zk-printer
   (with-zk-formatting
    (let ((str (with-output-to-string
		 (*standard-output*)
		 (printer `((:command ,decl))))))
      (salza2:compress-octet-vector
       (flexi-streams:string-to-octets str)
       comp)))))

(defun dump-proof-log-event (event comp)
  (dump-proof-log-details
   (list 'marker nil (list (event-name event) 'rawpo-to-po))
   (event-details event)
   comp)
  (unless (null (event-proof event))
    (let ((str (with-output-to-string
		 (*standard-output*)
		 (format t "~%(")
		 (let ((poname (intern (format nil "~A.PO" (event-name event))
				       *zk-package*)))
		   (dump-proof-log-entry
		    (list 'marker nil (list poname 'proof))))
		 (loop for display in (reverse (event-proof event))
		       do (dump-proof-log-details-aux
			   (display-details display)))
		 (format t ")"))))
      (salza2:compress-octet-vector
       (flexi-streams:string-to-octets str)
       comp))))

(defun dump-proof-log-details (marker details comp)
  (let ((str (with-output-to-string
	       (*standard-output*)
	       (format t "~%(")
	       (dump-proof-log-entry marker)
	       (dump-proof-log-details-aux details)
	       (format t ")"))))
    (salza2:compress-octet-vector
     (flexi-streams:string-to-octets str)
     comp)))

(defun dump-proof-log-details-aux (details)
  (dolist (entry (reverse details))
    (unless (eq (car entry) 'marker)
      (dump-proof-log-entry entry))))

(defun dump-proof-log-entry (entry)
  (format t "~%(")
  (format t "~A" (car entry))
  (let ((index (reverse (second entry))))
    (cond ((null index) (format t " ()"))
	  (t (format t " (~D" (car index))
	     (loop for i in (cdr index)
		   do (format t " ~D" i))
	     (format t ")"))))
  (dolist (expr (cddr entry))
    (format t " ")
    (dump-proof-log-expr expr))
  (format t ")"))

(defun ungenvar-for-log (expr)
   (or (get expr *ungenvar-base-for-log*)
       (let ((str (format nil "~A~A~D" *ungenvar-base-string-for-log*
                          *variable-separator-string*
                          *ungenvar-index-for-log*)))
         (incf *ungenvar-index-for-log*)
         (setf (get expr *ungenvar-base-for-log*) str)
         str)))

(defun dump-proof-log-expr (expr)
  (cond ((all-p expr)
         (format t "(ALL (")
	 (let ((vars (all-vars expr)))
	   (dump-proof-log-expr (car vars))
	   (dolist (e (cdr vars))
	     (format t " ")
	     (dump-proof-log-expr e)))
         (format t ") ")
         (dump-proof-log-expr (all-expr expr))
         (format t ")"))
        ((some-p expr)
         (format t "(SOME (")
	 (let ((vars (some-vars expr)))
	   (dump-proof-log-expr (car vars))
	   (dolist (e (cdr vars))
	     (format t " ")
	     (dump-proof-log-expr e)))
         (format t ") ")
         (dump-proof-log-expr (some-expr expr))
         (format t ")"))
        ((listp expr)
         (format t "(")
	 (dump-proof-log-expr (car expr))
         (dolist (e (cdr expr))
	   (format t " ")
	   (dump-proof-log-expr e))
         (format t ")"))
        ((symbolp expr)
         (cond ((get-rename expr)
                (cond ((genvarp expr)
                       (format t "~A" (ungenvar-for-log expr)))
                      (t (format t "~A" (substring (string expr) 1)))))
               (t (format t "~A" expr))))
        ((integerp expr) (format t "~D" expr))))

(defun open-paren (comp)
  (let ((str (with-output-to-string
	       (*standard-output*)
	       (format t "~%;; >> Level ~A~%(" *paren-level*))))
    (salza2:compress-octet-vector
     (flexi-streams:string-to-octets str)
     comp))
  (incf *paren-level*))

(defun close-paren (comp)
  (decf *paren-level*)
  (let ((str (with-output-to-string
	       (*standard-output*)
	       (format t "~%;; << Level ~A~%)" *paren-level*))))
    (salza2:compress-octet-vector
     (flexi-streams:string-to-octets str)
     comp)))
