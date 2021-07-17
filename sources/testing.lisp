
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

(export 'run-all-tests)

;;; ==================== Regression Testing ====================


;;; Running a test on a ZK source file (a file with ZK declarations and
;;; commands) consists of reading the file, processing the declarations
;;; and commands, and comparing the results with results saved from a
;;; previous test run. Saved results are stored in gzip-compressed test
;;; files since they can become large.

;;; -----
;;; Top level functions:

;;; make-test-file (filename)
;;; save a test run

;;; run-test-file (filename &optional error-stream check-proof-p)
;;; compare result of test run with previously saved test run

;;; run-all-tests-directory (directory &optional make-all-tests-p check-proof-p)
;;; run save/compare on all ZK source files in directory

;;; run-all-tests (&optional make-all-tests-p check-proof-p)
;;; run save/compare on all ZK source files in all test directories

;;; -----

;;; Files and types used by the testing package.

;;; Filename for the log file for the run-all-tests command.
;;; A summary is written here in the directory being tested.
(defparameter *run-all-tests-file* "run-all-tests")

;;; Each possible test file type has a corresponding loader.
(defvar *test-file-loaders* `(("ver" . zk-loader)))

;;; List of all test directories.
(defvar *test-file-directories*	(list *zk-examples-files*))

;;; -----

;;; Echo printing.

;;; Print event names to standard-output and copy to non-nil stream.
(defun echo-print-event-names (stream arg)
  (with-echo-printing
   stream
   (printer `((:event-name-list ,arg)))))

;;; Sorted list of all the files in the given test-directory.
(defun files-in-test-directory (test-directory)
  (let ((pathname (merge-pathnames test-directory)))
    (sort (directory (make-pathname :name :wild
			      :type (pathname-type pathname)
			      :defaults pathname))
	  #'(lambda (x y) (string-lessp (pathname-name x) (pathname-name y))))))

;;; Functions for creating test files.

;;; Get the print, proven and proof properties of the specified event.
;;; The proof properties will be without any proof logs.
;;; The car of the returned result is the name of the event while the
;;; cdr has the form of a property list for the three properties.
(defun get-event-properties (event)
  `(,(event-name event)
    print ,(funcall (get (event-type event) 'print) event)
    proven ,(event-proven event)
    proof ,(mapcar #'freeze-display-without-details (event-proof event))))

;;; Return an alist which captures each user event in the database.
;;; This alist is produced simply by mapping get-event-properties
;;; over user events.
(defun get-alist-database ()
  (update-proof-status)
  (mapcar #'get-event-properties (group-user-history)))	;flattened

;;; Load a file, sending output to a corresponding file of type logtype.
;;; The returned result is the time in seconds it took to perform the load.
(defun make-log-file (pathname logtype)
  (let ((loader (assoc-equal (string-downcase (pathname-type pathname))
			     *test-file-loaders*))
	(file (make-pathname :type logtype
			     :version :newest
			     :defaults pathname)))
    (when (null loader)				;just in case
      (error "No loader is supplied for the file type: ~A"
	      (string-downcase (pathname-type pathname))))
    (with-open-file (stream file :direction :output :if-exists :supersede)
      (unless stream
	(file-error "create" file)
	(return-from make-log-file nil))
      (reset)					;clear anything
      (let ((*standard-output* stream)
            (start-time (get-internal-run-time)))
	(funcall (cdr loader) pathname)
	(/ (- (get-internal-run-time) start-time)
	   (float internal-time-units-per-second))))))

(defcmd make-test-file (filename)
  ((:string "Creates log and test files corresponding to")
   (:command-argument filename)
   (:punctuation ".")
   (:string "The source file is loaded by the appropriate
loader with the log written to")
   (:command-argument filename)
   (:string "with the .log extension and the test information
written, compressed in gzip format, to")
   (:command-argument filename)
   (:string "
with the .test extension.  The two returned results represent the
run time in seconds and a list of all user events in")
   (:command-argument filename)
   (:punctuation ".")
   (:string "The test file which is created can then be used by either")
   (:command-name run-test-file)
   (:string "or")
   (:command-name run-all-tests)
   (:string "
for testing new versions of the prover."))
  (let* ((pathname (merge-pathnames filename))
	 (file (make-pathname :type "test"
			      :version :newest
			      :defaults pathname)))
    (let* ((time (make-log-file pathname "log"))
	   (curr-alist (get-alist-database))
	   (curr-events (mapcar #'car curr-alist)))
      (write-gzipped-file file curr-alist)
      (values time curr-events))))

;;; Functions for comparing test results.

;;; Events which have been added or deleted.
(defun test-different-events (past-events curr-events stream)
  (let ((added (set-difference-equal curr-events past-events))
	(deleted (set-difference-equal past-events curr-events)))
    (unless (null added)
      (with-echo-printing
       stream
       (printer '((:string "Events which have been added:"))))
      (echo-print-event-names stream added))
    (unless (null deleted)
      (with-echo-printing
       stream
       (printer '((:string "Events which have been deleted:"))))
      (echo-print-event-names stream deleted))
    (append added deleted)))

;;; Events whose printed form has been changed.
(defun test-changed-events (events past-alist curr-alist stream)
  (let ((changed
	 (remove-if
	  #'(lambda (u)
	      (equal (getf (cdr (assoc-eq u past-alist)) 'print)
		     (getf (cdr (assoc-eq u curr-alist)) 'print)))
	  events)))
    (unless (null changed)
      (with-echo-printing
       stream
       (printer '((:string "Events which are defined differently:"))))
      (echo-print-event-names stream changed))
    changed))

;;; Events whose proven status is different from before.
(defun test-proven-events (events past-alist curr-alist stream)
  (let* ((past-proven
	  (remove-if-not
	   #'(lambda (u) (getf (cdr (assoc-eq u past-alist)) 'proven)) events))
	 (curr-proven
	  (remove-if-not
	   #'(lambda (u) (getf (cdr (assoc-eq u curr-alist)) 'proven)) events))
	 (proven (set-difference-equal curr-proven past-proven))
	 (unproven (set-difference-equal past-proven curr-proven)))
    (unless (null proven)
      (with-echo-printing
       stream
       (printer
	'((:string "Events which are now proven and previously weren't:"))))
      (echo-print-event-names stream proven))
    (unless (null unproven)
      (with-echo-printing
       stream
       (printer
	'((:string "Events which are now unproven and previously were:"))))
      (echo-print-event-names stream unproven))
    (append proven unproven)))

;;; Events whose proof details have changed since before.
(defun test-differing-proofs (events past-alist curr-alist stream)
  (let ((differences
	 (remove-if
	  #'(lambda (u)
	      (equal (getf (cdr (assoc-eq u past-alist)) 'proof)
		     (getf (cdr (assoc-eq u curr-alist)) 'proof)))
	  events)))
    (unless (null differences)
      (with-echo-printing
       stream
       (printer	'((:string "Events whose proof is now different:"))))
      (echo-print-event-names stream differences))
    differences))

;;; Run test on the specified source file.
(defcmd run-test-file (filename &optional error-stream check-proofs-p)
  ((:string "Runs the tests associated with the")
   (:command-argument filename)
   (:string "given.  It is assumed that the test file has already
been created by")
   (:command-name make-test-file)
   (:punctuation ".")
   (:string "
The tests are run with all differences being reported.  A new log
file is also created.  If")
   (:command-argument error-stream)
   (:string "is provided then all errors are copied there."))
  (let* ((past-alist nil)
	 (pathname (merge-pathnames filename))
	 (file (make-pathname :type "test"
			      :version :newest
			      :defaults pathname)))
    (setq past-alist (ignore-errors (read-gzipped-file file)))
    (when (null past-alist)
      (file-error "open" file)
      (return-from run-test-file nil))
    (when check-proofs-p
      (log-on))
    (let ((time (make-log-file pathname "out")))
      (when check-proofs-p
	(with-echo-printing
	 error-stream
	 (check-all-proofs))
	(log-off))
      (let* ((curr-alist (get-alist-database))
	     (past-events (mapcar #'car past-alist))
	     (curr-events (mapcar #'car curr-alist))
	     (events (intersection-eq past-events curr-events)))
	(values time
		(append (test-different-events
			 past-events curr-events error-stream)
			(test-changed-events
			 events past-alist curr-alist error-stream)
			(test-proven-events
			 events past-alist curr-alist error-stream)
			(test-differing-proofs
			 events past-alist curr-alist error-stream)))))))

;;; Run tests on the specified directory. All source files in the
;;; directory are tested. A summary of results is written to the file
;;; run-all-tests.text. If make-all-tests-p is set to be non-nil then
;;; new test files are created. If check-proofs-p is non-nil,
;;; then proof logging is turned on while running the tests and
;;; the proofs are checked.
(defcmd run-all-tests-directory (directory &optional make-all-tests-p
					   check-proofs-p)
  ((:string "Runs all the tests within the given")
   (:command-argument directory)
   (:punctuation ".")
   (:string "For any tests which do not yet have a test file,")
   (:command-name make-test-file)
   (:string "is called.  Otherwise,")
   (:command-name run-test-file)
   (:string "is called on the tests and either the errors are 
reported or the test gets an OK.  A run-all-tests.text file, which gives the
timings, date, machine, and user information, is also created.  If")
   (:command-argument make-all-tests-p)
   (:string "is non-nil then all of the test files are simply recreated."))
  (let ((logfile (make-pathname :name *run-all-tests-file*
				:type (if make-all-tests-p
					  "log"
					"out")
				:version :newest
				:defaults directory)))
    (with-open-file (stream logfile :direction :output :if-exists :supersede)
      (unless stream
	(file-error "create" logfile)
	(return-from run-all-tests-directory nil))
      (format stream "~%Run-all-tests @ ~A~%~A~%"
	      (machine-instance) (get-decoded-date))
      (loop with total-time = 0
	    with (time events errors)
	    for file in (files-in-test-directory (merge-pathnames directory))
	    do (clear-stats)
	    (with-echo-printing
	     stream
	     (printer `((:string "Testing")
			(:string ,(pathname-name file))
			(:string "..."))))
	    if (or make-all-tests-p	;new tests regardless?
		   (null (probe-file
			  (make-pathname :name (pathname-name file)
					 :type "test"
					 :version :newest
					 :defaults directory))))
	    do
	    (unless make-all-tests-p
	      (with-echo-printing
	       stream
	       (printer '((:space) (:string "no test file ...")) nil)))
	    (multiple-value-setq (time events) (make-test-file file))
	    (unless (null events)
	      (with-echo-printing
	       stream (printer '((:space) (:string "created")) nil)))
	    else do (multiple-value-setq
			(time errors)
		      (run-test-file file stream check-proofs-p))
	    (when (null errors)
	      (with-echo-printing
	       stream
	       (printer '((:space) (:string "ok")) nil)))
	    do (print-stats stream)
	    (incf total-time time)
	    (format stream "~%~%")
	    (let ((*standard-output* stream)) (room))
	    (format stream "~%Time taken in seconds: ~A" time)
	    (force-output stream)
	    finally (format stream "~%Total time taken in seconds: ~A"
			    total-time)))))

;;; The top level function for running tests on all directories in
;;; *test-file-directories*.
(defcmd run-all-tests (&optional make-all-tests-p check-proofs-p)
  ((:string "Runs all the tests within the current test directories.  For
any tests which do not yet have a test file,")
   (:command-name make-test-file)
   (:string "is called.  Otherwise,")
   (:command-name run-test-file)
   (:string "is called on the tests and
either the errors are reported or the test gets an OK.  A
run-all-tests.out file, which gives the timings, date, machine,
and user information, is also created.  If")
   (:command-argument make-all-tests-p)
   (:string "is
non-nil then all of the test files are simply recreated.  This is
useful after changes to the output routines. If")
   (:command-argument check-proofs-p)
   (:string "is true then proof logging is turned on and the proof
logs are checked.  This only applies when not creating test files."))
  (let ((*package* *zk-package*))
    (set-library *zk-library-directory*)
    (loop for directory in *test-file-directories*
	  do (run-all-tests-directory
	      directory make-all-tests-p check-proofs-p))))
