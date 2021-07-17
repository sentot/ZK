
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

;;;
;;; Proof Logging
;;;


;;; Each log entry consists of an inference name, followed by an index
;;; to the subexpression on which the inference applies, optionally
;;; followed by other arguments. The last optional argument, when T,
;;; means the inference rule is to be applied in reverse.

;;; List of the valid inference rules (except MARKER which is not
;;; really an inference rule).
(eval-when (:compile-toplevel :load-toplevel)
(defparameter *inference-rules*
  '(

    if-true
    ;; (if (true) a b) <=> a

    if-false
    ;; (if (false) L R) <=> R

    if-test
    ;; (if test L R) <=> (if (= test (true)) L R)

    if-equal
    ;; (if a b b) => b

    case-analysis ; n
    ;; with n = 2:
    ;; (f x (if a b c) y) <=> (if a (f x b y) (f x c y))

    look-up ; result
    ;; expr => result
    ;;  [(= expr result) or (= result expr) assumed in context]

    use-axiom ; event-name
    ;; e.g. (use-axiom index foo)
    ;; (true)  <=> (all z (q z))
    ;; [the axiom of foo is (all z (q z))]

    is-boolean
    ;; x <=> (if x (true) (false))
    ;; where x is boolean.
    ;; x is considered a boolean if it is either a quantification,
    ;; an application of one the following:
    ;; true, false, not, and, or, implies, =, >=,
    ;; <=, >, <, m<, in, subset,
    ;; or x is of the form (if T L R) where L and R are boolean.

    flip-universals
    ;; (all (x ..) (all (y ..) (p x y))) <=> (all (y ..) (all (x ..) (p x y)))

    rename-universal ; old-var new-var
    ;; (all (old-var) expr1) <=> (all (new-var) expr2)
    ;; [expr2 is expr1 with new-var substituting old-var]

    instantiate-universal; instantiation
    ;; e.g. (instantiate (= x 2))
    ;; (all (x) (p x)) <=> (if (p 2) (all (x) (p x)) (false))

    remove-universal
    ;; (all (x) b) <=> (if b (true) (false))
    ;; [x not occurs free in b]

    all-case-analysis
    ;; (all vars (if a b (false))) <=> (if (all vars a) (all vars b) (false))
    ;; where vars is a list of variables (v1 v2 ...)

    induct ; m1
    ;; (all (m) (P m)) <=>
    ;;   (all (m) (implies (all (m1) (implies (m< m1 m) (P m1)))
    ;;                     (P m)))

    compute
    ;; expr <=> compute(expr)
    ;; where expr must be one of
    ;; (+ int1 int2)
    ;; (- int1 int1)
    ;; (* int1 int2)
    ;; (negate int1)
    ;; (div int1 nonzeroint)
    ;; (mod int1 nonzeroint)
    ;; (rem int1 nonzeroint)
    ;; (ord int1)
    ;; (type-of int1)
    ;; (type-of (true))
    ;; (type-of (false))
    ;; (>= int1 int2)
    ;; (= int1 int2)
    ;; (= bool1 bool2)
    ;; (= exp exp)
    ;; int1 and int2 are integer literals
    ;; nonzeroint is a nonzero integer literal
    ;; bool1 and bool2 are boolean literals (true) or (false)
    ;; expr needs to be specified when doing the inverse

    syntax
    ;; (and) <=> (and (true) (true))
    ;; (and x) <=> (and x (true))
    ;; (and x y) <=> (if x (if y (true) (false)) (false))
    ;; (and x y z ...)  <=>  (and x (and y z ...))
    ;; (or) <=> (or (false) (false))
    ;; (or x) <=> (or x (false))
    ;; (or x y) <=> (if x (true) (if y (true) (false)))
    ;; (or x y z ...)  <=>  (or x (or y z ...))
    ;; (implies x y) <=> (if x (if y (true) (false)) (true))
    ;; (not x) <=> (if x (false) (true))
    ;; (*) <=> (* 1 1)
    ;; (* x) <=> (* x 1)
    ;; (* x y z ...)  <=>  (* x (* y z ...))
    ;; (+) <=> (+ 0 0)
    ;; (+ x) <=> (+ x 1)
    ;; (+ x y z ...)  <=>  (+ x (+ y z ...))
    ;; (make-set)  <=>  (nullset)
    ;; (make-set a)  <=>  (setadd a (nullset))
    ;; (make-set a b  ... )  <=>  (setadd a (setadd b ... ))
    ;; (some (...) P)  <=> (not (all (...) (not P)))
    ;; (all (x y ...) P)  <=>  (all (x) (all (y ...) P))

    marker
    ;; Not really an inference rule

    )))

;;; macros for dealing with indices

(defmacro if-test-index () `(cons 1 index))
(defmacro if-left-index () `(cons 2 index))
(defmacro if-right-index () `(cons 3 index))

(defmacro all-expr-index () `(cons 2 index))
(defmacro some-expr-index () `(cons 2 index))

(defmacro implies-left-index () `(cons 1 index))
(defmacro implies-right-index () `(cons 2 index))

(defmacro and-left-index () `(cons 1 index))
(defmacro and-right-index () `(cons 2 index))

(defmacro or-left-index () `(cons 1 index))
(defmacro or-right-index () `(cons 2 index))

(defmacro not-expr-index () `(cons 1 index))

(defmacro =-left-index () `(cons 1 index))
(defmacro =-right-index () `(cons 2 index))

(defun repeat-all-expr-index (n index)
  (if (zerop n)
      index
      (repeat-all-expr-index (- n 1) (all-expr-index))))

;;; turn proof logging on(t) or off(nill)
;;; don't know if it should be t or nil by default
(defvar *record-proof-logs-flag* nil)

(defun logon ()
  ;; (declare '(special *reduce-caches-all-results-flag*))
  ;; (setq *reduce-caches-all-results-flag* nil)
  (setq *record-proof-logs-flag* t))

(defun logoff ()
  ;; (declare '(special *reduce-caches-all-results-flag*))
  ;; (setq *reduce-caches-all-results-flag* t)
  (setq *record-proof-logs-flag* nil))

(defcmd log-on ()
  ((:string "This command enables proof logging.  It can be used
at any time to begin recording proof logs.  (Recording a log for
part of a proof is not very useful.)  Initially, proof logging is
disabled."))
  (logon))

(defcmd log-off ()
  ((:string "This command disables proof logging.  It can be used
at any time to end recording proof logs.  (Recording a log for
part of a proof is not very useful.)  Initially, proof logging is
disabled."))
  (logoff))

;;; A structure and macros for the proof log.
;;; The proof log is saved before subgoaling and restored after failure.
;;; That way anything performed in irrelevent subgoals can be deleted.

;;; The current proof log.
(defvar *proof-log* nil)

;;; Get current state of *proof-log*. If we have a mutable structure
;;; for proof logs in the future, then need to make a copy.
(defsubst save-proof-log ()
  *proof-log*)

;;; Restore a previously saved proof log
(defsubst restore-proof-log (proof-log)
  (setq *proof-log* proof-log))



;;; Push an entry to the proof log. Ensure that the inference exists.
(defmacro push-proof-log (infer index &rest parms)
  (when (and (consp infer)
             (eq (car infer) 'quote)
             (consp (cdr infer))
             (symbolp (cadr infer))
             (not (member-eq (cadr infer) *inference-rules*)))
    (error "The inference ~A is not an inference rule." infer))
  `(push-proof-log-aux ,infer ,index . ,parms))

;;; Push an inference entry into the current proof log.
(defun push-proof-log-aux (infer index &rest parms)
  (when *record-proof-logs-flag*
    (push (cons infer (cons index parms)) *proof-log*)))

(defun print-proof-log-aux (display detail-level &optional indent)
  detail-level
  (printer '((:newline)))
  (printer `((:string ">") (:command ,(format-display display))))
  (loop for detail in (reverse (display-details display))
        do (printer `((:formula ,(cons (car detail)
                                       (cons (reverse (cadr detail))
                                             (cddr detail)))))
                    t indent)))

(defcmd print-proof-log (&optional event-name detail-level)
  ((:string "Displays a complete or partial proof log.  If")
   (:command-argument event-name)
   (:string "is supplied,
it prints the proof log associated with")
   (:command-argument event-name)
   (:punctuation ".")
   (:string "Otherwise, it prints the current proof log."))
  (update-proof-status)				;save current proof
  (mapc #'(lambda (u) (print-proof-log-aux u detail-level))
	(if (null event-name)
	    (when *current-display*
	      (reverse (cons *current-display* *display-history*)))
	    (let ((event (when (symbolp event-name)
			       (get-event event-name))))
	      (when event
		(reverse (event-proof event))
		))))
  (printer '((:newline)))
  nil)

;;; print out all of the proof logs, for debugging
(defun map-print-proof-log ()
  (mapc #'(lambda (event)
	    (let ((event-name (event-name event)))
	      (printer `((:string "----")
			 (:event-name ,event-name) (:string "----")))
	      (print-proof-log event-name)))
	(reverse (group-user-history)))
  nil)


(defcmd print-all-log-stats (&optional detail-level)
  ((:string "Print logging statistics (under construction)."))
  (update-proof-status)
  (loop for event in (mapcar #'(lambda (u) (get-event u))
                             (select-proof-events))
        do (print-log-stats-proof (event-proof event) detail-level)))

(defcmd print-log-stats (&optional event-name detail-level)
  ((:string "Print logging statistics (under construction)."))
  (update-proof-status)
  (let ((proof (if (null event-name)
                   (when *current-display*
                     (cons *current-display* *display-history*))
                 (let ((event (when (symbolp event-name)
                                (get-event event-name))))
                   (when event (event-proof event))))))
    (print-log-stats-proof proof detail-level)))

(defun print-log-stats-proof (proof detail-level)
  (or (null proof)
      (let ((total-infer 0)
            (rev-proof (reverse proof)))

        (format t "~%Stats for ~A ..."
                (let ((event (display-event (car rev-proof))))
                  (cond ((null event) "An unnamed formula")
                        (t (event-name event)))))
        (force-output *standard-output*)

        (loop for display in rev-proof
              for command = (car (display-command display))
              for infer = (length (display-details display))
              do (incf total-infer infer)
                 (when detail-level
                       (format t " ~A(~A)" command infer)))

        (format t " ~A" total-infer)
        (force-output *standard-output*))))


;;; Predicates to determine if log entry is a start/end marker

(defun start-marker-p (entry)
  (and (listp entry)
       (eq (first entry) 'marker)
       (eq (second (third entry)) 'start)))

(defun end-marker-p (entry)
  (and (listp entry)
       (eq (first entry) 'marker)
       (eq (second (third entry)) 'end)))

(defun marker-p (entry)
  (and (listp entry) (eq (first entry) 'marker)))


;;; ----- Utility functions for proof logging.

(defun internal-name (name)
  (intern (format nil "~A.~A" name 'internal) *zk-package*))

(defun definition-name (name)
  (intern (format nil "~A.~A" name 'definition) *zk-package*))

;;; Given the argument list, compute the index displacement (assuming
;;; that a formula is universally closed on the arguments).

(defun index-args (args)
  (index-args-aux args nil))

(defun index-args-aux (args index)
  (if (null args)
      index
    (cons 2 (index-args-aux (cdr args) index))))
