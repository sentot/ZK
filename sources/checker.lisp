
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
;;; The Integrated Proof Checker
;;;

;;; *** Note that the indexing in a proof log entry internally is
;;; the reverse of the "official" entry in dumped proof logs.
;;; It is innermost first here (convenient to construct using
;;; cons, but not so convenient for traversal) and outermost first
;;; in an "official" entry (convenient for traversal using car).


;;; The Integrated Proof Checker is a prototype proof checker for ZK.
;;; The intention of the prototype is to demonstrate the correctness
;;; of the proof logs being generated and to demonstrate feasibility
;;; of proof checking generally.

;;; Although the integrated proof checker depends upon significant
;;; portions of ZK, such as parsing and database management, it is
;;; still able to fully check the proof logs.  Thus, it gives an
;;; increased level of assurance in spite of the dependence and its
;;; lack of verification.

;;; The checker consists of two main parts.  The first is the dispatch
;;; routine, the second is a collection of functions for checking
;;; inferences.  Checking proceeds by dispatching on each of the
;;; inferences given in the proof log.  At each step the inference
;;; rule is applied at the index and the formula is updated.  The
;;; check is successful only if every inference and index are defined,
;;; the inference applies at the specified index, and the result
;;; following the checking is the same formula that ZK produced.
;;; (This last condition is checked after every command.)

;;; The interface to integrated proof checker consists of two commands:

;;; (check-proof &optional event-name detail-level) checks a single
;;; proof.  The default is to check the current proof.  If event-name
;;; is supplied (non nil) then the proof log for that event is
;;; checked.  Check-proof succeeds or fails (returning t or nil), and
;;; prints information according to the setting of detail-level.

;;; (check-all-proofs &optional detail-level) checks every proof in the
;;; database.  check-all-proofs succeeds (returning t) if every
;;; proof-check suceeds, otherwise it fails (returning nil).  The
;;; setting of detail-level controls what is printed during checking.

;;; The optional detail-level controls how much is printed by the
;;; checker.  The default value is 1.  The other possible values are:

;;; 0 - nothing is printed,
;;; 1 - the event name and success or failure,
;;; 2 - everything printed by 1 plus the command names,
;;; 3 - everything printed by 2 plus the inference names,
;;; 4 - everything printed by 3 plus the resulting formula.

;;; ___________________________________________________________________________


;;; Failure Codes.

;;; A proof check can fail for several reasons.  If printing is turned
;;; on and a check fails, then a failure code is printed.  The message
;;; takes the form 'code-failed', where 'code' is the failure code.
;;; The code indicates the reason for the failure of the proof check.
;;; All of the failure codes, and there meanings, are listed below.

;;; the inference cited in the log is unknown
(defparameter *infer-code* 'infer)

;;; the index cited in the log doesn't exist
(defparameter *index-code* 'index)

;;; the inference rule indicated that it failed
(defparameter *apply-code* 'apply)

;;; the result of checking a command is different
(defparameter *compare-code* 'compare)


;;; Primitive Functions.

;;; get the inference function associated with symbol
(defmacro get-infer (symbol)
  `(get ,symbol 'infer))

;;; return the default for the detail-level parameter
(defun default-detail-level (detail-level)
  (if (and (integerp detail-level)
           (>= detail-level 0)
           (<= detail-level 4))
      detail-level
    1))                                 ;default is 1

;;; Select and the subexpression specified by index.
;;; The result is a tuple
;;;   (subexpression context bool-p).

(defun select-index (index formula)
  ;; Recall from note above, index is "reversed".
  (select-index-aux (reverse index) formula nil))

(defun select-index-aux (rev-index formula context)
  (cond ((null rev-index) (values formula context))
        ((atom formula) (values nil nil nil))
        ((if-p formula)
         (let ((car-index (car rev-index)))
           (select-index-aux (cdr rev-index)
                             (nth car-index formula)
			     (cond ((= car-index 2)
				    (list* (if-test formula)
					   (make-= (if-test formula) *true*)
					   context))
				   ((= car-index 3)
				    (list* (make-if (if-test formula)
						    *false*
						    *true*)
					   (make-=
					    (make-if (if-test formula)
						     *false*
						     *true*)
					    *true*)
					   context))
				   (t context)))))
	((and (or (all-p formula) (some-p formula))
	      (= (car rev-index) 2))
	 (select-index-aux
	  (cdr rev-index)
	  (nth (car rev-index) formula)
	  ;; remove things from context that have captured free variables
	  (loop for a in context
		unless (intersection-eq
			(all-vars formula)
			(list-of-free-variables-unexpanded a))
		collect a)))
        (t (select-index-aux (cdr rev-index)
                             (nth (car rev-index) formula)
                             context))))

;;; replace the subformula in formula at index with subformula
;;; the result is formula with the replacement, it is destructive
;;; if the index doesn't describe a subformula then nil is returned
(defun replace-index (index formula subformula)
  (cond ((null index) subformula)
        (t (replace-index-aux (reverse index)
                              (copy-list formula)
                              subformula))))

(defun replace-index-aux (rev-index formula subformula)
  (cond ((atom formula)
         (and (null rev-index) subformula))
        ((null (cdr rev-index))
         (setf (nth (car rev-index) formula) subformula)
         formula)
        (t (setf (nth (car rev-index) formula)
                 (replace-index-aux (cdr rev-index)
                                    (copy-list (nth (car rev-index) formula))
                                    subformula))
           formula)))


;;; Commands for Checking.

(defvar *debug-checker* nil)

(defun debug-checker-on () (setq *debug-checker* t))

(defun debug-checker-off () (setq *debug-checker* nil))

(defcmd check-all-proofs (&optional detail-level)
  ((:string "Checks every complete or partial proof in the
database.  By default, it indicates whether the proof check succeeded
or failed for each proof.  The amount of detail printed is controlled by")
   (:command-argument detail-level)
   (:punctuation "."))
  (update-proof-status)                 ;save current proof
  (let ((success t)
        (level (default-detail-level detail-level)))
    ;; proof check events in the user-history
    ;; there is no need to look inside groups
    (loop for event in (mapcar #'(lambda (u) (get-event u))
                               (select-proof-events))
          do (or (check-proof-log (event-proof event) level)
                 (setq success nil)))
    success))

(defcmd check-proof (&optional event-name detail-level)
  ((:string "Checks a complete or partial proof.  If")
   (:command-argument event-name)
   (:string "is supplied, it checks the proof associated with")
   (:command-argument event-name)
   (:punctuation ".")
   (:string "Otherwise, it checks the current proof.  By default,
it indicates whether the proof check succeeded or failed.  The
amount of detail printed is controlled by")
   (:command-argument detail-level)
   (:punctuation "."))
  (update-proof-status)                 ;save current proof
  (let ((level (default-detail-level detail-level))
        (proof (if (null event-name)
                   (when *current-display*
                     (cons *current-display* *display-history*))
                 (let ((event (when (symbolp event-name)
                                (get-event event-name))))
                   (when event (event-proof event))))))
    ;; if the proof is null, then this will succeed
    (check-proof-log proof level)))


;;; Proof Checking Function.

;;; the basic function for checking a proof log
;;; t is returned if and only if the proof check succeeds
;;; detail-level is an integer that specifies extra printing
;;; recall, both proofs and proof logs are stored in reverse order
(defun check-proof-log (proof detail-level)
  (or (null proof)                      ;empty proof
      (let ((*current-display* (car proof))
            (*display-history* (cdr proof)))
        (let* ((code nil)
               (success t)
               (rev-proof (reverse proof))
               ;; the current formula is destructively updated
               (formula
                (cond ((null (display-event *current-display*))
                       (let ((expr
                              (copy-tree (display-formula (car rev-proof)))))
                         (universally-quantify
                          (unique (list-of-free-variables-unexpanded expr))
                          expr)))
                      (t (let* ((expr (copy-tree
                                       (event-rawpo
                                        (display-event *current-display*))))
                                (vars (mapcar #'zk-internal-variables
                                              (unique
                                               (zk-list-of-free-variables
                                                expr)))))
                           (universally-quantify
                            vars
                            (zk-internal-variables expr)))))))
          (when (> detail-level 0)
	    (let ((event (display-event (car rev-proof))))
	      (printer (list '(:string "Checking")
			     (if (null event)
				 '(:string "an unnamed formula")
			       `(:event-name ,(event-name event)))
			     '(:string "...")))))
          (when (> detail-level 1)
	    (printer `((:string
			,(format nil " ~A"
				 (car (display-command (car rev-proof))))))
		     nil))
          (when (> detail-level 3)
	    (printer `((:formula ,formula)) nil))
          (loop for display in rev-proof
              do (multiple-value-setq (formula success code)
                   (check-proof-log-display display formula detail-level))
              until (not success))
          (when (> detail-level 0)
            (if success
		(printer '((:space) (:string "ok")) nil)
	      (printer (list (list :string (format nil " ~A-failed" code)))
		       nil)))
          success))))

;;; check the proof log associated with a display, ie one command
;;; three values are returned, the updated formula, a success
;;; indicator, and an error code giving the reason for failure
(defun check-proof-log-display (display formula detail-level)
  (let ((code nil)
        (success t))
    (when (> detail-level 1)
      (printer `((:command-name ,(car (display-command display)))
		 (:newline))))
    (loop for entry in (reverse (display-details display))
          do (multiple-value-setq (formula success code)
               (check-proof-log-entry entry formula detail-level))
          until (not success))
    (cond ((not success) (values formula nil code))
          ;; check that the inferences give the same result
          ((not (equal (universally-quantify
                        (unique (list-of-free-variables-unexpanded
                                 (display-formula display)))
                        (display-formula display))
                       (select-index (display-base-index display) formula)))
           (when *debug-checker*
             (format t "~%Prover's Result:~%~A~%Checker's Result:~%~A"
                     (universally-quantify
                      (unique (list-of-free-variables-unexpanded
                               (display-formula display)))
                      (display-formula display))
                     (select-index (display-base-index display) formula)))
           (values formula nil *compare-code*))
          (t (values formula t nil)))))


;;; The Dispatching Function.

;;; check a single entry in a proof log, ie exactly one inference
;;; three values are returned, the updated formula, a success
;;; indicator, and an error code giving the reason for failure
(defun check-proof-log-entry (entry formula detail-level)
  (cond
   ((eq (car entry) 'marker)
    (when *debug-checker* (print entry)
    (when (and (> (length entry) 2)
	       (listp (third entry))
	       (eq (car (third entry)) 'checkpoint))
      (format t "~%Presumed subformula:~%~S" (second (third entry)))
      (multiple-value-bind
       (subformula context)
       (select-index (cadr entry) formula)
       (if (equal (second (third entry)) subformula)
	   (format t "~%same as")
	 (format t "~%different from"))
       (format t "~%Actual subformula:~%~S~%" subformula))))
    (values formula t nil))
   (t (let* ((infer (car entry))
             (index (cadr entry))
             (args (cddr entry))
             (inference (and (symbolp infer) (get-infer infer))))
        (multiple-value-bind (subformula context)
          (select-index index formula)
          (when (> detail-level 2)
            (format t " ~A" infer))
          (cond ((null inference)
                 (values formula nil *infer-code*)) ;no such inference
                ((null subformula)
                 (when *debug-checker*
                   (format t "~%Index Failure for:~A" entry))
                 (values formula nil *index-code*)) ;index not in formula
                (t
                 (let ((result
                        (apply inference subformula context args)))
                   (cond ((null result)
                          (when *debug-checker*
			    (let ((zoom-formula
				   (select-index (nthcdr 5 index) formula)))
			      (format
			       t "~%Zoomed Formula at Index ~A:"
			       (nthcdr 5 index))
			      (format t "~%~A~%Subform:~%~A~%Inference:~%~A"
			       zoom-formula subformula entry)
			      ))
                          (values formula nil *apply-code*)) ;inference failed
                         ;; success, return the updated formula
                         (t (setq formula
                                  (replace-index index formula result))
                            (when (> detail-level 3)
                              (print formula))
                            (values formula t nil)))))))))))


;;; Debugging code

(defun check-proof-log-on-formula (log formula detail)
  (let ((code nil)
	(success t))
    (loop for entry in (reverse log)
	  do (multiple-value-setq
	      (formula success code)
	       (check-proof-log-entry entry formula detail))
	  until (not success))
    (if success (format t "~%Success") (format t "~%Failed"))
    (format t "~%Result ~%~S~%" formula)))

(defmacro check-log-fcn (fcn formula &rest args)
  `(let ((*proof-log* nil))
     (,fcn . ,args)
     (check-proof-log-on-formula *proof-log* ,formula 4)))




;;; The Inference Rules.

;;; Inference rules are functions.  They are stored on the property
;;; list of the symbol that names the inference with indicator infer.
;;; They take a formula argument and return the formula that results
;;; from the application of the inference rule.  If they fail for any
;;; reason, then nil is returned in place of the formula.  A few of
;;; the inference rules require additional arguments.

;;; return a list of the symbols in variable positions in expr
(eval-when (:compile-toplevel :load-toplevel)
(defun list-of-vars (expr)
  (cond ((atom expr)
         (and expr (symbolp expr) (list expr)))
        (t (mapcan #'list-of-vars (cdr expr)))))
)

;;; macro to generate inference rules for simple rewrite inferences
;;; given the left and right sides of the inference and the formula
;;; the condition is a restriction on the bindings in the left side
(defmacro infer-rewrite (left right formula &optional condition)
  (let ((substitutions (gensym))
        (success (gensym))
        (renaming-substitutions
         (mapcar #'(lambda (u)
		     (cons u
			   (intern (string-append "))" (string u))
				   *zk-package*)))
                 (unique (append (list-of-vars left)
                                 (list-of-vars right))))))
    (let ((renamed-left (sublis-eq renaming-substitutions left))
          (renamed-right (sublis-eq renaming-substitutions right))
          (renamed-condition (sublis-eq renaming-substitutions condition)))
      `(multiple-value-bind (,substitutions ,success)
           (match-pattern-formula ',renamed-left ,formula)
         (when (and ,success
                    . ,(and condition
                            `((let ,(mapcar
                                     #'(lambda (x)
                                         `(,x (binding-of ',x ,substitutions)))
                                     (unique (list-of-vars renamed-left)))
                                ,@(unique (list-of-vars renamed-left))
                                ,renamed-condition))))
           (sublis-eq ,substitutions ',renamed-right))))))

;;; The remaining comments are the inference rule descriptions taken
;;; from logging.lisp.  They are being converted into the inference
;;; rule functions, and then they are removed from this file.

(defun equal-except-at-nth (n list1 list2)
  (and (listp list1)
       (listp list2)
       (> n 0)
       (< n (length list1))
       (= (length list1) (length list2))
       (let ((copy-of-list2 (copy-list list2)))
	 (setf (nth n copy-of-list2) (nth n list1))
	 (equal list1 copy-of-list2))))

(defun all-ifs-with-equal-test (list)
  (and (consp list)
       (every #'if-p list)
       (let ((test (if-test (car list))))
	 (every #'(lambda (u) (equal (if-test u) test)) (cdr list)))))

;;; with n = 2:
;;; (f x (if a b c) y) <=> (if a (f x b y) (f x c y))
;;; with n = 0:
;;; (f (if a x y) (if a b c) (if a c d)) <=> (if a (f x b x) (f y c d))

(defpropfun (case-analysis infer) (formula context n &optional inverse)
  context
  (cond
   ((null inverse)
    (when (and (consp formula) (integerp n) (>= n 0) (< n (length formula)))
      (cond
       ((= n 0)
	(when (all-ifs-with-equal-test (cdr formula))
	  (make-if (if-test (second formula))
		   (cons (first formula) (mapcar #'third (cdr formula)))
		   (cons (first formula) (mapcar #'fourth (cdr formula))))))
       (t (let ((subformula (nth n formula)))
	    (when (if-p subformula)
	      (let ((left-update (copy-list formula))
		    (right-update (copy-list formula)))
		(setf (nth n left-update) (if-left subformula)
		      (nth n right-update) (if-right subformula))
		(make-if (if-test subformula) left-update right-update))))))))
   ((if-p formula)
    (let ((left (if-left formula))
	  (right (if-right formula)))
      (when (and (consp left) (integerp n) (>= n 0) (< n (length left)))
	(cond
	 ((= n 0)
	  (when (and (consp (if-left formula))
		     (consp (if-right formula))
		     (eq (car (if-left formula)) (car (if-right formula))))
	    (cons (car (if-left formula))
		  (mapcar #'(lambda (u v) (make-if (if-test formula) u v))
			  (cdr (if-left formula))
			  (cdr (if-right formula))))))
	 ((equal-except-at-nth n left right)
	  (let ((result (copy-list left)))
	    (setf (nth n result)
		  (make-if (if-test formula) (nth n left) (nth n right)))
	    result))))))))

(defpropfun (if-true infer) (formula context &optional right inverse)
  context
  (cond ((null inverse) (infer-rewrite (if (true) a b)	a formula))
	(t (make-if *true* formula right))))

;;; (if (false) L R)  <=>  R

(defpropfun (if-false infer) (formula context &optional left inverse)
  context
  (cond ((null inverse) (infer-rewrite (if (false) a b) b formula))
	(t (make-if *false* left formula))))

(defpropfun (if-equal infer) (formula context &optional test inverse)
  context
  (cond ((null inverse)
	 (infer-rewrite (if a b b) b formula))
	(t (make-if test formula formula))))

(defpropfun (remove-universal infer) (formula context &optional vars inverse)
  context
  (cond ((and (null inverse)
	      (all-p formula)
	      (null (intersection-eq
		     (all-vars formula)
		     (list-of-free-variables-unexpanded (all-expr formula)))))
	 (make-if (all-expr formula) *true* *false*))
	((and inverse
	      (if-p formula)
	      (true-p (if-left formula))
	      (false-p (if-right formula))
	      (null (intersection-eq
		     vars
		     (list-of-free-variables-unexpanded (if-test formula)))))
	 (make-all vars (if-test formula)))))

(defpropfun (use-axiom infer) (formula context event-name &optional inverse)
  context
  (let ((axiom (get-axiom event-name)))
    (cond ((null inverse)
	   (when (and axiom (true-p formula)) axiom))
	  ((equal axiom formula)
	   *true*))))

(defpropfun (flip-universals infer) (formula context)
  context
  (infer-rewrite (all x (all y p)) (all y (all x p)) formula))

(defpropfun (instantiate-universal infer)
  (formula context instantiation &optional inverse)
  context
  (cond ((null inverse)
	 (let ((instantiated
		(instantiate-universal-infer formula instantiation)))
	   (when instantiated
	     (make-if instantiated formula *false*))))
	((and (if-p formula)
	      (all-p (if-left formula))
	      (false-p (if-right formula))
	      (equal (if-test formula)
		     (instantiate-universal-infer (if-left formula)
						  instantiation)))
	 (if-left formula))))

(defun instantiate-universal-infer (formula instantiation)
  (cond ((and (all-p formula)
              (eq (all-var formula) (=-left instantiation)))
         (substitute-free-var (all-var formula)
                              (=-right instantiation)
                              (all-expr formula)))
        (t nil)))

(defpropfun (rename-universal infer) (formula context old-var new-var)
  context
  (when (and (all-p formula)
             (symbolp new-var)          ;**** a variable?
             (not (occurs-in new-var formula))
             (eq (all-var formula) old-var))
    (make-all-single
      new-var (substitute-free-var old-var new-var (all-expr formula)))))

(defun substitute-free-var (var replacement formula)
  (cond ((eq var formula) replacement)
        ((or (atom formula)
             (and (all-p formula)
		  (member-eq var (all-vars formula)))
             (and (some-p formula)
		  (member-eq var (some-vars formula))))
         formula)
        (t (mapcar #'(lambda (u) (substitute-free-var var replacement u))
                   formula))))

(defun substitute-expression (old new formula)
  (substitute-expression-aux
   old new formula (unique (list-of-free-variables old))))

(defun substitute-expression-aux (old new formula free-vars)
  (cond ((equal old formula) new)
        ((atom formula) formula)
        ((and (all-p formula) (member-eq (all-var formula) free-vars))
         formula)
        ((and (some-p formula) (member-eq (some-var formula) free-vars))
         formula)
        (t (mapcar #'(lambda (u)
                       (substitute-expression-aux old new u free-vars))
                   formula))))

;;; Inference for strong induction.
;;; m1 specifies the name of the variable quantified in the
;;; induction hypothesis.

(defpropfun (induct infer) (formula context m1)
  context
  (make-all-single (all-var formula)
            (make-implies
             (make-all-single
               m1
               (make-implies `(m< ,m1 ,(all-var formula))
                             (subst-eq m1
                                       (all-var formula)
                                       (all-expr formula))))
             (all-expr formula))))

(defun compute-infer (formula)
  (cond ((+-p formula)
	 (and (integerp (second formula))
	      (integerp (third formula))
	      (+ (second formula) (third formula))))
	((--p formula)
	 (and (integerp (second formula))
	      (integerp (third formula))
	      (- (second formula) (third formula))))
        ((negate-p formula)
	 (and (integerp (second formula))
	      (- (second formula))))
        ((*-p formula)
	 (and (integerp (second formula))
	      (integerp (third formula))
	      (* (second formula) (third formula))))
        ((ord-p formula)
	 (and (integerp (second formula))
	      (second formula)))
        ((and (consp formula) (eq (car formula) 'div))
         (truncate (second formula) (third formula)))
        ((and (consp formula) (eq (car formula) 'mod))
         (mod (second formula) (third formula)))
        ((and (consp formula) (eq (car formula) 'rem))
         (rem (second formula) (third formula)))
        ((>=-p formula)
	 (and (integerp (second formula))
	      (integerp (third formula))
	      (if (>= (second formula) (third formula)) *true* *false*)))
        ((type-of-p formula)
         (cond ((int-p (second formula)) '(int))
	       ((bool-p (second formula)) '(bool))))
        ((=-p formula)
	 (cond ((equal (=-left formula) (=-right formula)) *true*)
	       ((and (true-p (=-left formula)) (false-p (=-right formula)))
		*false*)
	       ((and (false-p (=-left formula)) (true-p (=-right formula)))
		*false*)
	       ((and (integerp (=-left formula)) (integerp (=-right formula)))
		*false*)))))

(defpropfun (compute infer) (formula context &optional original inverse)
  context
  (cond ((null inverse) (compute-infer formula))
	((equal (compute-infer original) formula) original)))

(defun expr-is-boolean (expr)
  (or (true-p expr)
      (false-p expr)
      (not-p expr)
      (or-p expr)
      (and-p expr)
      (implies-p expr)
      (=-p expr)
      (>=-p expr)
      (<=-p expr)
      (>-p expr)
      (<-p expr)
      (m<-p expr)
      (in-p expr)
      (zk-subset-p expr)
      (all-p expr)
      (some-p expr)
      (and (if-p expr)
	   (expr-is-boolean (if-left expr))
	   (expr-is-boolean (if-right expr)))))

(defpropfun (is-boolean infer) (formula context &optional inverse)
  context
  (cond ((null inverse)
	 (when (expr-is-boolean formula) (make-if formula *true* *false*)))
	((and (if-p formula)
	      (expr-is-boolean (if-test formula))
	      (true-p (if-left formula))
	      (false-p (if-right formula)))
	 (if-test formula))))

(defpropfun (all-case-analysis infer) (formula context &optional inverse)
  context
  (cond ((and (null inverse)
	      (all-p formula)
	      (if-p (all-expr formula))
	      (false-p (if-right (all-expr formula))))
	 (make-if (make-all (all-vars formula) (if-test (all-expr formula)))
		  (make-all (all-vars formula) (if-left (all-expr formula)))
		  *false*))
	((and inverse
	      (if-p formula)
	      (all-p (if-test formula))
	      (all-p (if-left formula))
	      (false-p (if-right formula))
	      (equal (all-vars (if-test formula))
		     (all-vars (if-left formula))))
	 (make-all (all-vars (if-test formula))
		   (make-if (all-expr (if-test formula))
			    (all-expr (if-left formula))
			    *false*)))))

;;; (if test L R) <=> (if (= test (true)) L R)

(defpropfun (if-test infer) (formula context &optional inverse)
  context
  (cond ((null inverse)
	 (when (if-p formula)
	   (make-if (make-= (if-test formula) *true*)
		    (if-left formula)
		    (if-right formula))))
	((and (if-p formula)
	      (=-p (if-test formula))
	      (true-p (=-right (if-test formula))))
	 (make-if (=-left (if-test formula))
		  (if-left formula)
		  (if-right formula)))))

(defun make-set-from-elements (elements)
  (cond
   ((null elements) '(nullset))
   (t (list 'setadd (car elements) (make-set-from-elements (cdr elements))))))

(defun syntax-expand-single (formula)
  (cond ((and-p formula)
	 (cond ((null (cdr formula)) (make-and *true* *true*))
	       ((null (cddr formula)) (make-and (cadr formula) *true*))
	       ((= (length formula) 3)
		(make-if (second formula)
			 (make-if (third formula) *true* *false*)
			 *false*))
	       ((> (length formula) 3)
		(make-and (cadr formula) (cons 'and (cddr formula))))))
	((or-p formula)
	 (cond ((null (cdr formula)) (make-or *false* *false*))
	       ((null (cddr formula)) (make-or (cadr formula) *false*))
	       ((= (length formula) 3)
		(make-if (second formula)
			 *true*
			 (make-if (third formula) *true* *false*)))
	       ((> (length formula) 3)
		(make-or (cadr formula) (cons 'or (cddr formula))))))
	((implies-p formula)
	 (when (= (length formula) 3)
	   (make-if (second formula)
		    (make-if (third formula) *true* *false*)
		    *true*)))
	((not-p formula) (make-if (second formula) *false* *true*))
	((*-p formula)
	 (cond ((null (cdr formula)) (make-* 1 1))
	       ((null (cddr formula)) (make-* (cadr formula) 1))
	       ((> (length formula) 3)
		(make-* (cadr formula) (cons '* (cddr formula))))))
	((+-p formula)
	 (cond ((null (cdr formula))(make-+ 0 0))
	       ((null (cddr formula))(make-+ (cadr formula) 0))
	       ((> (length formula) 3)
		(make-+ (cadr formula) (cons '+ (cddr formula))))))
	((+-p formula)
	 (cond ((null (cdr formula)) (make-+ 0 0))
	       ((null (cddr formula)) (make-+ (cadr formula) 0))
	       ((> (length formula) 3)
		(make-+ (cadr formula) (cons '+ (cddr formula))))))
	((some-p formula)
	 (make-not
	  (make-all (some-vars formula) (make-not (some-expr formula)))))
	((and (all-p formula) (> (length (all-vars formula)) 1))
	 (make-all-single
	  (car (all-vars formula))
	  (make-all (cdr (all-vars formula)) (all-expr formula))))
	((and (listp formula) (eq (car formula) 'make-set))
	 (make-set-from-elements (cdr formula)))))

(defun make-make-set-from-setadds-aux (formula)
  (cond ((eq (car formula) 'setadd)
	 (cons (cadr formula)
	       (make-make-set-from-setadds-aux (caddr formula))))))

(defun make-make-set-from-setadds (formula)
  (when (is-canonical-setadd formula)
    (cons 'make-set (make-make-set-from-setadds-aux formula))))

(defun is-canonical-setadd (formula)
  (or (equal formula '(nullset))
      (and (listp formula)
	   (eq (car formula) 'setadd)
	   (is-canonical-setadd (caddr formula)))))

(defun syntax-unexpand-single (formula)
  (cond ((and-p formula)
	 (when (= (length formula) 3)
	   (cond ((and (true-p (and-left formula)) (true-p (and-right formula)))
		  '(and))
		 ((true-p (and-right formula))
		  (list 'and (and-left formula)))
		 ((and (and-p (and-right formula))
		       (>= (length (and-right formula)) 3))
		  (list* 'and (and-left formula) (cdr (and-right formula)))))))
	((or-p formula)
	 (when (= (length formula) 3)
	   (cond ((and (false-p (or-left formula)) (false-p (or-right formula)))
		  '(or))
		 ((false-p (or-right formula))
		  (list 'or (or-left formula)))
		 ((and (or-p (or-right formula))
		       (>= (length (or-right formula)) 3))
		  (list* 'or (or-left formula) (cdr (or-right formula)))))))
	((not-p formula)
	 (when (and (all-p (not-expr formula))
		    (not-p (all-expr (not-expr formula))))
	   (make-some (all-vars (not-expr formula))
		      (not-expr (all-expr (not-expr formula))))))
	((*-p formula)
	 (when (= (length formula) 3)
	   (cond ((and (equal (*-left formula) 1) (equal (*-right formula) 1))
		  '(*))
		 ((equal (*-right formula) 1)
		  (list '* (*-left formula)))
		 ((and (*-p (*-right formula))
		       (>= (length (*-right formula)) 3))
		  (list* '* (*-left formula) (cdr (*-right formula)))))))
	((+-p formula)
	 (when (= (length formula) 3)
	   (cond ((and (equal (+-left formula) 0) (equal (*-right formula) 0))
		  '(+))
		 ((equal (+-right formula) 0)
		  (list '+ (+-left formula)))
		 ((and (+-p (+-right formula))
		       (>= (length (+-right formula)) 3))
		  (list* '+ (+-left formula) (cdr (+-right formula)))))))
	((if-p formula)
	 (cond ((and (false-p (if-left formula)) (true-p (if-right formula)))
		(make-not (if-test formula)))
	       ((and (false-p (if-right formula))
		     (if-p (if-left formula))
		     (true-p (if-left (if-left formula)))
		     (false-p (if-right (if-left formula))))
		(make-and (if-test formula) (if-test (if-left formula))))
	       ((and (true-p (if-left formula))
		     (if-p (if-right formula))
		     (true-p (if-left (if-right formula)))
		     (false-p (if-right (if-right formula))))
		(make-or (if-test formula)  (if-test (if-right formula))))
	       ((and (true-p (if-right formula))
		     (if-p (if-left formula))
		     (true-p (if-left (if-left formula)))
		     (false-p (if-right (if-left formula))))
		(make-implies (if-test formula) (if-test (if-left formula))))))
	((all-p formula)
	 (when (all-p (all-expr formula))
	   (make-all (append (all-vars formula) (all-vars (all-expr formula)))
		     (all-expr (all-expr formula)))))
	((equal formula '(nullset)) (list 'make-set))
	((and (listp formula) (eq (car formula) 'setadd))
	 (make-make-set-from-setadds formula))))

(defpropfun (syntax infer) (formula context &optional inverse)
  context
  (cond ((null inverse) (syntax-expand-single formula))
	(t (syntax-unexpand-single formula))))

(defpropfun (look-up infer) (formula context result)
  context
  (when (or (member-equal (make-= formula result) context)
	    (member-equal (make-= result formula) context))
    result))
