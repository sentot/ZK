
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

;;; The CASES facility allows different conjuncts or disjuncts to be
;;; worked on separately.  The system will take care of the management
;;; of the cases, including navigation and determining whether the
;;; entire formula has been satisfied or contradicted.

;;; The commands are CASES, NEXT and DELETE-HYPOTHESES.

;;; The CASES command splits the current formula into conjunctive
;;; or disjunctive cases.  A case can further be split.

;;; The NEXT command moves one to the next case, regardless of whether
;;; the current case is done.  The NEXT command may complete the proof
;;; (or disproof) if all the cases have been satisfied (or contradicted)
;;; or if the current case causes short-circuiting.  On the last case,
;;; and if not all the cases are done and there is no short-circuiting,
;;; the unfinished cases are collected.

;;; The DELETE-HYPOTHESES command produce a disjunction of the current
;;; formula with a subset of the hypotheses deleted and the entire
;;; current formula.  The user can then work on the part with some
;;; of the hypotheses deleted (e.g., irrelevant hypotheses).  If the
;;; proof of that part succeeds then it short circuits the proof of
;;; the disjunction.  Otherwise we still have the original current
;;; formula as a case.



;;; ========== The CASES command.

(defcmd cases (:display)
  ((:string "Try to split the current subformula into individual cases.")
   (:paragraph)
   (:string"If the top level connective of the current formula is an")
   (:event-name and)
   (:punctuation ",")
   (:string "then a conjunctive split is performed producing one case for each
conjunct in the")
   (:event-name and)
   (:punctuation ".")
   (:paragraph)
   (:string "If the top level connective is an")
   (:event-name or)
   (:punctuation ",")
   (:string "then a disjunctive split is performed.")
   (:paragraph)
   (:string "If the top level
connective is an")
   (:event-name if)
   (:punctuation ",")
   (:string "then a conjunctive split is performed producing two cases.
The first case is the")
   (:event-name test)
   (:string "implying the")
   (:event-name then)
   (:string "part; the second case is the negation of the")
   (:event-name test)
   (:string "implying the")
   (:event-name else)
   (:string "part.")
   (:paragraph)
   (:string "If the top level connective is an")
   (:event-name implies)
   (:punctuation ",")
   (:string "then the split is performed on the conclusion, with the
hypothesis of the implication added as a hypothesis of each of the
cases.")
   (:paragraph)
   (:string "If the")
   (:command-name cases)
   (:string "succeeds, then the proof of the first case is begun.
The cases are numbered in reverse order to provide a better indication
of the amount of work remaining. The")
   (:command-name next)
   (:string "command permits movement to the next case."))
  (let ((number (and (can-apply-cases-p (display-formula display))
                     (cases-number display))))
    (unless (null number)
      (cases-log-cases display)
      (make-display :changed t
                    :formula (cases-formula display number)
		    :explain `((:string "Starting case")
			       (:string ,(cases-number-string
                                          display
                                          number
                                          (cons *current-display*
                                                *display-history*)))
			       (:string "..."))
		    :caseof (list (display-number display) number)))))

;;; Given a formula, return non-nil if cases can be performed
;;; on the formula.

(defun can-apply-cases-p (formula)
  (cond ((if-p formula)
         (or (list-of-free-variables-unexpanded formula) (bool-p formula)))
        ((implies-p formula)
         (can-apply-cases-p (implies-right formula)))
        (t (or (and-p formula) (or-p formula)))))

;;; Given the parent display and the current relative case number,
;;; return the absolute case number as a string.

(defun cases-number-string (display number history)
  (loop with result = (format nil "~A" number)
        for caseof = (display-caseof display)
        when (null caseof) return result
        do (setq result (format nil "~A.~A" (second caseof) result))
           (setq history (search-display-history (first caseof) history))
           (setq display (car history))))

;;; Function to log the result of a CASES command.
;;; Display is the current display prior to the cases command.
;;; Conceptually, the formula in the display is transformed
;;; and parts of the transformed formula can be worked on separately.
;;; The cases command produces a next display that represent
;;; the first case (numbered backwards).

(defun cases-log-cases (display)
  (let* ((bool-p (make-context-for-bool-p-from-display display))
	 (transformed
	  (cases-log-cases-aux
	   (display-formula display) (display-formula-index display) bool-p))
	 (index (display-formula-index display))
	 (vars (unique (list-of-free-variables-unexpanded
			(display-formula display)))))
    (setq transformed
          (cons (car transformed)
                (loop for expr in (cdr transformed)
                      for n = 1 then (+ 1 n)
                      collect
                      (cond ((implies-p expr)
                             (unexpand-formula
                              (make-normalized-implies
                               (expand-formula (implies-left expr)
                                               (cons 1 (cons n index)))
                               (expand-formula (implies-right expr)
                                               (cons 2 (cons n index)))
                               (cons n index))
                              (cons n index)))
                            (t expr)))))
    ;; transformed is either (and case1 ... casen) or (or case1 ... casen)
    (cond ((eq (cases-kind display) 'or)
           (cases-log-cases-or (cdr transformed) 1 (display-base-index display)
                               (mapcar #'(lambda (u) u 2)
                                       (unique
                                        (list-of-free-variables-unexpanded
                                         transformed)))
			       (reverse vars)
			       transformed
			       bool-p)
	   ;; (or qcase1 qcase2 ... qoriginal)
	   )
          (t (cases-log-move-quantifiers-in display bool-p)))))

(defun cases-log-cases-or
    (disjuncts n base-index displacement reversed-vars trans bool-p)
  ;; displacement represents the prefix for index because of implicit
  ;; universal quantification on the free variables

  ;; we are really logging the transformation of (or case1 case2 ... )
  ;; to (true) by starting with n=1 until all disjuncts are handled
  (let* ((disjunct (car disjuncts))
         (index (append displacement base-index))
         (vars (unique (list-of-free-variables-unexpanded disjunct)))
         (renames (mapcar #'(lambda (u) (cons (genvar u) u)) vars))
         (qexpr (make-series-of-quantification
                 'all (mapcar #'car renames)
                 (sublis-eq (mapcar #'(lambda (u) (cons (cdr u) (car u)))
                                    renames)
                            disjunct))))
    ;; qexpr is (all () (all () ... (all () disjunct) ... ))
    ;; where the all-vars have been renamed
    (push-proof-log 'if-equal index qexpr t)
    ;; (if qexpr (or ...) (or ...))
    (log-instantiations 'all nil renames (if-test-index))
    ;; (if (if casen qexpr (false)) (or ...) (or ...)
    (cond ((null vars)
           (push-proof-log 'look-up (cons n (if-left-index)) *true*)
	   (log-or-true n (+ n (length (cdr disjuncts))) (if-left-index))
	   ;; qexpr = casen
	   ;; (if casen (true) (or ...))
	   )
          (t
           (push-proof-log 'case-analysis index 1)
           (push-proof-log 'if-false (if-right-index))
           (push-proof-log 'look-up (list* n 2 (if-left-index)) *true*)
	   (log-or-true
	    n (+ n (length (cdr disjuncts))) (cons 2 (if-left-index)))
	   ;; (if casen
	   ;;     (if qexpr (true) (or ...))
	   ;;     (or ...))
           (push-proof-log 'if-false (if-right-index) *true* t)
           (push-proof-log 'case-analysis index 1 t)
	   ;; (if (if casen qexpr (false)) (true) (or ...))
           (log-universal-subsumption
            (make-if disjunct qexpr *false*)
            (mapcar #'(lambda (u) (make-= (car u) (cdr u))) renames)
            (if-test-index))
	   ;; (if qexpr (true) (or ...))
	   ))
    ;; (if qexpr (true) (or ...))
    (cases-log-move-quantifiers-in-or
     (make-if qexpr *true* trans) reversed-vars nil displacement
     base-index)
    (log-renames renames (cons 1 base-index))
    ;; (if (all () disjunct) (true) (all () (or ...)))
    (push-proof-log 'is-boolean (cons 3 base-index))
    (push-proof-log 'syntax base-index t)
    ;; (or (all () disjunct) (all () (or ...)))
    (unless (null (cdr disjuncts))
      ;; now process remaining disjuncts on inner (all () (or ...))
      (cases-log-cases-or (cdr disjuncts) (+ n 1) (cons 2 base-index)
                          displacement
			  reversed-vars
			  trans bool-p)
      (push-proof-log 'syntax base-index t)
      ;; (or (all () disjunct) (all () nextdisjunct) ...)
      ))
  )

(defun cases-log-move-quantifiers-in-or
    (formula reversed-vars processed-vars displacement base-index)
  (unless (null displacement)
    ;; (all () (if qexpr (true) (or ...)))
    (let ((index (append (cdr displacement) base-index))
	  (right (make-series-of-quantification
		  'all processed-vars (if-right formula))))
      (log-all-case-analysis-1
       (make-all (list (car reversed-vars))
		 (make-if (if-test formula)
			  *true*
			  right))
       index)
      ;; (if qexpr (all () (true)) (all () (or ...)))
      (push-proof-log 'remove-universal (if-left-index))
      (push-proof-log 'is-boolean (if-left-index) t)
      ;; (if qexpr (true) (all (trailing-vars) (or ...)))
      (cases-log-move-quantifiers-in-or
       formula
       (cdr reversed-vars)
       (cons (car reversed-vars) processed-vars)
       (cdr displacement)
       base-index)))
  )

(defun cases-log-cases-aux (formula index bool-p)
  (cond ((if-p formula)
	 (log-cases-if formula bool-p index)
         (make-and (make-implies (if-test formula)
                                 (if-left formula))
                   (make-implies (negate (if-test formula)
                                         (cons 1 (and-right-index))
					 (make-context-for-bool-p
					  (make-implies
					   (make-not (if-test formula))
					   (if-right formula))
					  (and-right-index)))
                                 (if-right formula))))
	((implies-p formula)
	 (push-proof-log 'syntax index)
	 ;; (if left (if orig-right (true) (false)) (true))
         (let ((left (implies-left formula))
               (right (cases-log-cases-aux (implies-right formula)
                                           (cons 1 (if-left-index))
					   (make-context-for-bool-p
					    (make-if 1 1 1) (if-left-index)))))
	   (if (bool-p right)
	       (push-proof-log 'is-boolean (if-left-index) t)
	     ;; bool-p must be non-nil! *****
	     (log-remove-coercion-from-boolean-context bool-p index))
	   ;; (if left right (true))
           (if (and-p right)
               (log-convert-true-to-and (length (cdr right)) (if-right-index))
             (log-convert-true-to-or (length (cdr right)) (if-right-index)))
	   ;; (if left (and right1 ...) (and (true) ...))
           (push-proof-log 'case-analysis index 0 t)
	   ;; (and (if left right1 (true)) (if left right2 (true)) ...)
	   (cons (car right)
		 (loop for expr in (cdr right)
		       for i = 1 then (+ i 1)
		       collect
		       (progn
			 (if (bool-p expr)
			     (push-proof-log 'is-boolean (list* 2 i index))
			   (let ((bool-p
				  (make-context-for-bool-p
				   (cons
				    (car right)
				    (loop for x in (cdr right)
					  for j = 1 then (+ j 1)
					  collect
					  (if (< j i)
					      (make-implies left x)
					    (make-if left x *true*))))
				   index)))
			     (log-coerce-expr-in-boolean-context
			      bool-p (list* 2 i index))))
			 (push-proof-log 'syntax (cons i index) t)
			 (make-implies left expr))))))
        (t formula)))

(defun log-convert-true-to-and (n index)
  (push-proof-log 'if-true index *false* t)
  (push-proof-log 'is-boolean (if-left-index))
  (push-proof-log 'syntax index t)
  ;; We now have (and (true) (true))
  (dotimes (i (- n 2))
    (push-proof-log 'if-true index *false* t)
    (push-proof-log 'is-boolean (if-left-index))
    (push-proof-log 'syntax index t)
    (push-proof-log 'syntax index t)))

(defun log-convert-true-to-or (n index)
  (push-proof-log 'if-true index *true* t)
  (push-proof-log 'is-boolean (if-right-index))
  (push-proof-log 'syntax index t)
  ;; We now have (or (true) (true))
  (log-convert-true-to-or-aux (- n 2) index))

(defun log-convert-true-to-or-aux (n index)
  ;; (or (true) (true))
  (when (> n 0)
    (push-proof-log 'if-true (cons 2 index) *true* t)
    (push-proof-log 'is-boolean (list* 3 2 index))
    (push-proof-log 'syntax (cons 2 index) t)
    ;; (or (true) (or (true) (true)))
    (log-convert-true-to-or-aux (- n 1) (or-right-index))
    (push-proof-log 'syntax index t)))

(defun log-unexpand-universal-quantification (n index)
  (when (> n 1)
    (log-unexpand-universal-quantification (- n 1) (all-expr-index))
    (push-proof-log 'syntax index t)))

(defun log-expand-universal-quantification (n index)
  (when (> n 1)
    (push-proof-log 'syntax index)
    (log-expand-universal-quantification (- n 1) (all-expr-index))))

(defun cases-log-all-in-and-aux (n cases index)
  (cond ((> cases 2)
	 ;; (all (var1 ...) (and case1 case2 ...))
	 (push-proof-log 'syntax (all-expr-index))
	 ;; (all (var1 ...) (and case1 (and case2 ...)))
	 (push-proof-log 'syntax (all-expr-index))
	 ;; (all (var1 ...)
	 ;;      (if case1 (if (and case2 ...) (true) (false) (false))))
	 (push-proof-log 'is-boolean (cons 2 (all-expr-index)) t)
	 (push-proof-log 'all-case-analysis index)
	 ;; (if (all (var1 ...) case1) (all (var1 ...) (and case2 ...)) (false))
	 (cases-log-all-in-and-aux n (- cases 1) (if-left-index))
	 (log-expand-universal-quantification n (if-test-index))
	 (push-proof-log 'is-boolean (if-left-index))
	 (push-proof-log 'syntax index t)
	 ;; (and (all (var1) (all (var2) ...case1)) (and ...))
	 (push-proof-log 'syntax index t)
	 ;; (and (all (var1) ...) (all (var1) ...) ...)
	 )
	((= cases 2)
	 ;; (all (var1 ...) (and case1 case2))
	 (push-proof-log 'syntax (all-expr-index))
	 ;; (all (var1 ...) (if case1 (if case2 (true) (false)) (false)))
	 (push-proof-log 'all-case-analysis index)
	 ;; (if (all (var1 ...) case1)
	 ;;     (all (var1 ...) (if case2 (true) (false)))
	 ;;     (false))
	 (log-remove-bool-coercion-from-all-expr (if-left-index))
	 (log-expand-universal-quantification n (if-test-index))
	 (log-expand-universal-quantification n (if-left-index))
	 (push-proof-log 'is-boolean (if-left-index))
	 (push-proof-log 'syntax index t)
	 ;; (and (all (var1) ...) (all (var1) ...)
	 )))

(defun cases-log-all-in-and (n cases index)
  ;; (all (var1) ... (all (varn) (and case1 ... )) ...)
  (log-unexpand-universal-quantification n index)
  ;; (all (var1 ... varn) (and case1 ... ))
  (cases-log-all-in-and-aux n cases index))

(defun cases-log-move-quantifiers-in (display bool-p)
  (let ((formula (display-formula display))
	(base-index (display-base-index display)))
    (let ((vars (unique (list-of-free-variables-unexpanded formula)))
	  (number-of-cases (cases-number display)))
      (cases-log-all-in-and (length vars) number-of-cases base-index)
      (dotimes (i number-of-cases)
        (let* ((conjunct (cases-formula display (- number-of-cases i)))
	       (freevars (unique (list-of-free-variables-unexpanded
                                  conjunct))))
	  (cases-log-delete-quantifiers
	   vars freevars conjunct (cons (1+ i) base-index) bool-p)
	  (let ((orig-vars (loop for var in vars
				 when (member-eq var freevars)
				 collect var)))
	    (log-permute-quantifiers
	     orig-vars freevars (cons (1+ i) base-index)))
	  )))))

(defun cases-log-delete-quantifiers (vars freevars formula index bool-p)
  (unless (null vars)
    (let ((var (car vars)))
      (cond ((member-eq var freevars)
	     (cases-log-delete-quantifiers
	      (cdr vars) freevars formula (all-expr-index)
	      (make-context-for-bool-p (make-all-single var *true*) index)))
	    (t
	     (push-proof-log 'remove-universal index)
	     (if (or (cdr vars) (bool-p formula))
		 (push-proof-log 'is-boolean index t)
	       (log-remove-coercion-from-boolean-context bool-p index))
	     (cases-log-delete-quantifiers
	      (cdr vars) freevars formula index bool-p))))))

(defun log-flip-universals-reverse (number-of-vars index)
  (unless (zerop number-of-vars)
    (log-flip-universals-reverse (- number-of-vars 1) (all-expr-index))
    (push-proof-log 'flip-universals index)))


;;; ========== The NEXT command.

(defcmd nextf (:display)
  ((:string "Proceed to the next non-trivial case or, if there is
no more non-trivial case, completes the proof. Note that some
non-trivial cases may be short-circuited."))
  (and (display-caseof display)
       (neq (display-caseof display) t)
       (next-display (display-formula display)
                     (display-caseof display)
                     (cons *current-display* *display-history*)
		     (make-context-for-bool-p-from-parent-display display))))


;;; The main routine for the next command.

(defun next-display (formula caseof history bool-p)
  (let* ((next-history (search-display-history (first caseof) history))
         (parent-display (car next-history))
         (parent-caseof (display-caseof parent-display)))
    (cond
     ;; short-circuit
     ((and (true-p formula) (eq (cases-kind parent-display) 'or))
      (log-or-true (- (+ (cases-number parent-display) 1) (second caseof))
		   (+ (cases-number parent-display) 1)
		   (display-base-index parent-display))
      ;; defer making a display if need to recur
      (cond ((or (null parent-caseof) (eq parent-caseof t))
             (make-display :changed t :formula *true*
                           :explain
                           (cases-complete parent-display next-history)
                           :caseof
                           (or (display-caseof parent-display) t)))
            (t (next-display *true* parent-caseof next-history bool-p))))
     ((and (false-p formula) (eq (cases-kind parent-display) 'and))
      (log-and-false (- (+ (cases-number parent-display) 1) (second caseof))
		     (cases-number parent-display)
		     (display-base-index parent-display))
      ;; defer making a display if need to recur
      (cond ((or (null parent-caseof) (eq parent-caseof t))
             (make-display :changed t :formula *false*
                           :explain
                           (cases-complete parent-display next-history)
                           :caseof (or (display-caseof parent-display) t)))
            (t (next-display *false* parent-caseof next-history bool-p))))
     ;; collect cases
     ((= (second caseof) 1)
      (let ((result (if (eq (cases-kind parent-display) 'or)
                        (cases-collect-or parent-display formula bool-p)
                      (cases-collect parent-display formula bool-p))))
        ;; defer making a display if need to recur
        (cond ((and (or (true-p result) (false-p result))
                    parent-caseof (neq parent-caseof t))
               (next-display result parent-caseof next-history bool-p))
              (t (make-display
                  :changed t
                  :formula result
                  :explain (cases-complete parent-display next-history)
                  :caseof (or parent-caseof t))))))
     ;; move to next case
     (t (let ((formula (cases-formula parent-display (1- (second caseof)))))
          ;; defer making a display if need to recur
          (cond ((or (true-p formula) (false-p formula))
                 (next-display formula
                               (list (first caseof) (1- (second caseof)))
                               next-history
			       bool-p))
                (t
                 (make-display
                  :changed t
                  :formula formula
                  :explain `((:string "Starting case")
                             (:string ,(cases-number-string
                                        parent-display
                                        (1- (second caseof))
                                        history))
                             (:string "..."))
                  :caseof (list (first caseof)
                                (1- (second caseof)))))))))))

;;; Given the parent display and the formula for the last case,
;;; collect the cases into a single conjunction.
;;; This is a conjunctive case (originally an "and" or "if").
;;; An "if" would have been transformed into a conjunction
;;; of two implications.

(defun cases-collect (display formula bool-p)
  (let ((history (cons *current-display* *display-history*))
        (collected nil)
	(number (display-number display))
	(cases (cases-number display))
	(index (display-base-index display)))
    (if (true-p formula)
	(log-and-true cases cases index)
	(push formula collected))
    (loop with n = 2
	  for caseof = (list number n)
	  when (> n cases)
	  do (cond ((= (length collected) 0)
		    ;; (and)
		    (log-and-0 index)
		    (return *true*))
		   ((= (length collected) 1)
		    ;; (and case)
		    (log-and-1 index)
		    ;; (if case (true) (false))
		    (let ((form (car collected)))
		      (return
		       (coerce-to-bool
			(universally-quantify
			 (unique (list-of-free-variables-unexpanded form)) form)
			index
			bool-p))))
		   ;; Must also rename here!!!
		   (t (cases-log-collect-all collected index)
		      (return
		       (let* ((vars (unique
				     (list-of-free-variables-unexpanded
				      (cons 'and collected))))
			      ;; ind is the display-formula-index
			      ;; of the new display!!
			      (ind (display-formula-index-aux
				    vars (display-base-index display))))
			 (cons 'and
			       (loop for expr in collected
				     for i = 1 then (+ i 1)
				     collect
				     (unexpand-formula
				      (unrename-quantified-variables
				       (rename-quantified-variables
					(expand-formula
					 expr (cons i ind))
					(cons i ind))
				       (cons i ind) vars)
				      (cons i ind))))))))
	  do (let ((next-history (advance-to-caseof caseof history)))
               (cond (next-history
                      (setq history next-history)
                      (cond ((true-p (display-formula (car history)))
			     (cond ((and (= n cases) (= (length collected) 1))
				    ;; (and (true) expr)
				    (log-and-true 1 2 index))
				   ((and (= n (- cases 1)) (null collected))
				    ;; (and ? (true))
				    (log-and-true 2 2 index)
				    )
				   ((and (= n cases) (null collected))
				    ;; (and (true))
				    (log-and-true 1 1 index))
				   (t
				    (log-and-true
				     (1+ (- cases n))
				     (+ (1+ (- cases n)) (length collected))
				     index)
				    )))
                            (t (push (display-formula (car history))
                                     collected))))
                     ;; trivial case that didn't even have a display
                     ;; log its removal from conjunct
		     ((and (= n cases) (= (length collected) 1))
		      ;; (and (true) expr)
		      (log-and-true 1 2 index))
		     ((and (= n (- cases 1)) (null collected))
		      ;; (and ? (true))
		      (log-and-true 2 2 index))
		     ((and (= n cases) (null collected))
		      ;; (and (true))
		      (log-and-true 1 1 index))
                     (t
		      (log-and-true (1+ (- cases n))
				    (+ (1+ (- cases n)) (length collected))
				    index)))
               (incf n)))))

;;; Given the parent display and the formula for the last case,
;;; collect the cases plus the original formula (each fully quantified)
;;; into a single disjunction. This is a disjunctive case (originally
;;; an "or").

(defun cases-collect-or (display formula bool-p)
  (let ((history (cons *current-display* *display-history*))
        (collected nil)
	(number (display-number display))
	(cases (cases-number display))
	(index (display-base-index display)))
    (let ((expr (cons 'or (loop for i from cases downto 1
				collect (cases-formula display i)))))
      (push (unexpand-formula
	     (make-series-of-quantification
	      `all
	      (unique
	       (list-of-free-variables-unexpanded expr))
	      expr)
	     (cons (+ cases 1) index))
	    collected))
    (if (false-p formula)
	(log-or-false cases (+ cases 1) index)
      (push formula collected))
    (loop with n = 2
	  for caseof = (list number n)
	  when (> n cases)
	  do (cond ((= (length collected) 1)
		    ;; (or qorig)
		    (log-or-1 index)
		    (return (coerce-to-bool (car collected) index)))
		   (t (return
		       (cons
			'or
			(append
			 (loop for expr in (butlast collected)
			       for i = 1 then (+ i 1)
			       collect
			       (unexpand-formula
				(make-series-of-quantification
				 `all
				 (unique
				  (list-of-free-variables-unexpanded expr))
				 expr)
				(cons i index)))
			 (last collected))))))
	  do (let ((next-history (advance-to-caseof caseof history)))
               (cond (next-history
                      (setq history next-history)
                      (cond ((false-p (display-formula (car history)))
			     (cond ((and (= n cases) (= (length collected) 1))
				    ;; (or (false) qorig)
				    (log-or-false 1 2 index))
				   (t
				    (log-or-false
				     (1+ (- cases n))
				     (+ (1+ (- cases n)) (length collected))
				     index))))
                            (t (push (display-formula (car history))
                                     collected))))
                     ;; trivial case that didn't even have a display
                     ;; log its removal from disjunct
		     ((and (= n cases) (= (length collected) 1))
		      ;; (or (false) case)
		      (log-or-false 1 2 index))
                     (t
		      (log-or-false (1+ (- cases n))
				    (+ (1+ (- cases n)) (length collected))
				    index)))
               (incf n)))))

(defun cases-log-collect-all-aux (var list-of-conjuncts index)
  (cond ((> (length list-of-conjuncts) 2)
	 ;; (and expr1 expr ...)
	 (push-proof-log 'syntax index)
	 ;; (and expr1 (and expr2 ...))
	 (cases-log-collect-all-aux var (cdr list-of-conjuncts)
				    (and-right-index))
	 ;; (and expr1 (all (var) ...))
	 (cond ((member-eq var (list-of-free-variables-unexpanded
				(car list-of-conjuncts)))
		;; (and (all (var) ...) (all (var)...))
		(push-proof-log 'syntax index)
		;; (if (all (var) ...)
		;;     (if (all (var) ...) (true) (false))
		;;     (false))
		(push-proof-log 'is-boolean (if-left-index) t)
		(push-proof-log 'all-case-analysis index t)
		;; (all (var) (if ex1 (and ex2 ...) (false)))
		(push-proof-log 'is-boolean (cons 2 (all-expr-index)))
		(push-proof-log 'syntax (all-expr-index) t)
		;; (all (var) (and ex1 (and ex2 ...)))
		(push-proof-log 'syntax (all-expr-index) t)
		;; (all (var) (and ex1 ex2 ...))
		)
	       (t
		;; (and expr1 (all (var) ...))
		(push-proof-log 'syntax index)
		(log-coerce-if-test-to-bool index)
		(push-proof-log 'remove-universal (if-test-index) (list var) t)
		;; (if (all (var) expr1)
		;;     (if (all (var) ...) (true) (false))
		;;     (false))
		(push-proof-log 'is-boolean (if-left-index) t)
		(push-proof-log 'all-case-analysis index t)
		;; (all (var) (if ex1 (and ex2 ...) (false)))
		(push-proof-log 'is-boolean (cons 2 (all-expr-index)))
		(push-proof-log 'syntax (all-expr-index) t)
		;; (all (var) (and ex1 ex2))
		(push-proof-log 'syntax (all-expr-index) t)
		;; (all (var) (and ex1 ex2 ...))
		)))
	((= (length list-of-conjuncts) 2)
	 ;; (and expr1 expr2)
	 (push-proof-log 'syntax index)
	 ;; (if expr1 (if expr2 (true) (false)) (false))
	 (unless (member-eq var (list-of-free-variables-unexpanded
				 (car list-of-conjuncts)))
	   (log-coerce-if-test-to-bool index)
	   (push-proof-log 'remove-universal (if-test-index) (list var) t))
	 ;; (if (all (var) ...) (if expr2 (true) (false)) (false))
	 (cond ((member-eq var (list-of-free-variables-unexpanded
				(second list-of-conjuncts)))
		(push-proof-log 'is-boolean (if-left-index) t)
		(log-coerce-all-expr-to-bool (list var) (if-left-index)))
	       (t
		(push-proof-log 'remove-universal (if-left-index) (list var) t)
		(log-coerce-all-expr-to-bool (list var) (if-left-index))))
	 ;; (if (all (var) ...) (all (var) (if ex2 (true) (false))) (false))
	 (push-proof-log 'all-case-analysis index t)
	 ;; (all (var) (if ex1 (if ex2 (true) (false)) (false)))
	 (push-proof-log 'syntax (all-expr-index) t)
	 ;; (all (var) (and ex1 ex2))
	 )))


(defun cases-log-collect-all (list-of-conjuncts index)
  (let ((vars (unique (list-of-free-variables-unexpanded
		       (make-conjunction list-of-conjuncts))))
	(collected-vars nil))
    (loop for var in vars
	  for i = 0 then (1+ i)
	  do (let ((current-index (repeat-all-expr-index i index)))
	       (loop for conjunct in list-of-conjuncts
		   for j = 1 then (1+ j)
		   do (cases-log-flip-quantifiers
		       var collected-vars conjunct (cons j current-index)))
	       (cases-log-collect-all-aux var list-of-conjuncts current-index)
	       (push var collected-vars)))))

(defun cases-log-flip-quantifiers (var collected-vars formula index)
  (let ((vars (set-difference-eq
	       (unique (list-of-free-variables-unexpanded formula))
	       collected-vars)))
    (when (member-eq var vars)
      (log-flip-universals-reverse
       (- (length vars) (length (member-eq var vars)))
       index))))

;;; Advance (really go back in history) to the point where caseof
;;; or any of its subcases was last worked on.  If the case did not
;;; produce a display, return nil.

(defun advance-to-caseof (caseof history)
  (loop do (multiple-value-bind (success result-history)
             (advance-to-caseof-aux
              (display-caseof (car history))
              caseof
              history)
             (cond (success (return history))
                   ((null result-history) (setq history (cdr history)))
                   (t (setq history result-history)))
             (when (<= (display-number (car history)) (first caseof))
               (return nil)))))

;;; The main searching routine for advance-to-caseof.
;;; If unsuccessful, the next iteration can start from the returned
;;; history value, possibly jumping over many displays.  (A nil
;;; value for the returned history means cannot jump over next
;;; display.)

(defun advance-to-caseof-aux (c1 c2 history)
  (cond ((equal c1 c2) (values t history))
        ((or (null c1) (<= (first c1) (first c2)))
         (values nil nil))
        (t (let ((next-history (search-display-history (first c1) history)))
             (multiple-value-bind (success result-history)
               (advance-to-caseof-aux
                (display-caseof (car next-history)) c2 next-history)
               (cond (success (values t history))
                     ((null result-history) (values nil (cdr next-history)))
                     (t (values nil result-history))))))))
                      
;;; Produce the explain for completed cases.

(defun cases-complete (display history)
  (let ((caseof (display-caseof display)))
    (cond ((null caseof) `((:string "Completing all cases produces ...")))
	  (t `((:string "Completing case")
	       (:string ,(cases-number-string
			   (search-display (first caseof))
			   (second caseof)
                           history))
	       (:string "produces ..."))))))


;;; ========== The DELETE-HYPOTHESES command.

;;; Note that DELETE-HYPOTHESES doesn't automatically take you to the
;;; case with deleted hypotheses. You must still do a CASES.

(defcmd delete-hypotheses (hypothesis-list :display)
  ((:string "Produce a disjunction of the current subformula with the
hypotheses specified in")
   (:command-argument hypothesis-list)
   (:string "deleted and the entire current subformula. The")
   (:command-name cases)
   (:string "command may then be used to start the proof of the
case with the deleted hypotheses which, if successful, completes
the proof of the entire current formula (you must complete it using the")
   (:command-name next)
   (:string "command)."))
  (unless
      (without-proof-logging
       (member-eq nil (mapcar #'parse-formula-phase-1 hypothesis-list)))
    (let* ((formula (display-formula display))
	   (hypo-list (and (implies-p formula)
                           (if (and-p (implies-left formula))
                               (cdr (implies-left formula))
                             (list (implies-left formula))))))
      (when (subsetp-equal hypothesis-list hypo-list)
	(let ((remaining-hyp (set-difference-equal hypo-list hypothesis-list)))
          (log-delete-hypotheses formula hypo-list remaining-hyp
                                 (implies-right formula) index)
	  (make-display
           :formula
           (make-disjunction
            (list (cond ((null remaining-hyp) (implies-right formula))
                        ((= (length remaining-hyp) 1)
                         (make-implies (car remaining-hyp)
                                       (implies-right formula)))
                        (t (make-implies
                            (cons 'and remaining-hyp)
                            (implies-right formula))))
                  formula))
           :explain `((:string "Deleting hypotheses")
                      (:formula-list ,hypothesis-list)
                      (:string "produces ..."))))))))

(defun log-delete-hypotheses (formula old-list new-list conclusion index)
  (cond ((null new-list)
         (push-proof-log 'if-equal index conclusion t)
         ;; We now have:
         ;; (if conclusion
         ;;     (implies hypotheses conclusion)
         ;;     (implies hypotheses conclusion))
         (push-proof-log 'look-up (cons 2 (if-left-index)) *true*)
         (log-implies-to-or (if-left-index))
	 (log-or-true 2 2 (if-left-index))
	 (push-proof-log 'is-boolean (if-right-index))
	 (push-proof-log 'syntax index t)
	 ;; (or conclusion (implies hypotheses conclusion))
	 )
        (t (let ((new-hyps (make-conjunction new-list)))
	     ;; *** new-hyps in expanded form!
             (push-proof-log
	      'if-equal index (make-implies new-hyps conclusion) t)
             (push-proof-log 'syntax (if-test-index))
	     (log-remove-coercion-from-boolean-context
	      (make-context-for-bool-p (make-if 1 1 1) index)
	      (cons 2 (if-test-index)))
             ;; We now have:
             ;; (if (if new-hyps conclusion (true))
             ;;     (implies hypotheses conclusion)
             ;;     (implies hypotheses conclusion))
             (log-delete-hypotheses-aux
	      formula old-list new-list conclusion index)
             ;; We now have:
             ;; (if (implies new-hyps conclusion)
             ;;     (true)
             ;;     (implies hypotheses conclusion))
	     (push-proof-log 'is-boolean (if-right-index))
	     (push-proof-log 'syntax index t)
	     ))))

;;; Note that old-list will have length >= 2 at this point.

(defun log-delete-hypotheses-aux (formula old-list new-list conclusion index)
  ;; (if (if new-hyps conclusion (true))
  ;;     (implies hypotheses conclusion)
  ;;     (implies hypotheses conclusion))
  (push-proof-log 'case-analysis index 1)
  (let* ((new-hyp (car new-list))
	 ;; there is some n where nth hypothesis is new-hyp
	 (n (- (+ (length old-list) 1)
	       (length (member-equal new-hyp old-list)))))
    (cond ((= (length new-list) 1)
	   ;; At this point we have:
	   ;; (if new-hyp
	   ;;     (if conclusion
	   ;;         (implies hypotheses conclusion)
	   ;;         (implies hypotheses conclusion))
	   ;;     (if (true)
	   ;;         (implies hypotheses conclusion)
	   ;;         (implies hypotheses conclusion)))
	   (push-proof-log 'look-up (list* 2 2 (if-left-index)) *true*)
	   (log-implies-to-or (cons 2 (if-left-index)))
	   (log-or-true 2 2 (cons 2 (if-left-index)))
	   ;; (if new-hyp
	   ;;     (if conclusion (true) (implies hypotheses conclusion))
	   ;;     (if (true)
	   ;;         (implies hypotheses conclusion)
	   ;;         (implies hypotheses conclusion)))
	   (cond ((bool-p new-hyp)
		  (log-look-up-false
		   (list* n 1 2 (if-right-index))))
		 (t (let ((hypotheses (cons 'and old-list)))
		      (log-coerce-to-bool-inside-connective
		       (cons 'and old-list) n (list* 1 2 (if-right-index)))
		      (log-look-up-false-for-coercion
		       (list* n 1 2 (if-right-index))))))
	   (log-and-false n (length old-list) (list* 1 2 (if-right-index)))
	   ;; (if new-hyp
	   ;;     (if conclusion (true) (implies hypotheses conclusion))
	   ;;     (if (true)
	   ;;         (implies (false) conclusion)
	   ;;         (implies hypotheses conclusion))
	   (log-implies-to-or (cons 2 (if-right-index)))
	   (push-proof-log 'syntax (list* 1 2 (if-right-index)))
	   (push-proof-log 'if-false (list* 1 2 (if-right-index)))
	   (log-or-true 1 2 (cons 2 (if-right-index)))
	   ;; At this point we have:
	   ;; (if new-hyp
	   ;;     (if conclusion (true) (implies hypotheses conclusion))
	   ;;     (if (true) (true) (implies hypotheses conclusion)))
	   (push-proof-log 'case-analysis index 1 t)
	   ;; (if (if new-hyp conclusion (true))
	   ;;     (true)
	   ;;     (implies hypotheses conclusion))
	   (if (bool-p conclusion)
	       (push-proof-log 'is-boolean (cons 2 (if-test-index)))
	     (log-coerce-expr-in-boolean-context
	      (make-context-for-bool-p (make-if 1 1 1) index)
	      (cons 2 (if-test-index))))
	   (push-proof-log 'syntax (if-test-index) t)
	   ;; We get:
	   ;; (if (implies new-hyp conclusion)
	   ;;     (true)
	   ;;     (implies hypotheses conclusion))
	   )
	  (t ; (> (length new-list) 1)
	   ;; At this point we have:
	   ;; (if (and hyp1 rest-hyp)
	   ;;     (if conclusion
	   ;;         (implies hypotheses conclusion)
	   ;;         (implies hypotheses conclusion))
	   ;;     (if (true)
	   ;;         (implies hypotheses conclusion)
	   ;;         (implies hypotheses conclusion)))
	   (push-proof-log 'syntax (if-test-index))
	   (log-remove-coercion-from-boolean-context
	    (make-context-for-bool-p (make-if 1 1 1) index)
	    (cons 2 (if-test-index)))
	   ;; (if (if hyp1 rest-hyp (false))
	   ;;     (if conclusion
	   ;;         (implies hypotheses conclusion)
	   ;;         (implies hypotheses conclusion))
	   ;;     (if (true)
	   ;;         (implies hypotheses conclusion)
	   ;;         (implies hypotheses conclusion)))
	   (push-proof-log 'case-analysis index 1)
	   ;; At this point we have:
	   ;; (if hyp1
	   ;;     (if rest-hyp
	   ;;         (if conclusion
	   ;;             (implies hypotheses conclusion)
	   ;;             (implies hypotheses conclusion))
	   ;;         (if (true)
	   ;;             (implies hypotheses conclusion)
	   ;;             (implies hypotheses conclusion)))
	   ;;     (if (false)
	   ;;         (if conclusion
	   ;;             (implies hypotheses conclusion)
	   ;;             (implies hypotheses conclusion))
	   ;;         (if (true)
	   ;;             (implies hypotheses conclusion)
	   ;;             (implies hypotheses conclusion))))
	   (push-proof-log 'if-false (if-right-index))
	   ;; (if hyp1
	   ;;     (if rest-hyp
	   ;;         (if conclusion
	   ;;             (implies hypotheses conclusion)
	   ;;             (implies hypotheses conclusion))
	   ;;         (if (true)
	   ;;             (implies hypotheses conclusion)
	   ;;             (implies hypotheses conclusion)))
	   ;;     (if (true)
	   ;;         (implies hypotheses conclusion)    <- Focus on this
	   ;;         (implies hypotheses conclusion)))
	   (cond ((bool-p new-hyp)
		  (log-look-up-false
		   (list* n 1 2 (if-right-index))))
		 (t (let ((hypotheses (cons 'and old-list)))
		      (log-coerce-to-bool-inside-connective
		       (cons 'and old-list) n (list* 1 2 (if-right-index)))
		      (log-look-up-false-for-coercion
		       (list* n 1 2 (if-right-index))))))
	   (log-and-false n (length old-list) (list* 1 2 (if-right-index)))
	   ;; (if hyp1
	   ;;     (if rest-hyp
	   ;;         (if conclusion
	   ;;             (implies hypotheses conclusion)
	   ;;             (implies hypotheses conclusion))
	   ;;         (if conclusion
	   ;;             (implies hypotheses conclusion)
	   ;;             (implies hypotheses conclusion)))
	   ;;     (if (true)
	   ;;         (implies (false) conclusion)
	   ;;         (implies hypotheses conclusion)))
	   (log-implies-to-or (cons 2 (if-right-index)))
	   ;; (if hyp1
	   ;;     (if rest-hyp
	   ;;         (if conclusion
	   ;;             (implies hypotheses conclusion)
	   ;;             (implies hypotheses conclusion))
	   ;;         (if conclusion
	   ;;             (implies hypotheses conclusion)
	   ;;             (implies hypotheses conclusion)))
	   ;;     (if (true)
	   ;;         (or (not (false)) conclusion)
	   ;;         (implies hypotheses conclusion)))
	   (push-proof-log 'syntax (list* 1 2 (if-right-index)))
	   (push-proof-log 'if-false (list* 1 2 (if-right-index)))
	   (log-or-true 1 2 (cons 2 (if-right-index)))
	   ;; At this point we have:
	   ;; (if hyp1
	   ;;     (if rest-hyp
	   ;;         (if conclusion
	   ;;             (implies hypotheses conclusion)
	   ;;             (implies hypotheses conclusion))
	   ;;         (if conclusion
	   ;;             (implies hypotheses conclusion)
	   ;;             (implies hypotheses conclusion)))
	   ;;     (if (true)
	   ;;         (true)
	   ;;         (implies hypotheses conclusion)))
	   (push-proof-log 'if-equal (cons 3 (if-left-index)))
	   (push-proof-log 'if-equal (cons 3 (if-left-index)) '(true) t)
	   (push-proof-log 'case-analysis (if-left-index) 1 t)
	   ;; We now have:
	   ;; (if hyp1
	   ;;     (if (if rest-hyp conclusion (true))
	   ;;         (implies hypotheses conclusion)
	   ;;         (implies hypotheses conclusion))
	   ;;     (if (true)
	   ;;         (true)
	   ;;         (implies hypotheses conclusion)))
	   (log-delete-hypotheses-aux formula old-list (cdr new-list) conclusion
				      (if-left-index))
	   ;; We now have:
	   ;; (if hyp1
	   ;;     (if (implies rest-hyps conclusion)
	   ;;         (true)
	   ;;         (implies hypotheses conclusion))
	   ;;     (if (true)
	   ;;         (true)
	   ;;         (implies hypotheses conclusion)))
	   (push-proof-log 'case-analysis index 1 t)
	   ;; (if (if hyp1 (implies rest-hyps conclusion) (true))	   
	   ;;     (true)
	   ;;     (implies hypotheses conclusion))
	   (push-proof-log 'is-boolean (cons 2 (if-test-index)))
	   (push-proof-log 'syntax (if-test-index) t)
	   (log-unnest-implies conclusion (if-test-index))
	   (when (>= (length new-list) 3)
	     (push-proof-log 'syntax (cons 1 (if-test-index)) t))
	   ;; We finally get:
	   ;; (if (implies (and hyp1 rest-hyps) conclusion)
	   ;;     (true)
	   ;;     (implies hypotheses conclusion))
	   ))))
