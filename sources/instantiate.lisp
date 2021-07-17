
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


;;; The INSTANTIATE command (manual instantiation of quantification).
;;; The actual instantiation can be quite complicated, moving around
;;; various quantifications to make the instantiation possible (e.g.,
;;; to make variable references in scope).

(defcmd instantiate (instantiations :display)
  ((:string "The")
   (:command-name instantiate)
   (:string "command performs simultaneous instantiations on the current
subformula. The instantiations to be performed is given by")
   (:command-argument instantiations)
   (:punctuation ".")
   (:string "To allow the instantiations to
occur, the scopes of quantifiers in the formula may be extended or
contracted. Logical equivalence is maintained by keeping the
uninstantiated subexpression as an extra conjunct or disjunct.
The requested instantiations may be disallowed, in which case the
command has no effect.") (:newline) (:newline)
   (:string "Example:") (:newline) (:newline)
   (:string "Beginning proof of ...") (:newline)
   (:formula (implies (all (i j k) (p i j k)) (all (l n) (p l m n))))
   (:newline) (:newline)
   (:command (instantiate '((= i l) (= j m) (= k n))))
   (:newline) (:newline)
   (:string "Instantiating")
   (:formula-list ((= i l) (= j m) (= k n)))
   (:string "gives ...")
   (:newline)
   (:formula (all (l n) (implies (and (p l m n) (all (i j k) (p i j k)))
			       (p l m n)))))
  (let ((substs (instantiate-parse-instantiations instantiations)))
    (when (and substs (not (substitutions-unmentionable-p substs)))
      (let ((*uncase-analysis-form-flag* nil)
            (vars (unique (list-of-free-variables-unexpanded
                           (display-formula display)))))
	(let ((result
	       (instantiate-formula
		(mapcar #'car substs) substs
                (internal-form
                 (universally-quantify
                  vars (display-formula display))
                 (display-base-index display))
		(make-context-for-bool-p-from-display display)
		(display-base-index display))))
	  (when result
	    (make-display :formula
			  (output-form result (display-base-index display))
			  :explain `((:string "Instantiating")
				     (:formula-list ,instantiations)
				     (:string "gives ..."))))))
      )))



;;; Code to check the well-formedness of instantiations.

(defun instantiate-parse-instantiations (instantiations)
  (when (without-errors (nil)
	  (cond ((atom instantiations)
		 (parse-error 'instantiations-ill-formed
			      instantiations))
		((not (every
		       #'(lambda (u) (and (=-p u)
					  (variable-p (=-left u))))
			     instantiations))
		 (parse-error 'instantiations-ill-formed
			      instantiations))
		((not (= (length
			  (unique (mapcar #'=-left instantiations)))
			 (length instantiations)))
		 (parse-error 'duplicate-instantiations
			      (mapcar #'=-left instantiations)))))
    (let ((internal-instantiations
	   (mapcar #'(lambda  (u) (parse-formula (=-right u)))
		   instantiations)))
      (unless (some #'null internal-instantiations)
	(mapcar #'(lambda (u v) (cons (=-left u)
				      (rename-quantified-variables v nil)))
		instantiations internal-instantiations)))))



;;; The basic strategy is this:
;;; 1. Out of scope vars start out as variables that occur free in
;;;    the right side of the instantiations.
;;; 2. We need to traverse (dive into) the formula until we hit a
;;;    quantification of any of the variables to be instantiated.
;;; 3. When diving inside a quantification, some out of scope variables
;;;    may become in scope.
;;; 4. When we hit a quantification to be instantiated, we
;;;    must move out quantification of remaining out of scope variables,
;;;    and then coalesce the quantifications of variables to be
;;;    instantiated.
;;; 5. Only then can the instantiations be performed.

;;; Note that instantiate works on IF form where all boolean
;;; connectives have been converted into IF expressions.

;;; The first group of routines does the traversal while trying to
;;; instantiate.  These routines are prefixed with "instantiate-".
;;; When we hit a quantification that is to be instantiated,
;;; then instantiate-quantification-aux is called. Only one attempt
;;; is made (only one call of instantiate-quantification-aux is
;;; made during the entire traversal). If it fails then
;;; instantiate-formula needs to restore the proof log.


;;; Try instantiate a formula.  If successful then the resulting
;;; transformed formula is returned. Otherwise nil is returned.
;;;
;;; Note that here, the formula is fully quantified (there are no
;;; free variables in it).
;;; vars is the list of variables to be instantiated
;;; subst-list is the substitution list that represents the instantiations

(defun instantiate-formula (vars subst-list formula bool-p index)
  (let ((bound-in-formula (unique (list-of-bound-variables formula)))
	(free-in-replacement
	 (unique (list-of-free-variables (mapcar #'cdr subst-list)))))
    (when (and (subset-p vars bound-in-formula)
               (subset-p free-in-replacement bound-in-formula))
        (unless (intersection-eq vars free-in-replacement)
          (let ((instantiated-formula
                 (instantiate-recursively
                  vars subst-list formula free-in-replacement bool-p index)))
            instantiated-formula)))))

;;; The main dispatcher for instantiating a formula.
;;; Each of the variables in vars and out-of-scope-vars occurs in the
;;; formula.  This is true for all the routines here.
;;; Need to be inside the scope of out-of-scope-vars.
;;; Either go inside or move the quantification out.

(defun instantiate-recursively (vars subst-list formula
				     out-of-scope-vars bool-p index)
  (cond ((or (all-p formula) (some-p formula))
	 ;; either we hit a quantification to be instantiated
	 ;; or we dive inside
	 (instantiate-quantification
	  vars subst-list formula out-of-scope-vars bool-p index))
	((if-p formula)
	 ;; generally we may need to move quantifications out
	 (instantiate-if
	  vars subst-list formula out-of-scope-vars bool-p index))
	(t (instantiate-term
	    vars subst-list formula out-of-scope-vars index))))

;;; Traversal hits a term that is neither a quantification nor
;;; an IF expression.  Need to try the subterms.
;;; instantiate-term and instantiate-term-list don't need
;;; to be passed bool-p since it is always nil.

(defun instantiate-term (vars subst-list term out-of-scope-vars index)
  (when (consp term)
    (instantiate-term-list
     vars subst-list term out-of-scope-vars (cons 0 index))))



;;; Traverse the arguments of a term.
;;; Rather weak but probably doesn't matter.

(defun instantiate-term-list
          (vars subst-list term-list out-of-scope-vars index)
  (cond ((null term-list) nil)
	((subset-p (append vars out-of-scope-vars)
		   (list-of-bound-variables (first term-list)))
	 (let ((result (instantiate-recursively
			vars subst-list (first term-list)
			out-of-scope-vars nil index)))
	   (when result (cons result (cdr term-list)))))
	(t (let ((result (instantiate-term-list
			  vars subst-list (cdr term-list)
			  out-of-scope-vars
			  (cons (+ 1 (car index)) (cdr index)))))
	     (when result (cons (car term-list) result))))))

;;; Traversal hits a quantification.  If it quantifies one of the
;;; variables to be instantiated, call instantiate-quantification-aux,
;;; to try to instantiate the quantification, and there will be no more
;;; traversal. Otherwise dive into the quantified expression (checking
;;; off an out of scope variable if it is the variable being quantified).

(defun instantiate-quantification
    (vars subst-list formula out-of-scope-vars bool-p index)
  (let ((var (if (all-p formula) (all-var formula) (some-var formula)))
	(expr (if (all-p formula) (all-expr formula) (some-expr formula)))
	(kind (if (all-p formula) 'all 'some)))
    (cond
     ((member-eq var vars)
      ;; Hit a quantification to be instantiated
      ;; Note that if the call fails, the proof log needs to be
      ;; restored somewhere up the call chain.
      (instantiate-quantification-aux
       vars subst-list formula out-of-scope-vars kind bool-p index))
     (t (let ((result (instantiate-recursively
		       vars subst-list expr
		       (remove-eq var out-of-scope-vars)
		       (make-context-for-bool-p formula index)
		       (all-expr-index))))
	  (when result
	    ;; Successful instantiation inside the quantification.
	    ;; Simply quantify the result.
	    (if (all-p formula)
		(make-all-single var result)
	      (make-some-single var result))))))))



;;; We've reached a quantification that needs to be instantiated.  Bring
;;; out the quantifications on vars and out-of-scope-vars (call the
;;; "move-quantifiers-out" routine).  The quantifiers must be of the
;;; same kind outside (i.e., they must be all universal or all
;;; existential) and the order of quantification may be flipped so that
;;; the quantifications on out-of-scope-vars are outside the
;;; quantifications on vars.  Only then can the instantiations be made.

(defun instantiate-quantification-aux
    (vars subst-list formula out-of-scope-vars kind bool-p index)
  (let ((result (move-quantifiers-out
		 vars out-of-scope-vars formula kind bool-p index)))
    (when result
      ;; For example if the quantification is universal, we have:
      ;; (all (outv1)..(all (outvi) (all (v1) (all (v2)..(all (vj) expr)))))
      ;; as result.
      ;; We must instantiate at
      ;; (all (v1) (all (v2)..(all (vj) expr)))
      ;; The case for existential quantification is similar.
      (instantiate-result
       vars subst-list result out-of-scope-vars kind bool-p index))))

;;; Definitely can perform instantiation. Just need to dive through
;;; the quantification of all out of scope variables at the surface.

(defun instantiate-result (vars subst-list formula out-vars kind bool-p index)
  (cond ((null out-vars)
	 (cond ((eq kind 'all)
		(instantiate-universal
		 vars subst-list formula bool-p index))
	       (t
		(instantiate-existential
		 vars subst-list formula bool-p index))))
	(t (list (car formula) (second formula)
		 (instantiate-result
		  vars subst-list (third formula) (cdr out-vars) kind
		  (make-context-for-bool-p
		   (list (car formula) (second formula) *true*) index)
		  (all-expr-index))))))

;;; Definitely instantiate a universal quantification.
;;; Recursively instantiate the quantifications.

(defun instantiate-universal (vars subst-list formula bool-p index)
  (cond ((null vars) formula)
	(t
	 (let* ((var (all-var formula))
		(value (cdr (assoc-eq var subst-list))))
	   (let* ((instantiated (subst-eq value var (all-expr formula)))
		  (form (make-if instantiated formula *false*)))
	     (push-proof-log 'instantiate-universal index
			     (make-= var value))
	     ;; (if instantiated original (false))
	     (let ((result (instantiate-universal
			    (remove-eq var vars) subst-list instantiated
			    (make-context-for-bool-p form index)
			    (if-test-index))))
	       (cond ((cdr vars)
		      ;; (if (if full-inst part-inst (false))
		      ;;     original
		      ;;     (false))
		      (push-proof-log 'case-analysis index 1)
		      ;; (if full-inst
		      ;;     (if part-inst original (false))
		      ;;     (if (false) original (false)))
		      (push-proof-log 'instantiate-universal
				      (if-left-index)
				      (make-= var value) t)
		      (push-proof-log 'if-false (if-right-index))
		      ;; (if full-inst original (false))
		      (make-if (if-test result) formula *false*))
		     (t (make-if result formula *false*)))))))))

;;; Definitely instantiate an existential quantification.

(defun instantiate-existential (vars subst-list formula bool-p index)
  (cond ((null vars) formula)
	(t
	 (let* ((var (some-var formula))
		(value (cdr (assoc-eq var subst-list))))
	   (let* ((instantiated (subst-eq value var (some-expr formula)))
		  (form (make-if instantiated *true* formula)))
	     (log-instantiate-existential (make-= var value) index)
	     ;; (if instantiated (true) original)
	     (let ((result (instantiate-existential
			    (remove-eq var vars) subst-list instantiated
			    (make-context-for-bool-p form index)
			    (if-test-index))))
	       (cond ((cdr vars)
		      ;; (if (if full-inst (true) part-inst)
		      ;;     (true)
		      ;;     original)
		      (push-proof-log 'case-analysis index 1)
		      ;; (if full-inst
		      ;;     (if (true) (true) original)
		      ;;     (if part-inst (true) original))
		      (log-uninstantiate-existential
		       (make-= var value) (if-right-index))
		      (push-proof-log 'if-true (if-left-index))
		      ;; (if full-inst (true) original)
		      (make-if (if-test result) *true* formula))
		     (t (make-if result *true* formula)))))))))




;;; Traversal hits an IF expression.

(defun instantiate-if (vars subst-list form out-of-scope-vars bool-p index)
  (let ((test (if-test form))
	(left (if-left form))
	(right (if-right form)))
    (let ((bound-test (unique (list-of-bound-variables test)))
	  (bound-left (unique (list-of-bound-variables left)))
	  (bound-right (unique (list-of-bound-variables right))))
      (let ((out-vars-test (intersection-eq bound-test out-of-scope-vars))
	    (out-vars-left (intersection-eq bound-left out-of-scope-vars))
	    (out-vars-right (intersection-eq bound-right out-of-scope-vars)))
	(cond ((or (intersection-eq out-vars-test out-vars-left)
		   (intersection-eq out-vars-test out-vars-right)
		   (intersection-eq out-vars-left out-vars-right))
	       ;; We cannot handle an out of scope variable bound in more
	       ;; than one of test, left, right.
	       nil)
	      ((subset-p vars bound-test)
	       ;; All of to be instantiated variables are bound in test.
	       ;; Commit to trying to instantiate the test branch.
	       (let ((result1 (move-out-vars
			       out-vars-left left bool-p (if-left-index)))
		     (result2 (move-out-vars
			       out-vars-right right bool-p (if-right-index))))
		 (when (and result1 result2)
		   (instantiate-if-test
		    vars subst-list test result1 result2 out-vars-test
		    out-vars-left out-vars-right bool-p index))))
	      ((and out-vars-test (not (true-p left)) (not (false-p left))
		    (not (true-p right)) (not (false-p right)))
	       ;; We cannot handle the case where there are out of scope
	       ;; variables bound in test and the IF formula is not
	       ;; one where one of left or right is either (true) or (false)
	       nil)
	      ((subset-p vars bound-left)
	       ;; All of to be instantiated variables are bound in left.
	       ;; Commit to trying to instantiate the left branch.
	       ;; We must must first move out quantifications on out
	       ;; of scope variables bound in test and those bound in
	       ;; right (but not bound in both!)
	       (let ((result1 (move-out-vars
			       out-vars-test test
			       (make-context-for-bool-p form index)
			       (if-test-index)))
		     (result2 (move-out-vars
			       out-vars-right right bool-p (if-right-index))))
		 (when (and result1 result2)
		   (instantiate-if-left
		    vars subst-list result1 left result2 out-vars-test
		    out-vars-left out-vars-right bool-p index))))
	      ((subset-p vars bound-right)
	       ;; All of to be instantiated variables are bound in right
	       ;; Commit to trying to instantiate the right branch.
	       ;; We must must first move out quantifications on out
	       ;; of scope variables bound in test and those bound in
	       ;; left (but not bound in both!).
	       (let ((result1 (move-out-vars
			       out-vars-test test
			       (make-context-for-bool-p form index)
			       (if-test-index)))
		     (result2 (move-out-vars
			       out-vars-left left bool-p (if-left-index))))
		 (when (and result1 result2)
		   (instantiate-if-right
		    vars subst-list result1 result2 right out-vars-test
		    out-vars-left out-vars-right bool-p index))))
	      (out-of-scope-vars
	       ;; We still don't know where the to be instantiated
	       ;; variables are bound. Move out the quantifications on
	       ;; out of scope variables first.
	       (let ((result (move-out-vars
			      out-of-scope-vars form bool-p index)))
		 (when result
		   (instantiate-recursively
		    vars subst-list result out-of-scope-vars bool-p index))))
	      (vars
	       ;; There are no more out of scope variables and vars are
	       ;; not all bound in one branch. Move out the quantifications
	       ;; on vars first and then do the main recursion and we hit
	       ;; the jackpot.
	       (let ((result (move-out-vars vars form bool-p index)))
		 (when result
		   (instantiate-recursively
		    vars subst-list result nil bool-p index)))))))))



;;; Try instantiate the test of an if expression.  Must first move out
;;; out-of-scope quantifiers from the left and right branches.

(defun instantiate-if-test (vars subst-list test left right
				 out-vars-test out-vars-left out-vars-right
				 bool-p index)
  (cond (out-vars-left
	 ;; some out of scope variables quantified in the left branch
	 (cond ((all-p left)
		(when (and (member-eq (all-var left) out-vars-left)
			   (or (bool-p right) bool-p))
		  (log-all-out-left (make-if test left right) bool-p index)
		  (let ((result (instantiate-if-test
				 vars subst-list test (all-expr left)
				 right out-vars-test
				 (remove-eq (all-var left) out-vars-left)
				 out-vars-right
				 (make-context-for-bool-p
				  (make-all (all-vars left) *true*) index)
				 (all-expr-index))))
		    (when result (make-all (all-vars left) result)))))
	       ((some-p left)
		(when (and (member-eq (some-var left) out-vars-left)
			   (or (bool-p right) bool-p))
		  (log-some-out-left (make-if test left right) bool-p index)
		  (let ((result (instantiate-if-test
				 vars subst-list test (some-expr left)
				 right out-vars-test
				 (remove-eq (some-var left) out-vars-left)
				 out-vars-right
				 (make-context-for-bool-p
				  (make-some (some-vars left) *true*) index)
				 (some-expr-index))))
		    (when result (make-some (some-vars left) result)))))))
	(out-vars-right
	 ;; some out of scope variables quantified in the right branch
	 (cond ((all-p right)
		(when (and (member-eq (all-var right) out-vars-right)
			   (or (bool-p left) bool-p))
		  (log-all-out-right (make-if test left right) bool-p index)
		  (let ((result (instantiate-if-test
				 vars subst-list test left
				 (all-expr right) out-vars-test out-vars-left
				 (remove-eq (all-var right) out-vars-right)
				 (make-context-for-bool-p
				  (make-all (all-vars right) *true*) index)
				 (all-expr-index))))
		    (when result (make-all (all-vars right) result)))))
	       ((some-p right)
		(when (and (member-eq (some-var right) out-vars-right)
			   (or (bool-p left) bool-p))
		  (log-some-out-right (make-if test left right) bool-p index)
		  (let ((result (instantiate-if-test
				 vars subst-list test left
				 (some-expr right) out-vars-test out-vars-left
				 (remove-eq (some-var right) out-vars-right)
				 (make-context-for-bool-p
				  (make-some (some-vars right) *true*) index)
				 (some-expr-index))))
		    (when result (make-some (some-vars right) result)))))))
	(t
	 ;; No more out of scope vars bound in left and right.
	 (let ((result (instantiate-recursively
			  vars subst-list test out-vars-test
			  (make-context-for-bool-p
			   (make-if test left right) index)
			  (if-test-index))))
	   (when result (make-if result left right))))))



;;; Try instantiate the left branch of an if expression.  Must first move
;;; out quantifications on out-of-scope variables from the test and the
;;; right branch.

(defun instantiate-if-left (vars subst-list test left right
				 out-vars-test out-vars-left out-vars-right
				 bool-p index)
  (cond
   (out-vars-test
    ;; some out of scope variables bound in the test branch
    (cond
     ((and (not (true-p right)) (not (false-p right))) nil)
     ((all-p test)
      (when (and (member-eq (all-var test) out-vars-test)
		 (or (bool-p left) bool-p))
	(cond ((true-p right)
	       ;; (if (all (v) texpr) left (true))
	       (log-coerce-expr-for-boolean-or-bool-p
		left (if-left-index) bool-p)
	       (log-introduce-existential (all-vars test) (if-left-index))
	       (log-some-uncase-analysis-4 index)
	       ;; (some (v) (if texpr left (true)))
	       )
	       (t
	       ;; (if (all (v) texpr) left (false))
		(log-coerce-expr-for-boolean-or-bool-p
		 left (if-left-index) bool-p)
	       (push-proof-log 'remove-universal (if-left-index)
			       (all-vars test) t)
	       (push-proof-log 'all-case-analysis index t)
	       ;; (all (v) (if texpr left (false)))
	       ))
	(let ((result (instantiate-if-left
		       vars subst-list (all-expr test) left right
		       (remove-eq (all-var test) out-vars-test)
		       out-vars-left out-vars-right
		       (make-context-for-bool-p
			(if (true-p right)
			    (make-some (all-vars test) *true*)
			  (make-all (all-vars test) *true*))
			index)
		       (all-expr-index))))
	  (when result
	    (if (true-p right)
		(make-some (all-vars test) result)
	      (make-all (all-vars test) result))))))
     ((some-p test)
      (when (and (member-eq (some-var test) out-vars-test)
		 (or (bool-p left) bool-p))
	(cond ((true-p right)
	       ;; (if (some (v) texpr) left (true))
	       (log-coerce-expr-for-boolean-or-bool-p
		left (if-left-index) bool-p)
	       (log-all-uncase-analysis-2
		(make-if test (make-if left *true* *false*) *true*) index)
	       ;; (all (v) (if texpr left (true)))
	       )
	      (t
	       ;; (if (some (v) texpr) left (false))
	       (log-coerce-expr-for-boolean-or-bool-p
		left (if-left-index) bool-p)
	       (log-some-uncase-analysis-2
		(make-if test (make-if left *true* *false*) *false*) index)
	       ;; (some (v) (if texpr left (false)))
	       ))
	(let ((result (instantiate-if-left
		       vars subst-list (some-expr test) left right
		       (remove-eq (some-var test) out-vars-test)
		       out-vars-left out-vars-right
		       (make-context-for-bool-p
			(if (true-p right)
			    (make-all (some-vars test) *true*)
			  (make-some (some-vars test) *true*))
			index)
		       (all-expr-index))))
	  (when result
	    (if (true-p right)
		(make-all (some-vars test) result)
	      (make-some (some-vars test) result))))))))
   (out-vars-right
    ;; some out of scope variables bound in the right branch
    (cond ((all-p right)
	   (when (and (member-eq (all-var right) out-vars-right)
		      (or (bool-p left) bool-p))
	     (log-all-out-right (make-if test left right) bool-p index)
	     (let ((result (instantiate-if-left
			    vars subst-list test left (all-expr right)
			    out-vars-test out-vars-left
			    (remove-eq (all-var right) out-vars-right)
			    (make-context-for-bool-p
			     (make-all (all-vars right) *true*)
			     index)
			    (all-expr-index))))
	       (when result (make-all (all-vars right) result)))))
	  ((some-p right)
	   (when (and (member-eq (some-var right) out-vars-right)
		      (or (bool-p left) bool-p))
	     (log-some-out-right (make-if test left right) bool-p index)
	     (let ((result (instantiate-if-left
			    vars subst-list test left (some-expr right)
			    out-vars-test out-vars-left
			    (remove-eq (some-var right) out-vars-right)
			    (make-context-for-bool-p
			     (make-some (some-vars right) *true*)
			     index)
			    (some-expr-index))))
	       (when result (make-some (some-vars right) result)))))))
   (t
    ;; No more out of scope vars bound in the test and right.
    (let ((result (instantiate-recursively
		   vars subst-list left out-vars-left bool-p
		   (if-left-index))))
      (when result (make-if test result right))))))



;;; Try instantiate the right branch of an if expression.  Must first move
;;; out quantifications on out-of-scope variables from the test and the
;;; left branch.

(defun instantiate-if-right (vars subst-list test left right
				  out-vars-test out-vars-left out-vars-right
				  bool-p index)
  (cond
   (out-vars-test
    ;; some out of scope variables bound in the test branch
    (cond
     ((and (not (true-p left)) (not (false-p left))) nil)
     ((all-p test)
      (when (and (member-eq (all-var test) out-vars-test)
		 (or (bool-p right) bool-p))
	(cond ((true-p left)
	       ;; (if (all (v) texpr) (true) right)
	       (log-coerce-expr-for-boolean-or-bool-p
		left (if-right-index) bool-p)
	       (log-all-uncase-analysis-3
		(make-if test left (make-if right *true* *false*)) index)
	       ;; (all (v) (if texpr (true) right))
	       )
	      (t
	       ;; (if (all (v) texpr) (false) right)
	       (log-coerce-expr-for-boolean-or-bool-p
		left (if-right-index) bool-p)
	       (log-some-uncase-analysis-3
		(make-if test left (make-if right *true* *false*)) index)
	       ;; (some (v) (if texpr (false) right))
	       ))
	(let ((result (instantiate-if-right
		       vars subst-list (all-expr test) left right
		       (remove-eq (all-var test) out-vars-test)
		       out-vars-left out-vars-right
		       (make-context-for-bool-p
			(if (false-p left)
			    (make-some (all-vars test) *true*)
			  (make-all (all-vars test) *true*))
			index)
		       (all-expr-index))))
	  (when result
	    (if (false-p left)
		(make-some (all-vars test) result)
	    (make-all (all-vars test) result))))))
     ((some-p test)
      (when (and (member-eq (some-var test) out-vars-test)
		 (or (bool-p right) bool-p))
	(cond ((true-p left)
	       ;; (if (some (v) texpr) (true) right)
	       (log-coerce-expr-for-boolean-or-bool-p
		left (if-right-index) bool-p)
	       (log-introduce-existential (some-vars test) (if-right-index))
	       (log-some-uncase-analysis-5
		(make-if test left (make-if right *true* *false*)) index)
	       ;; (some (v) (if texpr (true) right))
	       )
	      (t
	       ;; (if (some (v) texpr) (false) right)
	       (log-coerce-expr-for-boolean-or-bool-p
		left (if-right-index) bool-p)
	       (push-proof-log 'remove-universal (if-right-index)
			       (some-vars test) t)
	       (log-all-uncase-analysis-5
		(make-if test left (make-all (some-vars test) right)) index)
	       ;; (all (v) (if texpr (false) right))
	       ))
	(let ((result (instantiate-if-right
		       vars subst-list (some-expr test) left right
		       (remove-eq (some-var test) out-vars-test)
		       out-vars-left out-vars-right
		       (make-context-for-bool-p
			(if (false-p left)
			    (make-all (some-vars test) *true*)
			  (make-some (some-vars test) *true*))
			index)
		       (all-expr-index))))
	  (when result
	    (if (false-p left)
		(make-all (some-vars test) result)
	    (make-some (some-vars test) result))))))))
   (out-vars-left
    ;; some out of scope variables bound in the left branch
    (cond ((all-p left)
	   (when (and (member-eq (all-var left) out-vars-left)
		      (or (bool-p right) bool-p))
	     (log-all-out-left (make-if test left right) bool-p index)
	     (let ((result (instantiate-if-right
			    vars subst-list test (all-expr left) right
			    out-vars-test
			    (remove-eq (all-var left) out-vars-left)
			    out-vars-right
			    (make-context-for-bool-p
			     (make-all (all-vars left) *true*)
			     index)
			    (all-expr-index))))
	       (when result (make-all (all-vars left) result)))))
	  ((some-p left)
	   (when (and (member-eq (some-var left) out-vars-left)
		      (or (bool-p right) bool-p))
	     (log-some-out-left (make-if test left right) bool-p index)
	     (let ((result (instantiate-if-right
			    vars subst-list test (some-expr left) right
			    out-vars-test
			    (remove-eq (some-var left)  out-vars-left)
			    out-vars-right
			    (make-context-for-bool-p
			     (make-some (some-vars left) *true*)
			     index)
			    (some-expr-index))))
	       (when result (make-some (some-vars left) result)))))))
   (t
    ;; No more out of scope vars bound in test and left.
    (let ((result (instantiate-recursively
		   vars subst-list right out-vars-right
		   bool-p (if-right-index))))
      (when result (make-if test left result))))))



;;; The second group of routines try to move out the quantifications on
;;; vars and out-vars.  They are successful if the quantifications can
;;; be moved out to become the same kind outside.

(defun move-quantifiers-out (vars out-vars formula kind bool-p index)
  (if (and (null vars) (null out-vars))
      formula
      (cond
	((if-p formula)
	 (move-quantifiers-out-of-if vars out-vars formula kind bool-p index))
	((all-p formula)
	 (when (eq kind 'all)
	   (move-quantifiers-out-of-all vars out-vars formula index)))
	((some-p formula)
	 (when (eq kind 'some)
	   (move-quantifiers-out-of-some vars out-vars formula index))))))

(defun move-quantifiers-out-of-all (vars out-vars formula index)
  (let ((var (all-var formula))
	(expr (all-expr formula)))
    (cond ((member-eq var vars)
	   (let ((result (move-quantifiers-out
			  (remove-eq var vars) out-vars expr 'all
			  (make-context-for-bool-p formula index)
			  (all-expr-index))))
	     (when result
	       (push-in-all-var var (length out-vars) result index))))
	  ((member-eq var out-vars)
	   (let ((result (move-quantifiers-out
			  vars (remove-eq var out-vars) expr 'all
			  (make-context-for-bool-p formula index)
			  (all-expr-index))))
	     (when result
	       (make-all-single var result))))
	  (t (let ((result (move-quantifiers-out
			    vars out-vars expr 'all
			    (make-context-for-bool-p formula index)
			    (all-expr-index))))
	       (when result
		 (push-in-all-var var (+ (length vars) (length out-vars))
				  result index)))))))

(defun move-quantifiers-out-of-some (vars out-vars formula index)
  (let ((var (some-var formula))
	(expr (some-expr formula)))
    (cond ((member-eq var vars)
	   (let ((result (move-quantifiers-out
			  (remove-eq var vars) out-vars expr 'some
			  (make-context-for-bool-p formula index)
			  (some-expr-index))))
	     (when result
	       (push-in-some-var var (length out-vars) result index))))
	  ((member-eq var out-vars)
	   (let ((result (move-quantifiers-out
			  vars (remove-eq var out-vars) expr 'some
			  (make-context-for-bool-p formula index)
			  (some-expr-index))))
	     (when result
	       (make-some-single var result))))
	  (t (let ((result (move-quantifiers-out
			    vars out-vars expr 'some
			    (make-context-for-bool-p formula index)
			    (some-expr-index))))
	       (when result
		 (push-in-some-var var (+ (length vars) (length out-vars))
				  result index)))))))

(defun push-in-all-var (var n formula index)
  (cond ((> n 0)
	 (cond ((all-p formula)
		(push-proof-log 'flip-universals index)
		(let ((result
		       (push-in-all-var
			var (- n 1) (all-expr formula) (all-expr-index))))
		  (when result
		    (make-all (all-vars formula) result))))
	       (t
		;; Something wrong if you get here
		nil)))
	(t (make-all-single var formula))))

(defun push-in-some-var (var n formula index)
  (cond ((> n 0)
	 (cond ((some-p formula)
		(log-flip-existentials index)
		(let ((result
		       (push-in-some-var
			var (- n 1) (some-expr formula) (some-expr-index))))
		  (when result
		    (make-some (some-vars formula) result))))
	       (t
		;; Something wrong if you get here
		nil)))
	(t (make-some-single var formula))))



(defun move-quantifiers-out-of-if (vars out-vars formula kind bool-p index)
  (let ((test (if-test formula))
	(left (if-left formula))
	(right (if-right formula)))
    (cond
      ((and (true-p left) (or (bool-p right) bool-p))
       (move-quantifiers-out-of-or
	vars out-vars test right kind bool-p index))
      ((and (false-p left) (or (bool-p right) bool-p))
       (move-quantifiers-out-of-and-not
	vars out-vars test right kind bool-p index))
      ((and (true-p right) (or (bool-p left) bool-p))
       (move-quantifiers-out-of-implies
	vars out-vars test left kind bool-p index))
      ((and (false-p right) (or (bool-p left) bool-p))
       (move-quantifiers-out-of-and
	vars out-vars test left kind bool-p index))
      (t (move-quantifiers-out-of-if-aux
	  vars out-vars test left right kind bool-p index)))))

(defun move-quantifiers-out-of-if-aux
        (vars out-vars test left right kind bool-p index)
  (let ((bound-test (unique (list-of-bound-variables test)))
	(bound-left (unique (list-of-bound-variables left)))
	(bound-right (unique (list-of-free-variables right))))
    (unless (or (intersection-eq bound-test vars)
		(intersection-eq bound-test out-vars))
      (let ((vars-left (intersection-eq vars bound-left))
	    (vars-right (intersection-eq vars bound-right))
	    (out-vars-left (intersection-eq out-vars bound-left))
	    (out-vars-right (intersection-eq out-vars bound-right)))
	(unless (or (intersection-eq vars-left vars-right)
		    (intersection-eq out-vars-left out-vars-right))
	  (let ((result1 (move-quantifiers-out
			  vars-left out-vars-left left kind bool-p
			  (if-left-index))))
	    (when result1
	      (let ((result2 (move-quantifiers-out
			      vars-right out-vars-right right kind bool-p
			      (if-right-index))))
		(when result2
		  ;; (if test (all (v) ...) (all (v) ...)) or
		  ;; (if test (some (v) ...) (some (v) ...))
		  (pull-quantifiers-out-of-left-right
		   vars-left out-vars-left vars-right out-vars-right
		   test result1 result2 kind index bool-p))))))))))

(defun pull-quantifiers-out-of-left-right
    (vars-left out-vars-left vars-right out-vars-right test left right kind
	       index bool-p)
  (cond (out-vars-left
	 (log-coerce-expr-for-boolean-or-bool-p right (if-right-index) bool-p)
	 (cond ((eq kind 'all)
		(push-proof-log 'remove-universal (if-right-index)
				(all-vars left) t)
		(log-all-uncase-analysis-1
		 (make-if test left (make-all (all-vars left) right)) index)
		(let ((result (pull-quantifiers-out-of-left-right
			       vars-left (cdr out-vars-left) vars-right
			       out-vars-right test (all-expr left)
			       right 'all (all-expr-index)
			       (make-context-for-bool-p
				(make-all (all-vars left) *true*) index))))
		  (when result
		    (make-all (all-vars left) result))))
	       (t
		(log-introduce-existential (some-vars left) (if-right-index))
		(log-some-uncase-analysis-1
		 (make-if test left (make-some (some-vars left) right)) index)
		(let ((result (pull-quantifiers-out-of-left-right
			       vars-left (cdr out-vars-left) vars-right
			       out-vars-right test (some-expr left)
			       right 'some (some-expr-index)
			       (make-context-for-bool-p
				(make-some (some-vars left) *true*) index))))
		  (when result
		    (make-some (some-vars left) result))))))
	(out-vars-right
	 (log-coerce-expr-for-boolean-or-bool-p left (if-left-index) bool-p)
	 (cond ((eq kind 'all)
		(push-proof-log 'remove-universal (if-left-index)
				(all-vars right) t)
		(log-all-uncase-analysis-1
		 (make-if test (make-all (all-vars right) left) right) index)
		(let ((result (pull-quantifiers-out-of-left-right
			       vars-left out-vars-left vars-right
			       (cdr out-vars-right) test left
			       (all-expr right) 'all (all-expr-index)
			       (make-context-for-bool-p
				(make-all (all-vars right) *true*) index))))
		  (when result
		    (make-all (all-vars right) result))))
	       (t
		(log-introduce-existential (some-vars right) (if-left-index))
		(log-some-uncase-analysis-1
		 (make-if test (make-some (some-vars right) left) right) index)
		(let ((result (pull-quantifiers-out-of-left-right
			       vars-left out-vars-left vars-right
			       (cdr out-vars-right) test left
			       (some-expr right) 'some (some-expr-index)
			       (make-context-for-bool-p
				(make-some (some-vars right) *true*) index))))
		  (when result
		    (make-some (some-vars right) result))))))
	(vars-left
	 (log-coerce-expr-for-boolean-or-bool-p right (if-right-index) bool-p)
	 (cond ((eq kind 'all)
		(push-proof-log 'remove-universal (if-right-index)
				(all-vars left) t)
		(log-all-uncase-analysis-1
		 (make-if test left (make-all (all-vars left) right)) index)
		(let ((result (pull-quantifiers-out-of-left-right
			       (cdr vars-left) out-vars-left vars-right
			       out-vars-right test (all-expr left)
			       right 'all (all-expr-index)
			       (make-context-for-bool-p
				(make-all (all-vars left) *true*) index))))
		  (when result
		    (make-all (all-vars left) result))))
	       (t
		(log-introduce-existential (some-vars left) (if-right-index))
		(log-some-uncase-analysis-1
		 (make-if test left (make-some (some-vars left) right)) index)
		(let ((result (pull-quantifiers-out-of-left-right
			       (cdr vars-left) out-vars-left vars-right
			       out-vars-right test (some-expr left)
			       right 'some (some-expr-index)
			       (make-context-for-bool-p
				(make-some (some-vars left) *true*) index))))
		  (when result
		    (make-some (some-vars left) result))))))
	(vars-right
	 (log-coerce-expr-for-boolean-or-bool-p left (if-left-index) bool-p)
	 (cond ((eq kind 'all)
		(push-proof-log 'remove-universal (if-left-index)
				(all-vars right) t)
		(log-all-uncase-analysis-1
		 (make-if test (make-all (all-vars right) left) right) index)
		(let ((result (pull-quantifiers-out-of-left-right
			       vars-left out-vars-left (cdr vars-right)
			       out-vars-right test left
			       (all-expr right) 'all (all-expr-index)
			       (make-context-for-bool-p
				(make-all (all-vars right) *true*) index))))
		  (when result
		    (make-all (all-vars right) result))))
	       (t
		(log-introduce-existential (some-vars right) (if-left-index))
		(log-some-uncase-analysis-1
		 (make-if test (make-some (some-vars right) left) right) index)
		(let ((result (pull-quantifiers-out-of-left-right
			       vars-left out-vars-left (cdr vars-right)
			       out-vars-right test left
			       (some-expr right) 'some (some-expr-index)
			       (make-context-for-bool-p
				(make-some (some-vars right) *true*) index))))
		  (when result
		    (make-some (some-vars right) result))))))
	(t (make-if test left right))))



(defun move-quantifiers-out-of-or (vars out-vars test right kind bool-p index)
  (let ((bound-test (unique (list-of-bound-variables test)))
	(bound-right (unique (list-of-bound-variables right))))
    (let ((vars-test (intersection-eq vars bound-test))
	  (vars-right (intersection-eq vars bound-right))
	  (out-vars-test (intersection-eq out-vars bound-test))
	  (out-vars-right (intersection-eq out-vars bound-right)))
      (unless (or (intersection-eq vars-test vars-right)
		  (intersection-eq out-vars-test out-vars-right))
	(let ((result1 (move-quantifiers-out
			vars-test out-vars-test test kind
			(make-context-for-bool-p
			 (make-if test *true* right) index)
			(if-test-index))))
	  (when result1
	    (let ((result2 (move-quantifiers-out
			    vars-right out-vars-right right kind bool-p
			    (if-right-index))))
	      (when result2
		(cond ((eq kind 'all)
		       (pull-universals-out-of-or
			vars-test out-vars-test vars-right out-vars-right
			result1 result2 bool-p index))
		      (t
		       (pull-existentials-out-of-or
			vars-test out-vars-test vars-right out-vars-right
			result1 result2 bool-p index)))))))))))

(defun pull-universals-out-of-or (vars-test out-vars-test vars-right
					    out-vars-right test right
					    bool-p index)
  (cond (out-vars-test
	 (log-coerce-expr-for-boolean-or-bool-p right (if-right-index) bool-p)
	 ;; (if (all () ...) (true) (if right (true) (false)))
	 (log-all-uncase-analysis-3
	  (make-if test *true* (make-if right *true* *false*)) index)
	 ;; (all () (if ... (true) right))
	 (let ((result (pull-universals-out-of-or
			vars-test (cdr out-vars-test) vars-right
			out-vars-right (all-expr test) right
			(make-context-for-bool-p
			 (make-all (all-vars test) *true*) index)
			(all-expr-index))))
	   (when result
	     (make-all (all-vars test) result))))
	(out-vars-right
	 ;; (if test (true) (all () ...))
	 (log-all-uncase-analysis-3a (make-if test *true* right) index)
	 ;; (all () (if ... (true) right))
	 (let ((result (pull-universals-out-of-or
			vars-test nil vars-right (cdr out-vars-right)
			test (all-expr right)
			(make-context-for-bool-p
			 (make-all (all-vars right) *true*) index)
			(all-expr-index))))
	   (when result
	     (make-all (all-vars right) result))))
	(vars-test
	 (log-coerce-expr-for-boolean-or-bool-p right (if-right-index) bool-p)
	 ;; (if (all () ...) (true) (if right (true) (false)))
	 (log-all-uncase-analysis-3
	  (make-if test *true* (make-if right *true* *false*)) index)
	 ;; (all () (if ... (true) right))
	 (let ((result (pull-universals-out-of-or
			(cdr vars-test) nil vars-right nil (all-expr test) right
			(make-context-for-bool-p
			 (make-all (all-vars test) *true*) index)
			(all-expr-index))))
	   (when result
	     (make-all (all-vars test) result))))
	(vars-right
	 ;; (if test (true) (all () ...))
	 (log-all-uncase-analysis-3a (make-if test *true* right) index)
	 ;; (all () (if ... (true) right))
	 (let ((result (pull-universals-out-of-or
			nil nil (cdr vars-right) nil test (all-expr right)
			(make-context-for-bool-p
			 (make-all (all-vars right) *true*) index)
			(all-expr-index))))
	   (when result
	     (make-all (all-vars right) result))))
	(t (make-if test *true* right))))

(defun pull-existentials-out-of-or
    (vars-test out-vars-test vars-right out-vars-right test right bool-p index)
  (cond (out-vars-test
	 ;; (if (some () ...) (true) right)
	 (log-coerce-expr-for-boolean-or-bool-p right (if-right-index) bool-p)
	 (log-introduce-existential (some-vars test) (if-right-index))
	 (log-some-uncase-analysis-5
	  (make-if test *true* (make-some (some-vars test) right)) index)
	 ;; (some () (if test (true) ...))
	 (let ((result (pull-existentials-out-of-or
			vars-test (cdr out-vars-test) vars-right out-vars-right
			(some-expr test) right
			(make-context-for-bool-p
			 (make-some (some-vars test) *true*) index)
			(some-expr-index))))
		  (when result
		    (make-some (some-vars test) result))))
	(out-vars-right
	 ;; (if test (true) (some () ...))
	 (log-coerce-expr-for-boolean-or-bool-p
	  test (if-test-index)
	  (make-context-for-bool-p (make-if test *true* right) index))
	 (log-introduce-existential (some-vars right) (if-test-index))
	 (log-some-uncase-analysis-5
	  (make-if (make-some (some-vars right) test) *true* right) index)
	 ;; (some () (if test (true) ...))
	 (let ((result (pull-existentials-out-of-or
			vars-test nil vars-right (cdr out-vars-right) test
			(some-expr right)
			(make-context-for-bool-p
			 (make-some (some-vars right) *true*) index)
			(some-expr-index))))
	   (when result
	     (make-some (some-vars right) result))))
	(vars-test
	 ;; (if (some () ...) (true) right)
	 (log-coerce-expr-for-boolean-or-bool-p right (if-right-index) bool-p)
	 (log-introduce-existential (some-vars test) (if-right-index))
	 (log-some-uncase-analysis-5
	  (make-if test *true* (make-some (some-vars test) right)) index)
	 ;; (some () (if test (true) ...))
	 (let ((result (pull-existentials-out-of-or
			(cdr vars-test) nil vars-right nil (some-expr test)
			right
			(make-context-for-bool-p
			 (make-some (some-vars test) *true*) index)
			(some-expr-index))))
		  (when result
		    (make-some (some-vars test) result))))
	(vars-right
	 ;; (if test (true) (some () ...))
	 (log-coerce-expr-for-boolean-or-bool-p
	  test (if-test-index)
	  (make-context-for-bool-p (make-if test *true* right) index))
	 (log-introduce-existential (some-vars right) (if-test-index))
	 (log-some-uncase-analysis-5
	  (make-if (make-some (some-vars right) test) *true* right) index)
	 ;; (some () (if test (true) ...))
	 (let ((result (pull-existentials-out-of-or
			nil nil (cdr vars-right) nil test (some-expr right)
			(make-context-for-bool-p
			 (make-some (some-vars right) *true*) index)
			(some-expr-index))))
	   (when result
	     (make-some (some-vars right) result))))
	(t (make-if test *true* right))))


(defun move-quantifiers-out-of-and (vars out-vars test left kind bool-p index)
  (let ((bound-test (unique (list-of-bound-variables test)))
	(bound-left (unique (list-of-bound-variables left))))
    (let ((vars-test (intersection-eq vars bound-test))
	  (vars-left (intersection-eq vars bound-left))
	  (out-vars-test (intersection-eq out-vars bound-test))
	  (out-vars-left (intersection-eq out-vars bound-left)))
      (unless (or (intersection-eq vars-test vars-left)
		  (intersection-eq out-vars-test out-vars-left))
	(let ((result1 (move-quantifiers-out
			vars-test out-vars-test test kind
			(make-context-for-bool-p
			 (make-if test left *false*) index)
			(if-test-index))))
	  (when result1
	    (let ((result2 (move-quantifiers-out
			    vars-left out-vars-left left kind bool-p
			    (if-left-index))))
	      (when result2
		(cond ((eq kind 'all)
		       (pull-universals-out-of-and
			vars-test out-vars-test vars-left out-vars-left
			result1 result2 bool-p index))
		      (t
		       (pull-existentials-out-of-and
			vars-test out-vars-test vars-left out-vars-left
			result1 result2 bool-p index)))))))))))


(defun pull-existentials-out-of-and
    (vars-test out-vars-test vars-left out-vars-left test left bool-p index)
  (cond (out-vars-test
	 (log-coerce-expr-for-boolean-or-bool-p left (if-left-index) bool-p)
	 ;; (if (some () ...) (if left (true) (false)) (false))
	 (log-some-uncase-analysis-2
	  (make-if test (make-if left *true* *false*) *false*) index)
	 ;; (some () (if ... left (false)))
	 (let ((result (pull-existentials-out-of-and
			vars-test (cdr out-vars-test) vars-left
			out-vars-left (some-expr test) left
			(make-context-for-bool-p
			 (make-some (some-vars test) *true*) index)
			(some-expr-index))))
	   (when result
	     (make-some (some-vars test) result))))
	(out-vars-left
	 ;; (if test (some () ...) (false))
	 (log-some-uncase-analysis-2a (make-if test left *false*) index)
	 ;; (some () (if ... left (false)))
	 (let ((result (pull-existentials-out-of-and
			vars-test nil vars-left (cdr out-vars-left)
			test (some-expr left)
			(make-context-for-bool-p
			 (make-some (some-vars left) *true*) index)
			(some-expr-index))))
	   (when result
	     (make-some (some-vars left) result))))
	(vars-test
	 (log-coerce-expr-for-boolean-or-bool-p left (if-left-index) bool-p)
	 ;; (if (some () ...) (if left (true) (false)) (false))
	 (log-some-uncase-analysis-2
	  (make-if test (make-if left *true* *false*) *false*) index)
	 ;; (some () (if ... left (false)))
	 (let ((result (pull-existentials-out-of-and
			(cdr vars-test) nil vars-left nil (some-expr test) left
			(make-context-for-bool-p
			 (make-some (some-vars test) *true*) index)
			(some-expr-index))))
	   (when result
	     (make-some (some-vars test) result))))
	(vars-left
	 ;; (if test (some () ...) (false))
	 (log-some-uncase-analysis-2a (make-if test left *false*) index)
	 ;; (some () (if ... left (false)))
	 (let ((result (pull-existentials-out-of-and
			nil nil (cdr vars-left) nil test (some-expr left)
			(make-context-for-bool-p
			 (make-some (some-vars left) *true*) index)
			(some-expr-index))))
	   (when result
	     (make-some (some-vars left) result))))
	(t (make-if test left *false*))))

(defun pull-universals-out-of-and
    (vars-test out-vars-test vars-left out-vars-left test left bool-p index)
  (cond (out-vars-test
	 ;; (if (all () ...) left (false))
	 (log-coerce-expr-for-boolean-or-bool-p left (if-left-index) bool-p)
	 (push-proof-log 'remove-universal (if-left-index) (all-vars test) t)
	 (push-proof-log 'all-case-analysis index t)
	 ;; (all () (if test ... (false)))
	 (let ((result (pull-universals-out-of-and
			vars-test (cdr out-vars-test) vars-left out-vars-left
			(all-expr test) left
			(make-context-for-bool-p
			 (make-all (all-vars test) *true*) index)
			(all-expr-index))))
	   (when result
	     (make-all (all-vars test) result))))
	(out-vars-left
	 ;; (if test (all () ...) (false))
	 (log-coerce-expr-for-boolean-or-bool-p
	  test (if-test-index)
	  (make-context-for-bool-p (make-if test left *false*) index))
	 (push-proof-log 'remove-universal (if-test-index) (all-vars left) t)
	 (push-proof-log 'all-case-analysis index t)
	 ;; (all () (if test ... (false)))
	 (let ((result (pull-universals-out-of-and
			vars-test nil vars-left (cdr out-vars-left)
			test (all-expr left)
			(make-context-for-bool-p
			 (make-all (all-vars left) *true*) index)
			(all-expr-index))))
	   (when result
	     (make-all (all-vars left) result))))
	(vars-test
	 ;; (if (all () ...) left (false))
	 (log-coerce-expr-for-boolean-or-bool-p left (if-left-index) bool-p)
	 (push-proof-log 'remove-universal (if-left-index) (all-vars test) t)
	 (push-proof-log 'all-case-analysis index t)
	 ;; (all () (if test ... (false)))
	 (let ((result (pull-universals-out-of-and
			(cdr vars-test) nil vars-left nil (all-expr test) left
			(make-context-for-bool-p
			 (make-all (all-vars test) *true*) index)
			(all-expr-index))))
	   (when result
	     (make-all (all-vars test) result))))
	(vars-left
	 ;; (if test (all () ...) (false))
	 (log-coerce-expr-for-boolean-or-bool-p
	  test (if-test-index)
	  (make-context-for-bool-p (make-if test left *false*) index))
	 (push-proof-log 'remove-universal (if-test-index) (all-vars left) t)
	 (push-proof-log 'all-case-analysis index t)
	 ;; (all () (if test ... (false)))
	 (let ((result (pull-universals-out-of-and
			nil nil (cdr vars-left) nil test (all-expr left)
			(make-context-for-bool-p
			 (make-all (all-vars left) *true*) index)
			(all-expr-index))))
	   (when result
	     (make-all (all-vars left) result))))
	(t (make-if test left *false*))))




(defun move-quantifiers-out-of-implies
    (vars out-vars test left kind bool-p index)
  (let ((bound-test (unique (list-of-bound-variables test)))
	(bound-left (unique (list-of-bound-variables left))))
    (let ((vars-test (intersection-eq vars bound-test))
	  (vars-left (intersection-eq vars bound-left))
	  (out-vars-test (intersection-eq out-vars bound-test))
	  (out-vars-left (intersection-eq out-vars bound-left)))
      (unless (or (intersection-eq vars-test vars-left)
		  (intersection-eq out-vars-test out-vars-left))
	(let ((result1 (move-quantifiers-out
			vars-test out-vars-test test
			(if (eq kind 'all) 'some 'all)
			(make-context-for-bool-p
			 (make-if test left *true*) index)
			(if-test-index))))
	  (when result1
	    (let ((result2 (move-quantifiers-out
			    vars-left out-vars-left left kind bool-p
			    (if-left-index))))
	      (when result2
		(cond ((eq kind 'all)
		       (pull-universals-out-of-implies
			vars-test out-vars-test vars-left out-vars-left
			result1 result2 bool-p index))
		      (t
		       (pull-existentials-out-of-implies
			vars-test out-vars-test vars-left out-vars-left
			result1 result2 bool-p index)))))))))))

(defun pull-universals-out-of-implies
    (vars-test out-vars-test vars-left out-vars-left test left bool-p index)
  (cond (out-vars-test
	 (log-coerce-expr-for-boolean-or-bool-p left (if-left-index) bool-p)
	 ;; (if (some () ...) (if left (true) (false)) (true))
	 (log-all-uncase-analysis-2
	  (make-if test (make-if left *true* *false*) *true*) index)
	 ;; (all () (if ... left (true)))
	 (let ((result (pull-universals-out-of-implies
			vars-test (cdr out-vars-test) vars-left out-vars-left
			(all-expr test) left
			(make-context-for-bool-p
			 (make-all (some-vars test) *true*) index)
			(all-expr-index))))
	   (when result
	     (make-all (some-vars test) result))))
	(out-vars-left
	 ;; (if test (all () ...) (true))
	 (log-all-uncase-analysis-2a (make-if test left *true*) index)
	 ;; (all () (if test ... (true)))
	 (let ((result (pull-universals-out-of-implies
			vars-test nil vars-left (cdr out-vars-left)
			test (all-expr left) bool-p (all-expr-index))))
	   (when result
	     (make-all (all-vars left) result))))
	(vars-test
	 (log-coerce-expr-for-boolean-or-bool-p left (if-left-index) bool-p)
	 ;; (if (some () ...) (if left (true) (false)) (true))
	 (log-all-uncase-analysis-2
	  (make-if test (make-if left *true* *false*) *true*) index)
	 ;; (all () (if ... left (true)))
	 (let ((result (pull-universals-out-of-implies
			(cdr vars-test) nil vars-left nil (all-expr test) left
			(make-context-for-bool-p
			 (make-all (some-vars test) *true*) index)
			(all-expr-index))))
	   (when result
	     (make-all (some-vars test) result))))
	(vars-left
	 ;; (if test (all () ...) (true))
	 (log-all-uncase-analysis-2a (make-if test left *true*) index)
	 ;; (all () (if test ... (true)))
	 (let ((result (pull-universals-out-of-implies
			nil nil (cdr vars-left) nil test (all-expr left)
			bool-p (all-expr-index))))
	   (when result
	     (make-all (all-vars left) result))))
	(t (make-if test left *true*))))


(defun pull-existentials-out-of-implies
    (vars-test out-vars-test vars-left out-vars-left test left bool-p index)
  (cond (out-vars-test
	 ;; (if (all () ...) left (true))
	 (log-coerce-expr-for-boolean-or-bool-p
	  left (if-left-index) bool-p)
	 (log-introduce-existential (all-vars test) (if-left-index))
	 (log-some-uncase-analysis-4 index)
	 ;; (some () (if ... left (true)))
	 (let ((result (pull-existentials-out-of-implies
			vars-test (cdr out-vars-test) vars-left out-vars-left
			(some-expr test) left
			(make-context-for-bool-p
			 (make-some (all-vars test) *true*) index)
			(some-expr-index))))
	   (when result
	     (make-some (all-vars test) result))))
	(out-vars-left
	 ;; (if test (true) (some () ...))
	 (log-coerce-expr-for-boolean-or-bool-p
	  test (if-test-index)
	  (make-context-for-bool-p (make-if test left *true*) index))
	 (push-proof-log 'remove-universal (if-test-index) (some-vars left) t)
	 (log-some-uncase-analysis-4 index)
	 ;; (some () (if test ... (true)))
	 (let ((result (pull-existentials-out-of-implies
			vars-test nil vars-left (cdr out-vars-left) test
			(some-expr left)
			(make-context-for-bool-p
			 (make-some (some-vars left) *true*) index)
			(some-expr-index))))
	   (when result
	     (make-some (some-vars left) result))))
	(vars-test
	 ;; (if (all () ...) left (true))
	 (log-coerce-expr-for-boolean-or-bool-p
	  left (if-left-index) bool-p)
	 (log-introduce-existential (all-vars test) (if-left-index))
	 (log-some-uncase-analysis-4 index)
	 ;; (some () (if ... left (true)))
	 (let ((result (pull-existentials-out-of-implies
			(cdr vars-test) nil vars-left nil (some-expr test) left
			(make-context-for-bool-p
			 (make-some (all-vars test) *true*) index)
			(some-expr-index))))
	   (when result
	     (make-some (all-vars test) result))))
	(vars-left
	 ;; (if test (true) (some () ...))
	 (log-coerce-expr-for-boolean-or-bool-p
	  test (if-test-index)
	  (make-context-for-bool-p (make-if test left *true*) index))
	 (push-proof-log 'remove-universal (if-test-index) (some-vars left) t)
	 (log-some-uncase-analysis-4 index)
	 ;; (some () (if test ... (true)))
	 (let ((result (pull-existentials-out-of-implies
			nil nil (cdr vars-left) nil test (some-expr left)
			(make-context-for-bool-p
			 (make-some (some-vars left) *true*) index)
			(some-expr-index))))
	   (when result
	     (make-some (some-vars left) result))))
	(t (make-if test left *true*))))

(defun move-quantifiers-out-of-and-not
    (vars out-vars test right kind bool-p index)
  (let ((bound-test (unique (list-of-bound-variables test)))
	(bound-right (unique (list-of-bound-variables right))))
    (let ((vars-test (intersection-eq vars bound-test))
	  (vars-right (intersection-eq vars bound-right))
	  (out-vars-test (intersection-eq out-vars bound-test))
	  (out-vars-right (intersection-eq out-vars bound-right)))
      (unless (or (intersection-eq vars-test vars-right)
		  (intersection-eq out-vars-test out-vars-right))
	(let ((result1 (move-quantifiers-out
			vars-test out-vars-test test
			(if (eq kind 'all) 'some 'all)
			(make-context-for-bool-p
			 (make-if test *false* right) index)
			(if-test-index))))
	  (when result1
	    (let ((result2 (move-quantifiers-out
			    vars-right out-vars-right test kind
			    bool-p
			    (if-right-index))))
	      (when result2
		(cond ((eq kind 'some)
		       (pull-existentials-out-of-and-not
			vars-test out-vars-test vars-right out-vars-right
			result1 result2 bool-p index))
		      (t
		       (pull-universals-out-of-and-not
			vars-test out-vars-test vars-right out-vars-right
			result1 result2 bool-p index)))))))))))

(defun pull-existentials-out-of-and-not
    (vars-test out-vars-test vars-right out-vars-right test right bool-p index)
  (cond (out-vars-test
	 (log-coerce-expr-for-boolean-or-bool-p right (if-right-index) bool-p)
	 ;; (if (all () ...) (false) (if right (true) (false)))
	 (log-some-uncase-analysis-3
	  (make-if test *false* (make-if right *true* *false*)) index)
	 ;; (some () (if ... (false) right))
	 (let ((result (pull-existentials-out-of-and-not
			vars-test (cdr out-vars-test) vars-right out-vars-right
			(all-expr test) right
			(make-context-for-bool-p
			 (make-some (all-vars test) *true*) index)
			(some-expr-index))))
	   (when result
	     (make-some (all-vars test) result))))
	(out-vars-right
	 ;; (if test (false) (some () rexpr))
	 (log-some-uncase-analysis-3a (make-if test *false* right) index)
	 ;; (some () (if ... (false) rexpr))
	 (let ((result (pull-existentials-out-of-and-not
			vars-test nil vars-right (cdr out-vars-right)
			test (all-expr right)
			(make-context-for-bool-p
			 (make-some (some-vars right) *true*) index)
			(some-expr-index))))
	   (when result
	     (make-some (some-vars right) result))))
	(vars-test
	 (log-coerce-expr-for-boolean-or-bool-p right (if-right-index) bool-p)
	 ;; (if (all () ...) (false) (if right (true) (false)))
	 (log-some-uncase-analysis-3
	  (make-if test *false* (make-if right *true* *false*)) index)
	 ;; (some () (if ... (false) right))
	 (let ((result (pull-existentials-out-of-and-not
			(cdr vars-test) nil vars-right nil (all-expr test) right
			(make-context-for-bool-p
			 (make-some (all-vars test) *true*) index)
			(some-expr-index))))
	   (when result
	     (make-some (all-vars test) result))))
	(vars-right
	 ;; (if test (false) (some () rexpr))
	 (log-some-uncase-analysis-3a (make-if test *false* right) index)
	 ;; (some () (if ... (false) rexpr))
	 (let ((result (pull-existentials-out-of-and-not
			nil nil (cdr vars-right) nil test (all-expr right)
			(make-context-for-bool-p
			 (make-some (some-vars right) *true*) index)
			(some-expr-index))))
	   (when result
	     (make-some (some-vars right) result))))
	(t (make-if test *false* right))))

(defun pull-universals-out-of-and-not
    (vars-test out-vars-test vars-right out-vars-right test right bool-p index)
  (cond (out-vars-test
	 ;; (if (some () ...) (false) right)
	 (log-coerce-expr-for-boolean-or-bool-p
	  right (if-right-index) bool-p)
	 (push-proof-log 'remove-universal (if-right-index) (some-vars test) t)
	 (log-all-uncase-analysis-5
	  (make-if test *false* (make-all (some-vars test) right)) index)
	 ;; (all () (if ... (false) right))
	 (let ((result (pull-universals-out-of-and-not
			vars-test (cdr out-vars-test) vars-right out-vars-right
			(some-expr test) right
			(make-context-for-bool-p
			 (make-all (some-vars test) *true*) index)
			(all-expr-index))))
	   (when result
	     (make-all (some-vars test) result))))
	(out-vars-right
	 ;; (if test (false) (all () ...))
	 (log-coerce-expr-for-boolean-or-bool-p
	  test (if-test-index)
	  (make-context-for-bool-p (make-if test *false* right) index))
	 (log-introduce-existential (all-vars right) (if-test-index))
	 (log-all-uncase-analysis-5
	  (make-if (make-some (all-vars right) test) *false* right) index)
	 ;; (all () (if test (false) ...))
	 (let ((result (pull-existentials-out-of-and-not
			vars-test nil vars-right (cdr out-vars-right)
			test (all-expr right)
			(make-context-for-bool-p
			 (make-all (all-vars right) *true*) index)
			(all-expr-index))))
	   (when result
	     (make-all (all-vars right) result))))
	(vars-test
	 ;; (if (some () ...) (false) right)
	 (log-coerce-expr-for-boolean-or-bool-p right (if-right-index) bool-p)
	 (push-proof-log 'remove-universal (if-right-index) (some-vars test) t)
	 (log-all-uncase-analysis-5
	  (make-if test *false* (make-all (some-vars test) right)) index)
	 ;; (all () (if ... (false) right))
	 (let ((result (pull-universals-out-of-and-not
			(cdr vars-test) nil vars-right nil
			(some-expr test) right
			(make-context-for-bool-p
			 (make-all (some-vars test) *true*) index)
			(all-expr-index))))
	   (when result
	     (make-all (some-vars test) result))))
	(vars-right
	 ;; (if test (false) (all () ...))
	 (log-coerce-expr-for-boolean-or-bool-p
	  test (if-test-index)
	  (make-context-for-bool-p (make-if test *false* right) index))
	 (log-introduce-existential (all-vars right) (if-test-index))
	 (log-all-uncase-analysis-5
	  (make-if (make-some (all-vars right) test) *false* right) index)
	 ;; (all () (if test (false) ...))
	 (let ((result (pull-existentials-out-of-and-not
			nil nil (cdr vars-right) nil test (all-expr right)
			(make-context-for-bool-p
			 (make-all (all-vars right) *true*) index)
			(all-expr-index))))
	   (when result
	     (make-all (all-vars right) result))))
	(t (make-if test *false* right))))




;;; The third group of routines try to move out the quantifications
;;; on vars.  Unlike "move-quantifiers-out", here the quantifications do
;;; not have to be of the same kind outside and they appear explicitly
;;; in the results returned.

;;; The real purpose of move-out-vars is to move quantifications out
;;; of if expressions.  Quantifications on out-of-scope variables
;;; are moved out so that they become in scope.  Quantifications on
;;; variables to be instantiated may need to be moved out if they
;;; appear in different components of an IF expression.

;;; Note that once move-out-vars fails, the proof log needs to be
;;; restored somewhere up the call chain.

;;; move-out-vars, if successful, produces a series of quantifications
;;; (not necessarily of the same kind) over vars.

(defun move-out-vars (vars formula bool-p index)
  (if (null vars)
      formula
      (let ((result (move-out-var (first vars) formula bool-p index)))
	(cond ((all-p result)
	       (let ((result2 (move-out-vars
			       (rest vars)
			       (all-expr result)
			       (make-context-for-bool-p result index)
			       (all-expr-index))))
		 (when result2
		   (make-all (all-vars result) result2))))
	      ((some-p result)
	       (let ((result2 (move-out-vars
			       (rest vars)
			       (some-expr result)
			       (make-context-for-bool-p result index)
			       (some-expr-index))))
		 (when result2
		   (make-some (some-vars result) result2))))))))

(defun move-out-var (var formula bool-p index)
  (cond ((all-p formula)
	 (if (eq (all-var formula) var)
	     formula
	     (let ((result (move-out-var
			    var (all-expr formula)
			    (make-context-for-bool-p formula index)
			    (all-expr-index))))
	       (when (all-p result)
		 (push-proof-log 'flip-universals index)
		 (make-all-single var (make-all (all-vars formula)
                                                (all-expr result)))))))
	((some-p formula)
	 (if (eq (some-var formula) var)
	     formula
	     (let ((result (move-out-var
			    var (some-expr formula)
			    (make-context-for-bool-p formula index)
			    (some-expr-index))))
	       (when (some-p result)
		 (log-flip-existentials index)
		 (make-some-single var (make-some (some-vars formula)
                                                  (some-expr result)))))))
	((if-p formula)
	 (move-out-var-if
	  var (if-test formula) (if-left formula) (if-right formula)
	  bool-p index))))



(defun move-out-var-if (var test left right bool-p index)
  (cond ((occurs-in var test)
	 (and (or (true-p left) (false-p left)
		  (true-p right) (false-p right))
	      (move-out-var-test var test left right bool-p index)))
	((occurs-in var left)
	 (let ((result (move-out-var var left bool-p (if-left-index))))
	   (cond ((and (all-p result) (or (bool-p right) bool-p))
		  (log-all-out-left (make-if test result right) bool-p index)
		  (make-all (all-vars result)
			    (make-if test (all-expr result) right)))
		 ((some-p result)
		  (log-some-out-left (make-if test result right) bool-p index)
		  (make-some (some-vars result)
			     (make-if test (some-expr result) right))))))
	((occurs-in var right)
	 (let ((result (move-out-var var right bool-p (if-right-index))))
	   (cond ((all-p result)
		  (log-all-out-right (make-if test left result) bool-p index)
		  (make-all (all-vars result)
			    (make-if test left (all-expr result))))
		 ((some-p result)
		  (log-some-out-right (make-if test left result) bool-p index)
		  (make-some (some-vars result)
			     (make-if test left	(some-expr result)))))))))

(defun move-out-var-test (var test left right bool-p index)
  (let ((result (move-out-var var test
			      (make-context-for-bool-p
			       (make-if test left right) index)
			      (if-test-index))))
    (cond ((all-p result)
	   (cond ((and (false-p left) (or (bool-p right) bool-p))
		  (log-coerce-expr-for-boolean-or-bool-p
		   right (if-right-index) bool-p)
		  (log-some-uncase-analysis-3
		   (make-if result left (make-if right *true* *false*)) index)
		  (make-some (all-vars result)
			     (make-if (all-expr result) left right)))
		 ((and (true-p right) (or (bool-p left) bool-p))
		  (log-coerce-expr-for-boolean-or-bool-p
		   left (if-left-index) bool-p)
		  (log-introduce-existential (all-vars result) (if-left-index))
		  (log-some-uncase-analysis-4 index)
		  (make-some (all-vars result)
			     (make-if (all-expr result) left right)))
		 ((and (true-p left) (or (bool-p right) bool-p))
		  (log-coerce-expr-for-boolean-or-bool-p
		   right (if-right-index) bool-p)
		  (log-all-uncase-analysis-3
		   (make-if result left (make-if right *true* *false*)) index)
		  (make-all (all-vars result)
			    (make-if (all-expr result) left right)))
		 ((and (false-p right) (or (bool-p left) bool-p))
		  (log-coerce-expr-for-boolean-or-bool-p
		   left (if-left-index) bool-p)
		  (push-proof-log 'remove-universal (if-left-index)
				  (all-vars result) t)
		  (push-proof-log 'all-case-analysis index t)
		  (make-all (all-vars result)
			    (make-if (all-expr result) left right)))))
	  ((some-p result)
	   (cond ((and (false-p left) (or (bool-p right) bool-p))
		  (log-coerce-expr-for-boolean-or-bool-p
		   right (if-right-index) bool-p)
		  (push-proof-log 'remove-universal (if-right-index)
				  (all-vars result) t)
		  (log-all-uncase-analysis-5
		   (make-if result left (make-all (some-vars result) right))
		   index)
		  (make-all (some-vars result)
			    (make-if (some-expr result) left right)))
		 ((and (true-p right) (or (bool-p left) bool-p))
		  (log-coerce-expr-for-boolean-or-bool-p
		   left (if-left-index) bool-p)
		  (log-all-uncase-analysis-2
		   (make-if result (make-if left *true* *false*) right) index)
		  (make-all (some-vars result)
			    (make-if (some-expr result) left right)))
		 ((and (true-p left) (or (bool-p right) bool-p))
		  (log-coerce-expr-for-boolean-or-bool-p
		   right (if-right-index) bool-p)
		  (log-introduce-existential
		   (some-vars result) (if-right-index))
		  (log-some-uncase-analysis-5
		   (make-if result left (make-some (some-vars result) right))
		   index)
		  (make-some (some-vars result)
			     (make-if (some-expr result) left right)))
		 ((and (false-p right) (or (bool-p left) bool-p))
		  (log-coerce-expr-for-boolean-or-bool-p
		   left (if-left-index) bool-p)
		  (log-some-uncase-analysis-2
		   (make-if result (make-if left *true* *false*) right) index)
		  (make-some (some-vars result)
			     (make-if (some-expr result) left right))))))))
