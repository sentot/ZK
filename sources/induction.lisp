
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


;;; Boyer-Moore style induction.

;;; All the heuristics of Boyer-Moore induction plus the concept of
;;; a scheme being inherently flawed when weeding out flawed
;;; induction schemes.

;;; More than half of the code has to do with proof logging.

;;; ----- Structures for use during induction.

;;; Structure for the induction cases. An induction template is just
;;; a list of induction cases.

(defstruct (induction-case  :named)
  tests           ;list of tests for the case
  substitutions   ;list of substitution lists (one for each recursive call)
  calls           ;list of recursive calls (*p*'s) in hypothesis
  hypothesis)     ;conjunction of *p*'s possibly universally quantified

;;; Structure for representing the induction schemes.

(defstruct (scheme  :named)
  template        ;induction template for the scheme
  changing        ;changing variables 
  unchanging      ;unchanging variables
  changeables     ;changeable variables
  unchangeables   ;unchangeable variables
  score           ;for ranking schemes
  flawed          ;flawed scheme
  origin)         ;term that suggested the induction scheme


;;; ==================== Prover Commands ====================

(defcmd induct (&optional term :display)
  ((:string "Try to apply an induction scheme to the current
subformula. Normally, the induction scheme is heuristically chosen.
However, you may explicitly supply a term on which to induct.
The term on which to induct does not have to be in the current
subformula."))
  (let ((formula (display-formula display))
        (template nil)
        (origin nil))
    (if (null term)
        (let ((schemes (get-induction-schemes
                        formula
                        (unique
                         (list-of-free-variables-unexpanded
                          formula)))))
          (when schemes
	    ;; Need to choose a scheme.
            (let ((scheme (select-induction-scheme schemes)))
	      ;; Set the template.
              (setq template (scheme-template scheme)
                    origin (scheme-origin scheme)))))
      (without-proof-logging
       ;; No need to choose a scheme in this case.
       (and (parse-formula-phase-1 term)
            (not (formula-unmentionable-p term))
            (subset-p (unique (list-of-free-variables-unexpanded term))
                      (unique (list-of-free-variables-unexpanded formula)))
	    ;; Set the template.
            (setq template (third (get-induction-template-for-term
                                   (rename-quantified-variables
                                    (expand-formula term nil) nil)
                                   (unique
                                    (list-of-free-variables-unexpanded
                                     formula))))
                  origin term))))
    (when template
      ;; Apply the template.
      (let* ((vars (unique (list-of-free-variables-unexpanded formula)))
             (machine (machine-from-template template vars))
	     (h1 (apply-machine-formula (if-form-machine machine) vars formula))
             (event (get-event (car origin)))
             (measured-expressions (mapcar #'(lambda (u v) (and u v))
                                           (ufunction-measured-subset event)
                                           (cdr origin)))
             (measured-positions
              (mapcar #'(lambda (u) (occurs-in u measured-expressions))
                      vars))
             (measured-quants (measured-quants-in-machine
                               machine measured-positions))
             (measure (sublis-eq (pairlis (ufunction-args event) (cdr origin))
                                 (ufunction-measure event))))
        (log-induction formula vars machine origin measure measured-quants
                       (display-base-index display))
	(push-proof-log 'marker index (list 'checkpoint
					    (make-implies h1 formula)))
	;; (implies H1 Phi) where H1 is induction machine in IF form.
        (log-apply-machine (if-form-machine machine)
				 template vars formula index
				 (make-context-for-bool-p
				  (make-all (last vars) *true*) (cdr index))))
      (push-proof-log 'marker index
		      (list 'checkpoint
			    (apply-induction-template-to-formula
			     template formula)))
      ;; Now really apply the template.
      (let ((result (unexpand-formula
                     (unrename-quantified-variables
                      (expand-formula
                       (apply-induction-template-to-formula template formula)
                       index)
                      index)
                     index)))
        (make-display :formula result
                      :explain
                      `((:string
                         "Inducting using the following scheme ...")
                        ;; **** Unrename may be different from above?
			(:newline)
                        (:formula ,(without-proof-logging
                                    (unexpand-formula
                                     (unrename-quantified-variables
                                      (expand-formula
                                       (scheme-description template formula)
                                       nil)
                                      nil)
                                     nil)))
                        (:newline)
                        (:string "produces ...")))))))

;;; Printable representation of a scheme that goes in a proof detail.
(defun scheme-description (induction-template formula)
  (let* ((vars (sort (unique
                      (list-of-free-variables-unexpanded formula))
                     #'alphalessp))
         (form (cons '*p* vars)))
    (apply-induction-template-to-formula induction-template form)))

(defcmd prove-by-induction (:display)
  ((:string "Try to prove the current subformula with automatic induction
(see")
   (:help-name induction)
   (:punctuation ").")
   (:string "A non-inductive proof is first attempted. If this fails,
the theorem prover will try to apply an induction scheme to the formula.
The theorem prover may discard the non-inductive proof prior to the
induction."))
  (let* ((original-formula-worth-inducting
           (worth-inducting-p (display-formula display)))
         (success (reduce)))
    (cond ((literal-p (display-formula *current-display*)) success)
          ((and success original-formula-worth-inducting)
           (back)
           (induct)
	   (reduce)
           t)                                   ;have succeeded
          ((worth-inducting-p (display-formula *current-display*))
           (induct)
	   (reduce)
           t)                                   ;induction performed
          (t success))))

;;; Decide whether or not we should induct on the formula.
(defun worth-inducting-p (formula)
  (get-induction-schemes formula
                         (unique (list-of-free-variables-unexpanded formula))))


;;; ==================== Supporting Functions ====================


;;; ----- Functions used to prepare proof logging.

;;; Construct induction machine from template.  May be different
;;; from induction machine stored in the struct for the recursive
;;; function, although the format is the same (a list of cases where
;;; each case has a list of assumptions and an induction hypothesis).
(defun machine-from-template (template vars)
  (mapcar
   #'(lambda (u)
       (let ((call-substitutions
              (mapcar
               #'(lambda (c s)
                   (cons c (sublis-eq s (cons *induction-pattern* vars))))
               (induction-case-calls u) (induction-case-substitutions u))))
         (list (induction-case-tests u)
               (sublis-equal call-substitutions
                             (induction-case-hypothesis u)))))
   template))

;;; List of bound variables in the hypotheses of the machines that
;;; occur in measured positions, needed for proof logging.
(defun measured-quants-in-machine (machine measured-positions)
  (let ((measured-expressions
         (loop for call in (list-of-calls *induction-pattern* machine)
               append (loop for expr in (cdr call)
                            for measured in measured-positions
                            when measured
                            collect expr)))
        (bound (loop for case in machine
                     append (list-of-bound-variables-unexpanded
                             (second case)))))
    (remove-if-not #'(lambda (u) (occurs-in u measured-expressions)) bound)))


;;; ==================== Templates ====================


;;; ----- Apply Template

;;; Take an induction template and a formula, and apply the template
;;; to produce an equivalent formula.
(defun apply-induction-template-to-formula (induction-template formula)
  ;; Note that the logging of AND expansions will be performed by
  ;; log-cases-if-hypothesis
  (add-simplified-conjuncts
   (mapcar #'(lambda (m) (make-induction-lemma-case m formula))
           induction-template)
   *true*))

 ;;; Make an induction case.
(defun make-induction-lemma-case (induction-case formula)
  (let ((induction-hypothesis
          (substitute-hypothesis
           (induction-case-substitutions induction-case)
           (induction-case-calls induction-case)
           (induction-case-hypothesis induction-case)
           formula)))
    (let ((result
           (make-implies
            ;; Note that the logging of AND expansions will be performed by
            ;; log-cases-if-hypothesis
            (add-simplified-conjuncts
	     (mapcar #'(lambda (u) (if (and (if-p u) (true-p (if-left u))
					    (false-p (if-right u)))
				       (if-test u)
				     u))
		     (append
		      (induction-case-tests induction-case)
		      (list-of-induction-hypotheses induction-hypothesis)))
	     *true*)
            formula)))
      result)))

(defun list-of-induction-hypotheses (induction-hypothesis)
  (cond ((and-p induction-hypothesis) (cdr induction-hypothesis))
	((null induction-hypothesis) nil)
	(t (list induction-hypothesis))))

(defun substitute-hypothesis (subst calls hypo formula)
  (sublis-equal
   (pairlis calls
            (mapcar #'(lambda (u) (sublis-eq u formula)) subst))
   hypo))


;;; ----- Make Template

;;; Make an induction template from a recursive definition and a
;;; term. It is assumed that the template suggested by the recursive
;;; definition applies to the term.
(defun construct-induction-template
    (args subst changeables unchangeables machine)
  (let ((instantiated-machine (sublis-eq subst machine)))
    (mapcar #'(lambda (m)
                (without-proof-logging
                 (let* ((hypothesis
                         (rename-quantified-variables
                          (second m) nil))
                        (calls (list-of-calls *induction-pattern*
                                              hypothesis)))
                   (make-induction-case
                    :tests (first m)
                    :substitutions
                    (construct-induction-substitutions args
                                                       changeables
                                                       unchangeables
                                                       calls)
                    :calls calls
                    :hypothesis hypothesis))))
            instantiated-machine)))

;;; Construct the substitutions for the calls of a machine case.
(defun construct-induction-substitutions
    (args changeables unchangeables calls)
  (when calls
    (cons (construct-induction-substitution-case
            args changeables unchangeables (car calls))
          (construct-induction-substitutions
            args changeables unchangeables (cdr calls)))))

;;; Construct the substitution for a call of a machine case. Illegal
;;; substitutions are deleted here.
(defun construct-induction-substitution-case
    (args changeables unchangeables call)
  (let ((subst (mapcar #'cons args (cdr call)))
        (substitution nil))
    (mapc #'(lambda (u v)
              (or
               ;; never substitute unchangeables
               (member-eq (car u) unchangeables)
               ;; never substitute non-variables
               (not (variable-p (car u)))
               ;;(eq (car u) (cdr u))
               (let ((entry (assoc-eq (car u) substitution)))
                 (setq substitution
                   (if (and entry v)
                       (cons u (remove-eq entry substitution))
                     (cons u substitution))))))
          subst changeables)
    (reverse substitution)))

;;; ----- Changing/Unchangeable Variables.

;;; Given an induction template, return the list of changing arguments
;;; (Boyer-Moore's terminology - from "A Computational Logic").
(defun changing-induction-variables-in-template (induction-template)
  (and (not (null induction-template))
       (unique
        (union-eq
         (variables-substituted
          (induction-case-substitutions (car induction-template)))
         (changing-induction-variables-in-template (cdr induction-template))))))

;;; Given a set of substitutions, return a unique list of variables that
;;; are substituted for (with something other than itself).
(defun variables-substituted (case-substitutions)
  (and (not (null case-substitutions))
       (unique
        (union-eq (loop for pair in (car case-substitutions)
                        when (not (eq (car pair) (cdr pair)))
                        collect (car pair))
                  (variables-substituted (cdr case-substitutions))))))

;;; List of unchangeables as defined in Boyer & Moore's "A Computational
;;; Logic." These are variables in expressions appearing in measured
;;; positions that cannot change.
(defun list-of-unchangeables
    (measured-positions unchanging-positions term-arguments)
  (let ((unchangeable-expressions (mapcar #'(lambda (u v w) (and u v w))
                                          measured-positions
                                          unchanging-positions
                                          term-arguments)))
    (unique (mapcan #'list-of-free-variables-unexpanded
                    unchangeable-expressions))))

;;; Return t if the elements of the given list are distinct variables.
(defun is-list-of-distinct-variables-p (list-of-expr)
  (let ((checked-variables nil)
        (success t))
    (dolist (e list-of-expr)
      (if (or (not (variable-p e))
              (member-eq e checked-variables))
          (return (setq success nil))
          (push e checked-variables)))
    success))


;;; =============== Choose Scheme ===============

;;; ----- Called first, get candidate induction schemes.

;;; Collect all induction schemes suggested by terms in the formula.
(defun get-induction-schemes (formula free-vars)
  (and (consp formula)
       (let ((induction-template
              (get-induction-template-for-term formula free-vars)))
         (cond (induction-template
                (let ((changeables (first induction-template))
                      (unchangeables (second induction-template))
                      (template (third induction-template)))
                  (let ((changing
                         (changing-induction-variables-in-template template))
                        (args (cdr formula)))
                    (cons (make-scheme :template template
                                       :changing changing
                                       :unchanging
                                       (set-difference-equal
                                        (unique
                                         (loop
                                          for x in args
                                          append
                                          (list-of-free-variables-unexpanded
                                           x)))
                                        changing)
                                       :changeables changeables
                                       :unchangeables unchangeables
                                       :score
                                       (rdiv (length changing)
                                             (length args))
				       ;; Set if inherently flawed.
                                       :flawed
                                       (flawed-template-p template args)
                                       :origin formula)
                          (loop for expr in formula
                              append (get-induction-schemes
                                      expr free-vars))))))
               (t (loop for expr in formula
                      append (get-induction-schemes expr free-vars)))))))

;;; Construct an induction template for a term when there is an
;;; induction template that applies to the term.
(defun get-induction-template-for-term (term free-vars)
  (and (consp term)
       (atom (first term))
       (let ((name (get-event (first term))))
         (and (ufunction-p name)
              (not (event-inaccessible-p name))
              (ufunction-recursive name)
              (every #'(lambda (v) (occurs-in v free-vars))
                     (unique (list-of-free-variables-unexpanded term)))
              (let ((measured-positions (ufunction-measured-subset name))
                    (unchanging-positions (ufunction-unchangeables name))
                    (term-arguments (cdr term)))
                (let ((changeables
                       (mapcar #'(lambda (u v w) (and u (not v) w))
                               measured-positions
                               unchanging-positions
                               term-arguments))
                      (unchangeables
                       (list-of-unchangeables measured-positions
                                              unchanging-positions
                                              term-arguments)))
                  (and (induction-template-applies-p changeables
                                                     unchangeables)
                       (list (remove-if #'null changeables)
                             unchangeables
                             (construct-induction-template
                              (cdr term)
                              (pairlis (ufunction-args name)
                                       (cdr term))
                              changeables
                              unchangeables
                              (ufunction-machine name))))))))))

;;; Return t if the changeables are distinct variables and the
;;; intersection of changeables and unchangeables is empty.
(defun induction-template-applies-p (changeables unchangeables)
  (let ((changeable-list (remove-if #'null changeables)))
    (and (is-list-of-distinct-variables-p changeable-list)
         (null (intersection-eq changeable-list unchangeables)))))

;;; Code to help determine if an induction scheme is inherently "flawed".

;;; Some cases flawed.
(defun flawed-template-p (template args)
  (some #'(lambda (u) (flawed-template-case u args)) template))

;;; All calls flawed.
(defun flawed-template-case (case args)
  (let ((calls (induction-case-calls case)))
    (and calls
         (every #'(lambda (u) (flawed-template-call u args)) calls))))

;;; Flawed call.
(defun flawed-template-call (call args)
  (some #'(lambda (u v) (and (not (equal u v)) (not (variable-p v))))
	(cdr call)
	args))


;;; ----- Select Induction Scheme

;;; Selection goes through 3 filtering steps before a winner is picked:
;;; 1. Remove subsumed schemes (and increase scores of subsuming schemes).
;;; 2. Merge schemes, removing the original schemes merged.
;;; 3. Remove flawed schemes if possible.
(defun select-induction-scheme (list-of-schemes)
  (superimpose-cases
   (pick-winner
    (list-of-unflawed-schemes
     (list-of-merged-schemes
      (list-of-unsubsumed-schemes list-of-schemes))))))

;;; Pick an induction scheme with the highest score.
(defun pick-winner (list-of-schemes)
  (let ((champ (first list-of-schemes)))
    (dolist (challenger (cdr list-of-schemes))
      (when (> (scheme-score challenger) (scheme-score champ))
        (setq champ challenger)))
    champ))


;;; =============== Code for Manipulating Schemes ===============


;;; ----- Superimpose Scheme Cases

;;; Once a winner is picked, superimpose (merge) induction cases that
;;; have the same test (condition).
(defun superimpose-cases (scheme)
  (when scheme
    (let ((template (scheme-template scheme))
          (acc nil))
      (dolist (case template)
        (unless
          (dolist (c acc)
             (when (and (subsetp-equal (induction-case-tests c)
                                       (induction-case-tests case))
                        (subsetp-equal (induction-case-tests case)
                                       (induction-case-tests c)))
               (setf (induction-case-substitutions c)
                     (append (induction-case-substitutions c)
                             (induction-case-substitutions case)))
               (setf (induction-case-calls c)
                     (append (induction-case-calls c)
                             (induction-case-calls case)))
               (setf (induction-case-hypothesis c)
                     (make-simplified-and (induction-case-hypothesis c)
                                          (induction-case-hypothesis case)))
               (simplify-superimposed-case c)
               (return t)))
          (push case acc)))
      (setf (scheme-template scheme) (reverse acc))))
  scheme)

(defun simplify-superimposed-case (case)
  (when (and-p (induction-case-hypothesis case))
      (let ((mask (simplify-superimposed-case-aux
                   nil (cdr (induction-case-hypothesis case)))))
        (setf (induction-case-substitutions case)
              (mapcan #'(lambda (x y) (and x (list y)))
                      mask (induction-case-substitutions case)))
        (setf (induction-case-calls case)
              (mapcan #'(lambda (x y) (and x (list y)))
                      mask (induction-case-calls case)))
        (setf (induction-case-hypothesis case)
              (mapcan #'(lambda (x y) (and x (list y)))
                      mask
                      (if (and-p (induction-case-hypothesis case))
                          (cdr (induction-case-hypothesis case))
                          (induction-case-hypothesis case))))
        (setf (induction-case-hypothesis case)
              (if (null (cdr (induction-case-hypothesis case)))
                  (car (induction-case-hypothesis case))
                  (cons 'and (induction-case-hypothesis case)))))))

(defun simplify-superimposed-case-aux (acc hyps)
  (cond ((null hyps) nil)
        ((member-equal (car hyps) acc)
         (cons nil (simplify-superimposed-case-aux acc (cdr hyps))))
        (t (cons t
                 (simplify-superimposed-case-aux (cons (car hyps) acc)
                                                 (cdr hyps))))))


;;; ----- Scheme Subsumption

;;; Given a list of induction schemes, it deletes those that are
;;; subsumed by other schemes. This is the first filtering step.
(defun list-of-unsubsumed-schemes (list-of-schemes)
  (and list-of-schemes
       (list-of-unsubsumed-schemes-aux
        (first list-of-schemes)
        (list-of-unsubsumed-schemes (cdr list-of-schemes))
        nil)))

(defun list-of-unsubsumed-schemes-aux
    (scheme unprocessed-schemes processed-schemes)
  (if (null unprocessed-schemes)
      (cons scheme processed-schemes)
      (let ((next-scheme (first unprocessed-schemes)))
        (cond ((scheme-subsumes-scheme-p scheme next-scheme)
               (list-of-unsubsumed-schemes-aux
                 (make-scheme
                  :template (scheme-template scheme)
                  :changing (scheme-changing scheme)
                  :unchanging (scheme-unchanging scheme)
                  :changeables (scheme-changeables scheme)
                  :unchangeables (scheme-unchangeables scheme)
                  :score (+ (scheme-score scheme)
                            (scheme-score next-scheme))
                  :flawed (scheme-flawed scheme)
                  :origin (scheme-origin scheme))
                 (cdr unprocessed-schemes)
                 processed-schemes))
              ((scheme-subsumes-scheme-p next-scheme scheme)
               (append (cdr unprocessed-schemes)
                       (cons (make-scheme
                              :template (scheme-template next-scheme)
                              :changing (scheme-changing next-scheme)
                              :unchanging (scheme-unchanging next-scheme)
                              :changeables (scheme-changeables next-scheme)
                              :unchangeables
                              (scheme-unchangeables next-scheme)
                              :score (+ (scheme-score scheme)
                                        (scheme-score next-scheme))
                              :flawed (scheme-flawed next-scheme)
                              :origin (scheme-origin next-scheme))
                             processed-schemes)))
              (t (list-of-unsubsumed-schemes-aux
                  scheme
                  (cdr unprocessed-schemes)
                  (cons next-scheme processed-schemes)))))))

;;; Subsumption check for induction schemes as described in
;;; Boyer & Moore's "A Computational Logic."

;;; Return t if the first scheme subsumes the second scheme.
(defun scheme-subsumes-scheme-p (scheme-1 scheme-2)
  (and (subset-p (scheme-changing scheme-2)
                 (scheme-changing scheme-1))
       (subset-p (scheme-unchanging scheme-2)
                 (scheme-unchanging scheme-1))
       (scheme-cases-subsume-p (scheme-template scheme-1)
                               (scheme-template scheme-2))))

;;; For cases of a scheme to subsume cases of another scheme each case of
;;; the latter scheme must be subsumed by a unique case of the former scheme.
(defun scheme-cases-subsume-p (template-1 template-2)
  (or (null template-2)
      (multiple-value-bind (subsumed updated-template)
          (scheme-case-subsumed-by (first template-2) template-1 nil)
        (and subsumed
             (scheme-cases-subsume-p updated-template (cdr template-2))))))

;;; Determine if a case is subsumed by a another case in a template.
;;; If successful it will return two values: t and the list of cases
;;; in the template minus the case that subsumes the first case.
(defun scheme-case-subsumed-by (case template updated-template)
  (cond ((null template) (values nil updated-template))
        ((scheme-single-case-subsumes-p (first template) case)
         (values t (append (cdr template) updated-template)))
        (t (scheme-case-subsumed-by
            case
            (cdr template)
            (cons (car template) updated-template)))))

;;; Return t if the first case subsumes the second case.
(defun scheme-single-case-subsumes-p (case-1 case-2)
  (and (subset-p (induction-case-tests case-2)
                 (induction-case-tests case-1))
       (substitutions-subsumes-substitutions-p
        (induction-case-substitutions case-1)
        (induction-case-substitutions case-2))))

;;; Return t if a list of substitutions subsumes a second list.
(defun substitutions-subsumes-substitutions-p
    (list-of-sublis-1 list-of-sublis-2)
  (or (null list-of-sublis-2)
      (multiple-value-bind (subsumed updated-list)
          (substitution-subsumed-by-list (first list-of-sublis-2)
                                         list-of-sublis-1
                                         nil)
        (and subsumed
             (substitutions-subsumes-substitutions-p
              updated-list (cdr list-of-sublis-2))))))

;;; Return a success indicator and the modified list of substitutions
;;; if the substitution is subsumed by a substitution in the list.
;;; The modified list will have the subsuming substitution removed.
(defun substitution-subsumed-by-list (subst list-of-subst updated-list)
  (cond ((null list-of-subst) (values nil updated-list))
        ((substitution-subsumed-by subst (first list-of-subst))
         (values t (append (cdr list-of-subst) updated-list)))
        (t (substitution-subsumed-by-list
            subst
            (cdr list-of-subst)
            (cons (car list-of-subst) updated-list)))))

(defun substitution-subsumed-by (subst1 subst2)
  (cond ((null subst1) t)
        (t (let ((match (assoc-eq (caar subst1) subst2)))
             (and match
                  (expr-occurs (cdar subst1) (cdr match))
                  (substitution-subsumed-by
                   (cdr subst1)
                   (remove-equal match subst2)))))))

;;; ----- Merging Schemes

;;; Given a list of schemes, it will delete those that can be merged into
;;; other schemes. This is the second filtering step.
(defun list-of-merged-schemes (list-of-schemes)
  (and list-of-schemes
       (list-of-merged-schemes-aux
        (first list-of-schemes)
        (list-of-merged-schemes (cdr list-of-schemes))
        nil)))

(defun list-of-merged-schemes-aux
    (scheme unprocessed-schemes processed-schemes)
  (if (null unprocessed-schemes)
      (cons scheme processed-schemes)
      (let ((merged (merge-schemes scheme (first unprocessed-schemes))))
        (if merged
            (list-of-merged-schemes-aux
             merged
             (append (cdr unprocessed-schemes)
                     processed-schemes)
             nil)
            (list-of-merged-schemes-aux
             scheme
             (cdr unprocessed-schemes)
             (cons (first unprocessed-schemes)
                   processed-schemes))))))

;;; Return the merged scheme if one of the schemes can be merged into
;;; the other scheme.
(defun merge-schemes (scheme-1 scheme-2)
  (and (not (null (intersection-eq (scheme-changing scheme-1)
                                   (scheme-changing scheme-2))))
       (null (intersection-eq (scheme-unchanging scheme-1)
                              (scheme-changing scheme-2)))
       (null (intersection-eq (scheme-unchanging scheme-2)
                              (scheme-changing scheme-1)))
       ;; only merge into a scheme which has no quantified hypothesis
       (or (make-merged-scheme
            scheme-2 scheme-1
            (merge-templates (scheme-template scheme-2)
                             (scheme-template scheme-1)))
           (make-merged-scheme
            scheme-1 scheme-2
            (merge-templates (scheme-template scheme-1)
                             (scheme-template scheme-2))))))

(defun make-merged-scheme (scheme-1 scheme-2 merged-template)
  (and merged-template
       (make-scheme
        :template merged-template
        :changing (unique (union-eq (scheme-changing scheme-1)
                                    (scheme-changing scheme-2)))
        :unchanging (unique (union-eq (scheme-unchanging scheme-1)
                                      (scheme-unchanging scheme-2)))
        :changeables (scheme-changeables scheme-2)
        :unchangeables (scheme-unchangeables scheme-2)
        :score (+ (scheme-score scheme-1) (scheme-score scheme-2))
        :flawed (or (scheme-flawed scheme-1) (scheme-flawed scheme-2))
        :origin (scheme-origin scheme-2))))

;;; Return the merged template if the first template can be merged into
;;; the second one.
(defun merge-templates (template-1 template-2)
  (and (<= (length template-1) (length template-2))
       (let ((template (merge-templates-stage-1 template-1 template-2)))
         (when template
           (merge-template-stage-2 template-1 template-2)))))

;;; In stage 1, try to merge each case of the first template into a unique
;;; case of the second template. If successful it will return the merged
;;; template.
(defun merge-templates-stage-1 (template-1 template-2)
  (merge-templates-stage-1-aux template-1 template-2
                               (mapcar #'(lambda (u) u nil) template-2)))

(defun merge-templates-stage-1-aux (template-1 template-2 merged-cases)
  (cond ((null template-1) template-2)
        ((null (induction-case-substitutions (car template-1)))
         (merge-templates-stage-1-aux
          (cdr template-1) template-2 merged-cases))
        (t (multiple-value-bind (template merged)
             (merge-templates-stage-1-aux-aux
              (car template-1) template-2 merged-cases nil nil)
             (when template
               (merge-templates-stage-1-aux
                (cdr template-1) template merged))))))

(defun merge-templates-stage-1-aux-aux (case template merged tmp mrg)
  (cond ((null template) (values nil nil))
        (t (let ((merged-case (and (null (car merged))
                                   (merge-cases-1 case (car template)))))
             (cond (merged-case (values (revappend tmp (cons merged-case
                                                             (cdr template)))
                                        (revappend mrg (cons t (cdr merged)))))
                   (t (merge-templates-stage-1-aux-aux
                       case (cdr template) (cdr merged)
                       (cons (car template) tmp)
                       (cons (car merged) mrg))))))))

;;; In stage 2, try to merge each case of template-1 into as many cases
;;; of template-2 as possible.  This stage will always be successful.
(defun merge-template-stage-2 (template-1 template-2)
  (cond ((null template-2) nil)
        ((null (induction-case-substitutions (car template-2)))
         (cons (car template-2)
               (merge-template-stage-2 template-1 (cdr template-2))))
        (t (cons (merge-template-stage-2-aux template-1 (car template-2))
                 (merge-template-stage-2 template-1 (cdr template-2))))))

(defun substitutions-in-template (template)
  (unless (null template)
    (append (induction-case-substitutions (car template))
            (substitutions-in-template (cdr template)))))

(defun bound-variables-in-template (template)
  (unless (null template)
    (append (list-of-bound-variables
             (induction-case-hypothesis (car template)))
            (bound-variables-in-template (cdr template)))))

(defun merge-template-stage-2-aux (template case-2)
  (multiple-value-bind (result s1 rs rc)
      (merge-cases-2 (induction-case-hypothesis case-2)
                     (induction-case-substitutions case-2)
                     (substitutions-in-template template)
                     nil
                     nil)
    (if (null s1)
        (make-induction-case :tests (induction-case-tests case-2)
                             :substitutions (reverse rs)
                             :calls (reverse rc)
                             :hypothesis (make-series-of-quantification
                                          'all
                                          (intersection-eq
                                           (unique (bound-variables-in-template
                                                    template))
                                           (list-of-all-variables result))
                                          result))
      case-2)))

(defun merge-cases-2 (expr s1 s2 rs rc)
  (cond ((atom expr) (values expr s1 rs rc))
        ((eq (car expr) *induction-pattern*)
         (let ((s nil) (c nil))
           (loop for ss in s2
                 do (let ((merged (merge-sublis ss (car s1))))
                      (when (and merged
                                 (not (equal (remove-equal-subst merged)
                                             (remove-equal-subst (car s1)))))
                        (push merged s)
                        (push (list* *induction-pattern* (gensym) (cdr expr))
                              c))))
           (cond (s (values (cons 'and (revappend c (list expr)))
                            (cdr s1)
                            (append s (cons (car s1) rs))
                            (append c (cons expr rc))))
                 (t (values expr (cdr s1) (cons (car s1) rs)
                            (cons expr rc))))))
        (t (let ((expr-stack nil) (exp nil) (ts1 s1) (trs rs) (trc rc))
             (loop for e in expr
                   do (progn (multiple-value-setq (exp ts1 trs trc)
                               (merge-cases-2 e ts1 s2 trs trc))
                             (push exp expr-stack)))
             (values (reverse expr-stack) ts1 trs trc)))))

(defun remove-equal-subst (substitution)
  (remove-if #'(lambda (u) (eq (car u) (cdr u))) substitution))

;;; Return the merged case if the first case can be merged into the
;;; second case.
(defun merge-cases-1 (case-1 case-2)
  (unless (null (induction-case-substitutions case-2))
    (let ((merged-subst (merge-substitutions
			 (induction-case-substitutions case-1)
			 (induction-case-substitutions case-2))))
      (and merged-subst
           (make-induction-case
             :tests (induction-case-tests case-2)
             :substitutions merged-subst
             :calls (induction-case-calls case-2)
             :hypothesis (make-series-of-quantification
			  'all
			  (unique (list-of-bound-variables
				   (induction-case-hypothesis case-1)))
			  (induction-case-hypothesis case-2)))))))

;;; Return the merged list of substitutions if the first list of
;;; substitutions can be merged into the second list.
(defun merge-substitutions (subst-1 subst-2)
  (let ((merged-subst (merge-substitutions-aux subst-1 subst-2 nil)))
    (when merged-subst (revappend merged-subst subst-2))))

(defun merge-substitutions-aux (subst-1 subst-2 merged-subst)
  (cond ((null subst-1) merged-subst)
        ((null subst-2) nil)
        (t (multiple-value-bind (merged updated-subst)
               (merge-sublis-with-subst (first subst-1) subst-2 nil)
             (when merged
               (merge-substitutions-aux (cdr subst-1)
                                        updated-subst
                                        (cons merged merged-subst)))))))


;;; Return the merged substitution and the modified list of substitutions
;;; if the substitution can be merged into a substitution from the list
;;; of substitutions. The modified list will have the merged substitution
;;; removed.
(defun merge-sublis-with-subst (sublis list-of-substs updated-subst)
  (cond ((null list-of-substs) (values nil nil))
        (t (let ((merged (merge-sublis sublis (first list-of-substs))))
             (if merged
                 (values merged
                         (revappend updated-subst (cdr list-of-substs)))
                 (merge-sublis-with-subst
                  sublis
                  (cdr list-of-substs)
                  (cons (car list-of-substs) updated-subst)))))))

;;; Return the merged substitution if the first substitution can be
;;; merged into the second substitution.
(defun merge-sublis (sublis-1 sublis-2)
  (let ((overlap (intersection-eq (mapcar #'car sublis-1)
                                  (mapcar #'car sublis-2))))
    (and overlap
         (consistent-overlap-p overlap sublis-1 sublis-2)
         (some #'(lambda (u) (neq u (cdr (assoc-eq u sublis-1)))) overlap)
         (append sublis-2
                 (remove-if #'(lambda (u) (member-equal u sublis-2))
                            sublis-1)))))

;;; Return t if the overlapping symbols are consistently substituted
;;; by the two substitutions
(defun consistent-overlap-p (overlap sublis-1 sublis-2)
  (or (null overlap)
      (and (equal (assoc-eq (first overlap) sublis-1)
                  (assoc-eq (first overlap) sublis-2))
           (consistent-overlap-p (cdr overlap) sublis-1 sublis-2))))

;;; ----- Flawed Schemes

;;; Remove flawed schemes. If every scheme is flawed, try just removing
;;; all "really flawed" schemes. If all the schemes are really flawed,
;;; none are removed. This is the 3rd and last filtering step.
(defun list-of-unflawed-schemes (list-of-schemes)
  (or (remove-if #'(lambda (u) (scheme-flawed-p u list-of-schemes))
                 list-of-schemes)
      (remove-if #'(lambda (u) (scheme-really-flawed-p u list-of-schemes))
                 list-of-schemes)
      list-of-schemes))

;;; Return t if the scheme is flawed with respect to a list of schemes.
;;; This is used for weeding out flawed schemes as described in BM's ACL.
(defun scheme-flawed-p (scheme list-of-schemes)
  (let ((changeables (scheme-changeables scheme)))
    (dolist (s list-of-schemes)
      (when (and (not (eq scheme s))
                 (or (intersection-eq changeables (scheme-changing s))
                     (intersection-eq changeables (scheme-unchanging s))))
        (return t)))))

;;; Boyer-Moore implementation in thm and nqthm added a second (weaker)
;;; pass in case everything is weeded out by the first pass.  We added
;;; our own improvisation to Boyer-Moore's 2nd pass.
(defun scheme-really-flawed-p (scheme list-of-schemes)
  (or (scheme-flawed scheme)   ; our own improvisation
      ;; BM's enhancement in thm and nqthm
      (let ((changing (scheme-changing scheme)))
        (dolist (s list-of-schemes)
          (when (and (not (eq scheme s))
                     (intersection-eq changing (scheme-unchanging s)))
            (return t))))))


;;; =============== Code to Log Induction ===============

;;; Logs conversion of
;;; (all vs Phi)
;;; to
;;; (all vs (implies H1 Phi))
;;; where H1 is the "machine" (induction hypothesis) in IF form.

(defun log-induction (formula vars machine term measure measured-quants index)
  (let ((m (genvar (input-variable-p '|)M|)))
        (m1 (genvar (input-variable-p '|)M1|)))
        (h1 (apply-machine-formula (if-form-machine machine) vars formula))
        (h2 (make-h2 measure vars formula)))
    ;; Start with (all vs Phi)
    ;; Note that H2 is the strong induction hypothesis for formula
    ;; using the supplied measure. H1 is the actual instantiated
    ;; induction hypothesis.
    (log-induction-phase-1 formula vars h1 h2 index)
    ;; We now have:
    ;; (if (= (all vs Phi) (all vs (implies (and H1 H2) Phi)))
    ;;     (all vs (implies H1 Phi))
    ;;     (all vs Phi))
    (log-induction-phase-2 formula vars machine term
                           (append (mapcar #'(lambda (u) u 2) vars)
                                   (cons 2 (if-test-index)))
                           h1 h2 measured-quants)
    ;; We now have:
    ;; (if (= (all vs Phi) (all vs (implies H2 Phi)))
    ;;     (all vs (implies H1 Phi))
    ;;     (all vs Phi))
    (log-induction-phase-3
     formula h2 vars measure m m1 (cons 2 (if-test-index)))
    ;; We now have:
    ;; (if (= (all vs Phi)
    ;;        (all m (implies
    ;;                  (all m1 (implies (m< m1 m)
    ;;                                   (all vs1 (implies (= m1 (mu[vs1]))
    ;;                                                     Phi[vs1]))))
    ;;                  (all vs (implies (= m (mu[vs])) Phi)))))
    ;;     (all vs (implies H1 Phi))
    ;;     (all vs Phi))
    (log-renames (mapcar #'cons (list-of-leading-universals h2) vars)
                 (list* 2 2 1 2 2 (if-test-index)))
    (log-label (append (mapcar #'(lambda (u) u 2) vars)
		       (cons 1 (if-test-index)))
	       m measure)
    ;; (if (= (all vs (if (some m (= m mu[vs])) Phi (true)))
    ;;        (all m (implies
    ;;                  (all m1 (implies (m< m1 m)
    ;;                                   (all vs (implies (= m1 (mu[vs]))
    ;;                                                    Phi))))
    ;;                  (all vs (implies (= m (mu[vs])) Phi)))))
    ;;     (all vs (implies H1 Phi))
    ;;     (all vs Phi))
    (let ((inner-index (append (mapcar #'(lambda (u) u 2) vars)
			       (cons 1 (if-test-index)))))
      (if (bool-p formula)
	  (push-proof-log 'is-boolean (cons 2 inner-index))
	(log-coerce-expr-in-boolean-context
	 (make-context-for-bool-p
	  (make-all (last vars) *true*) (cdr inner-index))
	 (cons 2 inner-index)))
      (push-proof-log 'syntax inner-index t))
    ;; We now have:
    ;; (if (= (all vs (implies (some m (= m mu[vs])) Phi))
    ;;        (all m (implies
    ;;                  (all m1 (implies (m< m1 m)
    ;;                                   (all vs (implies (= m1 (mu[vs]))
    ;;                                                    Phi))))
    ;;                  (all vs (implies (= m (mu[vs])) Phi)))))
    ;;     (all vs (implies H1 Phi))
    ;;     (all vs Phi))
    (push-proof-log 'syntax
                    (append (mapcar #'(lambda (u) u 2) vars)
                            (cons 1 (if-test-index))))
    ;; (if (= (all vs (if (some m (= m mu[vs])) (if Phi (true) (false)) (true)))
    ;;        (all m (implies
    ;;                  (all m1 (implies (m< m1 m)
    ;;                                   (all vs (implies (= m1 (mu[vs]))
    ;;                                                    Phi))))
    ;;                  (all vs (implies (= m (mu[vs])) Phi)))))
    ;;     (all vs (implies H1 Phi))
    ;;     (all vs Phi))
    (let ((expr (make-if (make-some-single m (make-= m measure))
			 (make-if formula *true* *false*)
			 *true*)))
      (log-all-uncase-analysis-2
       expr
       (append (mapcar #'(lambda (u) u 2) vars)
	       (cons 1 (if-test-index)))))
        
    ;; We now have:
    ;; (if (= (all vs (all m (if (= m mu[vs]) Phi (true))))
    ;;        (all m (implies
    ;;                  (all m1 (implies (m< m1 m)
    ;;                                   (all vs (implies (= m1 (mu[vs]))
    ;;                                                    Phi))))
    ;;                  (all vs (implies (= m (mu[vs])) Phi)))))
    ;;     (all vs (implies H1 Phi))
    ;;     (all vs Phi))
    (log-move-universal-out (length vars) (cons 1 (if-test-index)))
    (let ((inner-index (cons 2 (append (mapcar #'(lambda (u) u 2) vars)
				       (cons 1 (if-test-index))))))
      (if (bool-p formula)
	  (push-proof-log 'is-boolean (cons 2 inner-index))
	(log-coerce-expr-in-boolean-context
	 (make-context-for-bool-p
	  (make-all (last vars) *true*) (cdr inner-index))
	 (cons 2 inner-index)))
      (push-proof-log 'syntax inner-index t))
    ;; We now have:
    ;; (if (= (all m (all vs (implies (= m mu[vs]) Phi)))
    ;;        (all m (implies
    ;;                  (all m1 (implies (m< m1 m)
    ;;                                   (all vs (implies (= m1 (mu[vs]))
    ;;                                                    Phi))))
    ;;                  (all vs (implies (= m (mu[vs])) Phi)))))
    ;;     (all vs (implies H1 Phi))
    ;;     (all vs Phi))

    ;; This is where we apply the INDUCT inference rule.
    ;; (P m) is (all vs (implies (= m mu[vs]) Phi)).
    ;; (P m1) is (all vs (implies (= m1 mu[vs]) Phi)).

    (push-proof-log 'induct (cons 1 (if-test-index)) m1)

    ;; and get:
    ;; (if (= (all m (implies
    ;;                  (all m1 (implies (m< m1 m)
    ;;                                   (all vs (implies (= m1 (mu[vs]))
    ;;                                                    Phi))))
    ;;                  (all vs (implies (= m (mu[vs])) Phi))))
    ;;        (all m (implies
    ;;                  (all m1 (implies (m< m1 m)
    ;;                                   (all vs (implies (= m1 (mu[vs]))
    ;;                                                    Phi))))
    ;;                  (all vs (implies (= m (mu[vs])) Phi)))))
    ;;     (all vs (implies H1 Phi))
    ;;     (all vs Phi))

    (push-proof-log 'compute (if-test-index))
    (push-proof-log 'if-true index)
    ;; We end up with:
    ;; (all vs (implies H1 Phi))
    ))

;;; Apply if-form of the machine to formula (i.e. apply scheme
;;; to formula).

(defun apply-machine-formula (machine vars formula)
  (cond ((true-p machine) *true*)
        ((if-p machine)
         (make-if (if-test machine)
                  (apply-machine-formula (if-left machine) vars formula)
                  (apply-machine-formula (if-right machine) vars formula)))
        ((all-p machine)
         (make-all (all-vars machine)
                   (apply-machine-formula (all-expr machine) vars formula)))
        ((and-p machine)
         (cons 'and (mapcar #'(lambda (u)
                                (apply-machine-formula u vars formula))
                            (cdr machine))))
        (t (sublis-eq (pairlis vars (cdr machine)) formula))))

;;; Make strong induction hypothesis according to measure,
;;; quantifying over newvars that correspond to vars.

(defun make-h2 (measure vars formula)
  (let* ((newvars (mapcar #'genvar vars))
         (substitutions (pairlis vars newvars)))
    (make-series-of-quantification
     'all newvars
     (make-implies `(m< ,(sublis-eq substitutions measure) ,measure)
                   (sublis-eq substitutions formula)))))

;;; log-induction-phase-1 logs the inferences that converts:
;;; (all vs Phi)
;;; to:
;;; (if (= (all vs Phi) (all vs (implies (and H1 H2) Phi)))
;;;     (all vs (implies H1 Phi))
;;;     (all vs Phi))
;;; (This is the uninteresting phase.)

(defun log-induction-phase-1 (formula vars h1 h2 index)
  (when *debug-checker*
    (push-proof-log 'marker index '(log-induction-phase-1)))
  (let ((qform (make-series-of-quantification 'all vars formula)))
    (let ((qh1imp (make-series-of-quantification
                   'all vars (make-implies h1 formula)))
          (qh1h2imp (make-series-of-quantification
                     'all vars (make-implies (make-and h1 h2) formula))))
      ;; H2 is the strong induction hypothesis.
      ;; qform = (all vs Phi)
      ;; qh1imp = (all vs (implies H1 Phi))
      ;; qh1h2imp = (all vs (implies (and H1 H2) Phi))
      (push-proof-log 'if-equal index (make-= qform qh1h2imp) t)
      (push-proof-log 'if-equal (if-left-index) (make-= qform qh1imp) t)
      (log-equality-substitute qform qform qh1imp (cons 2 (if-left-index)))
      (push-proof-log
       'if-equal (cons 1 (if-left-index)) (make-= qform qh1h2imp) t)
      (log-cases-if
       (make-if (make-= qform qh1h2imp)
		(make-= qform qh1imp)
		(make-= qform qh1imp))
       nil
       (cons 1 (if-left-index)))
      ;; (if (= (all vs Phi) (all vs (implies (and H1 H2) Phi)))
      ;;     (if (and (implies (= (all vs Phi)
      ;;                          (all vs (implies (and H1 H2) Phi)))
      ;;                       (all vs (implies H1 Phi)))
      ;;              (implies (not (= (all vs Phi)
      ;;                               (all vs (implies (and H1 H2) Phi))))
      ;;                       (all vs (implies H1 Phi)))
      ;;         (all vs (implies H1 Phi))
      ;;         (all vs Phi))
      ;;     (all vs Phi))
      (push-proof-log 'if-equal (cons 1 (cons 1 (if-left-index))) qform t)
      (log-induction-phase-1-aux
       vars (make-implies h1 formula) qform qh1imp qh1h2imp
       (list* 1 1 (if-left-index)))
      ;; (if (= (all vs Phi) (all vs (implies (and H1 H2) Phi)))
      ;;     (if (and (true)
      ;;              (implies (not (= (all vs Phi)
      ;;                               (all vs (implies (and H1 H2) Phi))))
      ;;                       (all vs (implies H1 Phi)))
      ;;         (all vs (implies H1 Phi))
      ;;         (all vs Phi))
      ;;     (all vs Phi))

      ;; Seems to be this:
      ;; (if (= (all vs Phi) (all vs (implies (and H1 H2) Phi)))
      ;;     (if (and (true)
      ;;              (implies (not (= (all vs Phi)
      ;;                               (all vs (implies (and H1 H2) Phi))))
      ;;                       (= (all vs Phi) (all vs (implies H1 Phi))))
      ;;         (all vs (implies H1 Phi))
      ;;         (all vs Phi))
      ;;     (all vs Phi))

      (push-proof-log 'syntax (cons 1 (if-left-index)))
      ;; (if (= (all vs Phi) (all vs (implies (and H1 H2) Phi)))
      ;;     (if (if (true)
      ;;             (if (implies (not (= (all vs Phi)
      ;;                                  (all vs (implies (and H1 H2) Phi))))
      ;;                          (all vs (implies H1 Phi)))
      ;;                 (true)
      ;;                 (false))
      ;;             (false))
      ;;         (all vs (implies H1 Phi))
      ;;         (all vs Phi))
      ;;     (all vs Phi))
      (push-proof-log 'if-true (cons 1 (if-left-index)))
      
      (push-proof-log 'is-boolean (cons 1 (if-left-index)) t)
      
      ;; (if (= (all vs Phi) (all vs (implies (and H1 H2) Phi)))
      ;;     (if (implies (not (= (all vs Phi)
      ;;                          (all vs (implies (and H1 H2) Phi))))
      ;;                  (all vs (implies H1 Phi)))
      ;;         (all vs (implies H1 Phi))
      ;;         (all vs Phi))
      ;;     (all vs Phi))
      ;; (if (= (all vs Phi) (all vs (implies (and H1 H2) Phi)))
      ;;     (...)
      ;;     (all vs Phi))
      (push-proof-log 'look-up (list* 1 1 1 (if-left-index)) *true*)
      ;; (if (= (all vs Phi) (all vs (implies (and H1 H2) Phi)))
      ;;     (if (implies (not (true)) (all vs (implies H1 Phi)))
      ;;         (all vs (implies H1 Phi))
      ;;         (all vs Phi))
      ;;     (all vs Phi))
      ;; (if (= (all vs Phi) (all vs (implies (and H1 H2) Phi)))
      ;;     (...)
      ;;     (all vs Phi))
      (push-proof-log 'syntax (cons 1 (cons 1 (if-left-index))))
      (push-proof-log 'if-true (cons 1 (cons 1 (if-left-index))))
      (push-proof-log 'syntax (cons 1 (if-left-index)))
      (push-proof-log 'if-false (cons 1 (if-left-index)))
      (push-proof-log 'if-true (if-left-index)))))

;;; log-induction-phase-1-aux logs inferences that converts:
;;; (if (all vs Phi)
;;;     (implies (= (all vs Phi) (all vs (implies (and H1 H2) Phi)))
;;;              (= (all vs Phi) (all vs (implies H1 Phi))))
;;;     (implies (= (all vs Phi) (all vs (implies (and H1 H2) Phi)))
;;;              (= (all vs Phi) (all vs (implies H1 Phi)))))
;;; to:
;;; (true).

(defun log-induction-phase-1-aux (vars h1imp qform qh1imp qh1h2imp index)
  (when *debug-checker*
    (push-proof-log 'marker index '(log-induction-phase-1-aux)))
  (push-proof-log 'look-up (cons 1 (cons 1 (if-left-index))) *true*)
  (log-=-true-left-to-if qh1h2imp (cons 1 (if-left-index)))
  (push-proof-log 'is-boolean (cons 1 (if-left-index)) t)
  (push-proof-log 'look-up (cons 1 (cons 2 (if-left-index))) *true*)
  (log-=-true-left-to-if qh1imp (cons 2 (if-left-index)))
  (push-proof-log 'is-boolean (cons 2 (if-left-index)) t)
  ;; (if (all vs Phi)
  ;;     (implies (all vs (implies (and H1 H2) Phi))
  ;;              (all vs (implies H1 Phi)))
  ;;     (implies (= (all vs Phi) (all vs (implies (and H1 H2) Phi)))
  ;;              (= (all vs Phi) (all vs (implies H1 Phi)))))
  (log-look-up-false (cons 1 (cons 1 (if-right-index))))
  (log-=-false-left-to-if qh1h2imp (cons 1 (if-right-index)))
  (log-look-up-false (cons 1 (cons 2 (if-right-index))))
  (log-=-false-left-to-if qh1imp (cons 2 (if-right-index)))
  ;; (if (all vs Phi)
  ;;     (implies (all vs (implies (and H1 H2) Phi))
  ;;              (all vs (implies H1 Phi)))
  ;;     (implies (if (all vs (implies (and H1 H2) Phi)) (false) (true))
  ;;              (if (all vs (implies H1 Phi)) (false) (true))))
  (log-cases-if
   (make-if qform
	    (make-implies qh1h2imp qh1imp)
	    (make-implies (make-if qh1h2imp *false* *true*)
			  (make-if qh1imp *false* *true*)))
   nil
   index)
  ;; (and (implies (all vs Phi)
  ;;               (implies (all vs (implies (and H1 H2) Phi))
  ;;                        (all vs (implies H1 Phi))))
  ;;      (implies (not (all vs Phi))
  ;;               (implies (if (all vs (implies (and H1 H2) Phi))
  ;;                            (false)
  ;;                            (true))
  ;;                        (if (all vs (implies H1 Phi)) (false) (true)))))
  (push-proof-log 'syntax (and-left-index))
  (push-proof-log 'is-boolean (cons 2 (and-left-index)) t)
  ;; (and (if (all vs Phi)
  ;;          (implies (all vs (implies (and H1 H2) Phi))
  ;;                   (all vs (implies H1 Phi)))
  ;;          (true))
  ;;      (implies (not (all vs Phi))
  ;;               (implies (if (all vs (implies (and H1 H2) Phi))
  ;;                            (false)
  ;;                            (true))
  ;;                        (if (all vs (implies H1 Phi)) (false) (true)))))
  (push-proof-log 'syntax (cons 2 (and-left-index)))
  (push-proof-log 'is-boolean (cons 2 (cons 2 (and-left-index))) t)
  ;; (and (if (all vs Phi)
  ;;          (if (all vs (implies (and H1 H2) Phi))
  ;;              (all vs (implies H1 Phi))
  ;;              (true))
  ;;          (true))
  ;;      (implies (not (all vs Phi))
  ;;               (implies (if (all vs (implies (and H1 H2) Phi))
  ;;                            (false)
  ;;                            (true))
  ;;                        (if (all vs (implies H1 Phi)) (false) (true)))))
  (log-induction-phase-1-aux-1
   vars (and-left-index) h1imp qform qh1imp qh1h2imp)
  (push-proof-log 'syntax index)
  ;; (if (true)
  ;;     (if (implies (not (all vs Phi))
  ;;                  (implies (if (all vs (implies (and H1 H2) Phi))
  ;;                               (false)
  ;;                               (true))
  ;;                           (if (all vs (implies H1 Phi)) (false) (true))))
  ;;         (true)
  ;;         (false))
  ;;     (false))
  (push-proof-log 'if-true index)
  (push-proof-log 'is-boolean index t)
  (log-induction-phase-1-aux-2 vars qform qh1imp qh1h2imp index)
  )

;;; log-induction-phase-1-aux-1 logs inferences that converts:
;;; (if (all vs Phi)
;;;     (if (all vs (implies (and H1 H2) Phi))
;;;         (all vs (implies H1 Phi))
;;;         (true))
;;;     (true))
;;; to:
;;; (true).

(defun log-induction-phase-1-aux-1 (vars index h1imp qform qh1imp qh1h2imp)
  (when *debug-checker*
    (push-proof-log 'marker index '(log-induction-phase-1-aux-1)))
  (let* ((renames (mapcar #'genvar vars))
	 (renamed-h1imp (sublis-eq (pairlis vars renames) h1imp))
	 (renamed-qh1imp (sublis-eq (pairlis vars renames) qh1imp)))
    (log-renames (mapcar #'cons vars renames) (cons 2 (if-left-index)))
    (log-all-out-lefts vars (if-left-index) qh1h2imp renamed-qh1imp)
    (log-all-out-lefts
     vars index qform
     (universally-quantify renames (make-if qh1h2imp renamed-h1imp *true*)))
    (let ((inner-index (display-formula-index-aux renames index)))
      (linearize-and-log-universal-instantiations
       (mapcar #'make-= vars renames)
       (cons 1 inner-index))
      (push-proof-log 'case-analysis inner-index 1)
      (push-proof-log 'if-false (cons 3 inner-index))
      (push-proof-log 'syntax (list* 2 2 2 inner-index))
      (push-proof-log 'look-up (list* 1 2 2 2 2 inner-index) *true*)
      (push-proof-log 'if-true (list* 2 2 2 2 inner-index))
      (push-proof-log 'if-equal (list* 2 2 2 inner-index))
      (push-proof-log 'if-equal (list* 2 2 inner-index))
      (push-proof-log 'if-equal (cons 2 inner-index))
      (push-proof-log 'if-equal inner-index)
      (dotimes (i (length vars))
        i
        (push-proof-log 'remove-universal index)
        (push-proof-log 'is-boolean index t))))
  )

;;; log-induction-phase-1-aux-2 logs inferences that converts:
;;; (implies (not (all vs Phi))
;;;          (implies (if (all vs (implies (and H1 H2) Phi)) (false) (true))
;;;                   (if (all vs (implies H1 Phi)) (false) (true))))
;;; to:
;;; (true).

(defun log-induction-phase-1-aux-2 (vars qform qh1imp qh1h2imp index)
  (when *debug-checker*
    (push-proof-log 'marker index '(log-induction-phase-1-aux-2)))
  (push-proof-log 'syntax (implies-right-index))
  ;; (implies (not (all vs Phi))
  ;;          (if (if (all vs (implies (and H1 H2) Phi)) (false) (true))
  ;;              (if (if (all vs (implies H1 Phi)) (false) (true))
  ;;                  (true)
  ;;                  (false))
  ;;              (true)))
  (push-proof-log 'case-analysis (implies-right-index) 1)
  ;; (implies (not (all vs Phi))
  ;;          (if (all vs (implies (and H1 H2) Phi))
  ;;              (if (false)
  ;;                  (if (if (all vs (implies H1 Phi)) (false) (true))
  ;;                      (true)
  ;;                      (false))
  ;;                  (true))
  ;;              (if (true)
  ;;                  (if (if (all vs (implies H1 Phi)) (false) (true))
  ;;                      (true)
  ;;                      (false))
  ;;                  (true))))
  (push-proof-log 'if-false (cons 2 (implies-right-index)))
  (push-proof-log 'if-true (cons 3 (implies-right-index)))
  ;; (implies (not (all vs Phi))
  ;;          (if (all vs (implies (and H1 H2) Phi))
  ;;              (true)
  ;;              (if (if (all vs (implies H1 Phi)) (false) (true))
  ;;                  (true)
  ;;                  (false)))))
  (push-proof-log 'case-analysis (cons 3 (implies-right-index)) 1)
  ;; (implies (not (all vs Phi))
  ;;          (if (all vs (implies (and H1 H2) Phi))
  ;;              (true)
  ;;              (if (all vs (implies H1 Phi))
  ;;                  (if (false) (true) (false))
  ;;                  (if (true) (true) (false)))))
  (push-proof-log 'if-false (list* 2 3 (implies-right-index)))
  (push-proof-log 'if-true (list* 3 3 (implies-right-index)))
  ;; (implies (not (all vs Phi))
  ;;          (if (all vs (implies (and H1 H2) Phi))
  ;;              (true)
  ;;              (if (all vs (implies H1 Phi)) (false) (true))))
  (let* ((renames (mapcar #'genvar vars))
	 (substitutions (mapcar #' cons vars renames)))
    (log-renames substitutions (cons 1 (implies-right-index)))
    (log-repeat-all-out-tests
     renames
     (make-if (sublis-eq substitutions qh1h2imp)
	      *true*
	      (make-if qh1imp *false* *true*))
     (implies-right-index))
    ;; (implies (not (all vs Phi))
    ;;          (all vs' (if (implies (and H1 H2) Phi)
    ;;                       (true)
    ;;                       (if (all vs (implies H1 Phi)) (false) (true))))
    (let ((inner-index (display-formula-index-aux renames
                                                  (implies-right-index))))
      ;; inner-index points to
      ;;   (if (implies (and H1 H2) Phi)
      ;;       (true)
      ;;       (if (all vs (implies H1 Phi)) (false) (true)))
      (push-proof-log 'syntax (cons 1 inner-index))
      (push-proof-log 'syntax (list* 1 1 inner-index))
      ;; (if (if (if H1 (if H2 (true) (false)) (false))
      ;;         (if Phi (true) (false))
      ;;         (true))
      ;;     (true)
      ;;     (if (all vs (implies H1 Phi)) (false) (true)))
      (push-proof-log 'syntax
                      (append (mapcar #'(lambda (u) u 2) vars)
                              (list* 1 3 inner-index)))
      ;; (if (if (if H1 (if H2 (true) (false)) (false))
      ;;         (if Phi (true) (false))
      ;;         (true))
      ;;     (true)
      ;;     (if (all vs (if H1 (if Phi (true) (false)) (true)))
      ;;         (false)
      ;;         (true)))
      (push-proof-log 'case-analysis inner-index 1)
      (push-proof-log 'if-true (cons 3 inner-index))
      ;; (if (if H1 (if H2 (true) (false)) (false))
      ;;     (if (if Phi (true) (false))
      ;;         (true)
      ;;         (if (all vs (if H1 (if Phi (true) (false)) (true)))
      ;;             (false)
      ;;             (true)))
      ;;     (true))
      (push-proof-log 'case-analysis (cons 2 inner-index) 1)
      (push-proof-log 'if-true (list* 2 2 inner-index))
      (push-proof-log 'if-false (list* 3 2 inner-index))
      ;; (if (if H1 (if H2 (true) (false)) (false))
      ;;     (if Phi
      ;;         (true)
      ;;         (if (all vs (if H1 (if Phi (true) (false)) (true)))
      ;;             (false)
      ;;             (true)))
      ;;     (true))
      (push-proof-log 'case-analysis inner-index 1)
      (push-proof-log 'if-false (cons 3 inner-index))
      ;; (if H1
      ;;     (if (if H2 (true) (false))
      ;;         (if Phi
      ;;             (true)
      ;;             (if (all vs (if H1 (if Phi (true) (false)) (true)))
      ;;                 (false)
      ;;                 (true)))
      ;;         (true))
      ;;     (true))
      (linearize-and-log-universal-instantiations
       (mapcar #'make-= vars renames)
       (list* 1 3 2 2 inner-index))
      ;; (if H1
      ;;     (if (if H2 (true) (false))
      ;;         (if Phi
      ;;             (true)
      ;;             (if (if (if H1' (if Phi' (true) (false)) (true))
      ;;                     (all vs (if H1 (if Phi (true) (false)) (true)))
      ;;                     (false))
      ;;                 (false)
      ;;                 (true)))
      ;;         (true))
      ;;     (true))
      (push-proof-log 'look-up (list* 1 1 1 3 2 2 inner-index) *true*)
      ;; (if H1
      ;;     (if (if H2 (true) (false))
      ;;         (if Phi
      ;;             (true)
      ;;             (if (if (if (true) (if Phi' (true) (false)) (true))
      ;;                     (all vs (if H1 (if Phi (true) (false)) (true)))
      ;;                     (false))
      ;;                 (false)
      ;;                 (true)))
      ;;         (true))
      ;;     (true))
      ;; Phi' is boolean? Coerce to make sure.
      (log-coerce-if-test-to-bool (list* 2 1 1 3 2 2 inner-index))
      (log-look-up-false-for-coercion (list* 1 2 1 1 3 2 2 inner-index))
      (push-proof-log 'if-true (list* 1 1 3 2 2 inner-index))
      (push-proof-log 'if-false (list* 1 1 3 2 2 inner-index))
      (push-proof-log 'if-false (list* 1 3 2 2 inner-index))
      (push-proof-log 'if-false (list* 3 2 2 inner-index))
      ;; (if H1
      ;;     (if (if H2 (true) (false))
      ;;         (if Phi (true) (true))
      ;;         (true))
      ;;     (true))
      (push-proof-log 'if-equal (list* 2 2 inner-index))
      (push-proof-log 'if-equal (cons 2 inner-index))
      (push-proof-log 'if-equal inner-index)
      ;; (true)

      ;; Finished with inner-index ======
      (dotimes (i (length vars))
        i
        (push-proof-log 'remove-universal (implies-right-index))
        (push-proof-log 'is-boolean (implies-right-index) t))
      (push-proof-log 'syntax index)
      (push-proof-log 'is-boolean (if-left-index) t)
      (push-proof-log 'if-equal index)))
  )

(defun log-all-out-lefts (vars index test left)
  (unless (null vars)
    ;; (if test (all () ...) (true))
    (log-all-uncase-analysis-2a (make-if test left *true*) index)
    (log-all-out-lefts (cdr vars) (all-expr-index)
		       test (all-expr left))))

(defun log-repeat-all-out-tests (vars formula index &optional bool-p)
  ;; (if (all (var1) (all (var2) ... P)) (true) Q)
  (unless (null vars)
    (let* ((q (if-right formula))
	   (coerced-q (make-if q *true* *false*)))
      ;; either Q is boolean or in boolean context so that Q
      ;; and (if Q (true) (false)) are equivalent.
      (log-coerce-expr-for-boolean-or-bool-p q (if-right-index) bool-p)
      ;; (if (all (var1) (all (var2) ... P)) (true) (if Q (true) (false)))
      (log-all-uncase-analysis-3
       (make-if (if-test formula) *true* coerced-q) index)
      ;; (all (var1) (if (all (var2) ... P) (true) Q))
      (unless (null (cdr vars))
	(log-repeat-all-out-tests
	 (cdr vars) (make-if (all-expr (if-test formula)) *true* q)
	 (all-expr-index)
	 (make-context-for-bool-p (make-all (list (car vars)) *true*) index)))
      )))



;;; log-induction-phase-2 logs inferences that converts
;;; (implies (and H1 H2) Phi)
;;; to
;;; (implies H2 Phi)
;;; index points to (implies (and H1 H2) Phi)
;;; term is the term that suggested the induction, e.g. (div i j)

(defun log-induction-phase-2
    (formula vars machine term index h1 h2 measured-quants)
  (when *debug-checker*
    (push-proof-log 'marker index '(log-induction-phase-2)))
  ;; commute H1 and H2 and then convert to if form
  (log-use-axiom-as-rewrite
   (make-and h1 h2) 'and.commutative
   (list (make-= '|)X| h1) (make-= '|)Y| h2)) (implies-left-index))
  (push-proof-log 'syntax index)
  (push-proof-log 'syntax (if-test-index))
  ;; (if (if H2 (if H1 (true) (false)) (false)) (if Phi (true) (false)) (true))
  (push-proof-log 'case-analysis index 1)
  ;; (if H2
  ;;     (if (if H1 (true) (false)) (if Phi (true) (false)) (true))
  ;;     (if (false) (if Phi (true) (false)) (true)))
  (log-remove-bool-coercion-from-if-test (if-left-index))
  (push-proof-log 'if-false (if-right-index))
  ;; At this point we have:
  ;; (if H2
  ;;     (if H1
  ;;         (if Phi (true) (false))
  ;;         (true))
  ;;     (true))
  
  ;; We now do the interesting part which is to knock off H1
  ;; (converting it to (true) with the help of PO).
  (let* ((po-name (intern (format nil "~A.PO" (car term))
			  *zk-package*))
         (po-args (unique (list-of-free-variables-unexpanded
                           (ufunction-formula (get-event (car term))))))
         (orig-po
          (progn
            (log-use-axiom (if-left-index) po-name)
            (ufunction-formula (get-event (car term)))))
         (po-args-renames (mapcar #'genvar po-args))
         (args (ufunction-args (get-event (car term))))
	 ;; rename inner quantifications of PO
         (renamed-po
          (rename-quantified-variables-unexpanded
           orig-po
           (append (mapcar #'(lambda (u) u 2) po-args)
                   (cons 1 (if-left-index)))))
	 ;; po is the PO applied to the induction term
         (po (sublis-eq (pairlis args (cdr term)) renamed-po)))
    (log-renames (mapcar #'cons po-args po-args-renames)
                 (cons 1 (if-left-index)))
    ;; (if H2
    ;;     (if quantifiedPO
    ;;         (if H1
    ;;             (if Phi (true) (false))
    ;;             (true))
    ;;         (true))
    ;;     (true))
    (let ((substitutions (pairlis (sublis-eq (pairlis po-args po-args-renames)
                                             args)
                                  (cdr term))))
      (linearize-and-log-universal-instantiations
       (mapcar #'(lambda (u) (make-= u (cdr (assoc-eq u substitutions))))
               po-args-renames)
       (cons 1 (if-left-index))))
    ;; At this point quantifiedPO has been transformed by instantiation.
    ;; (if H2
    ;;     (if (if PO quantifiedPO (false))
    ;;         (if H1
    ;;             (if Phi (true) (false))
    ;;             (true))
    ;;         (true))
    ;;     (true))

    ;; rename back the outer quantification
    (log-renames (mapcar #'cons po-args-renames po-args)
                 (list* 2 1 (if-left-index)))
    ;; unrename inner quantification of PO before discarding the axiom
    (log-renames-unexpanded
     renamed-po orig-po (append (mapcar #'(lambda (u) u 2) po-args)
                                (list* 2 1 (if-left-index))))
    (push-proof-log 'use-axiom (cons 2 (cons 1 (if-left-index))) po-name t)
    (log-remove-bool-coercion-from-if-test (if-left-index))
    ;; (if H2
    ;;     (if PO
    ;;         (if H1
    ;;             (if Phi (true) (false))
    ;;             (true))
    ;;         (true))
    ;;     (true))
    (push-proof-log 'syntax (cons 2 (if-left-index)) t)
    (push-proof-log 'is-boolean (cons 2 (if-left-index)))
    (push-proof-log 'syntax (if-left-index) t)
    (log-unnest-implies formula (if-left-index))
    ;; At this point we have:
    ;; (if H2 (implies (and PO H1) Phi) (true))
    (let ((expanded-po
           (expand-formula po (list* 1 1 (if-left-index)))))
      (log-induction-phase-2-aux
       formula vars
       (if-form-machine machine)
       expanded-po
       (cons 1 (if-left-index)) h1 h2
       measured-quants nil))
    ;; We now have (if H2 (implies PO Phi) (true))
    (let ((idx (cons 1 (if-left-index))))
      (push-proof-log 'if-equal idx `(= ,po ,po) t)
      ;; PO is now replaced by (if (= PO PO) PO PO)
      (expand-formula po (list* 1 1 idx))
      (push-proof-log 'look-up (cons 2 idx) po)
      (expand-formula po (list* 2 1 idx))
      (push-proof-log 'compute (cons 1 idx))
      (push-proof-log 'if-true idx)
      ;; we now have the unexpanded PO
      )
    (push-proof-log 'syntax (if-left-index))
    ;; (if H2 (if PO (if Phi (true) (false)) (true)) (true))
    (log-use-axiom (cons 2 (if-left-index)) po-name)
    (log-renames-unexpanded
     orig-po renamed-po (append (mapcar #'(lambda (u) u 2) po-args)
                                (list* 1 2 (if-left-index))))
    (log-renames (mapcar #'cons po-args po-args-renames)
                 (list* 1 2 (if-left-index)))
    ;; (if H2 (if PO (if qPO (if Phi (true) (false)) (true)) (true)) (true))
    (push-proof-log 'syntax (cons 2 (if-left-index)) t)
    ;; (if H2 (if PO (implies qPO Phi) (true)) (true))
    (push-proof-log 'is-boolean (cons 2 (if-left-index)))
    (push-proof-log 'syntax (if-left-index) t)
    ;; (if H2 (implies PO (implies qPO Phi)) (true))
    (log-unnest-implies formula (if-left-index))
    ;; (if H2 (implies (and PO qPO) Phi) (true))
    (push-proof-log 'syntax (cons 1 (if-left-index)))
    (push-proof-log 'is-boolean (list* 2 1 (if-left-index)) t)
    ;; (if H2 (implies (if PO qPO (false)) Phi) (true))
    (let ((substitutions
           (pairlis (sublis-eq (pairlis po-args po-args-renames) args)
                    (cdr term))))
      (log-universal-subsumption
       (make-if po
                (make-series-of-quantification
                 'all po-args-renames
                 (sublis-eq (pairlis po-args po-args-renames) renamed-po))
                *false*)
       (mapcar #'(lambda (u) (make-= u (cdr (assoc-eq u substitutions))))
               po-args-renames)
       (cons 1 (if-left-index))))
    (log-renames (mapcar #'cons po-args-renames po-args)
                 (cons 1 (if-left-index)))
    (log-renames-unexpanded
     renamed-po orig-po (append (mapcar #'(lambda (u) u 2) po-args)
                                (cons 1 (if-left-index))))
    ;; At this point we have:
    ;; (if H2 (implies qPO Phi) (true))
    (push-proof-log 'use-axiom (cons 1 (if-left-index)) po-name t)
    (push-proof-log 'syntax (if-left-index))
    (push-proof-log 'if-true (if-left-index))
    ;; (if H2 (if Phi (true) (false)) (true))
    (push-proof-log 'syntax index t))
  )

;;; Recursively dive into the ``if-form'' machine, until we hit either
;;; (true) or a list of substitutions.
;;; At the top level, it logs conversion of (and PO H1) to PO.
;;; Note that PO is in "if" form.

(defvar *debugging-log-induction* nil)

(defun log-induction-phase-2-aux
    (formula vars machine po index h1 h2 measured-quants renames)
  (when *debug-checker*
    (push-proof-log 'marker index '(log-induction-phase-2-aux)))
  (when *debugging-log-induction*
    (format t "~%Machine: ~S~%" machine)
    (format t "~%PO: ~S~%" po)
    (format t "~%H1: ~S~%" h1))
  (cond ((true-p machine)
	 ;; (and (true) (true))
	 (push-proof-log 'syntax index)
	 (push-proof-log 'if-true index)
	 (push-proof-log 'if-true index)
	 
         ;; (true)
	 )
        ((and (if-p po) (if-p machine))
	 ;; (and (if test leftPO rightPO) (if test leftH1 rightH1))
         (push-proof-log 'case-analysis index 1)
	 ;; (if test
	 ;;     (and leftPO (if test leftH1 rightH1))
	 ;;     (and rightPO (if test leftH1 rightH1)))
         (push-proof-log 'look-up (cons 1 (cons 2 (if-left-index))) *true*)
         (push-proof-log 'if-true (cons 2 (if-left-index)))
	 ;; (if test
	 ;;     (and leftPO (if test leftH1 rightH1))
	 ;;     (and rightPO (if test leftH1 rightH1)))
	 ;; ***** test is not necessarilly known to be boolean!
	 (log-coerce-expr-for-boolean-or-bool-p
	  (if-test h1) (list* 1 2 (if-right-index))
	  (make-context-for-bool-p h1 (cons 2 (if-right-index))))
	 (log-look-up-false-for-coercion (list* 1 2 (if-right-index)))
         ;;(log-look-up-false (cons 1 (cons 2 (if-right-index))))
         (push-proof-log 'if-false (cons 2 (if-right-index)))
	 ;; (if test
	 ;;     (and leftPO leftH1 rightH1)
	 ;;     (and rightPO rightH1))
         (log-induction-phase-2-aux formula
				    vars
				    (if-left machine)
                                    (if-left po)
                                    (if-left-index)
                                    (if-left h1)
                                    h2
                                    measured-quants
                                    renames)
	 ;; (if test leftPO (and rightPO rightH1))
         (log-induction-phase-2-aux formula
				    vars
				    (if-right machine)
                                    (if-right po)
                                    (if-right-index)
                                    (if-right h1)
                                    h2
                                    measured-quants
                                    renames)
	 ;; (if test leftPO rightPO)
         ;; which is the same as PO
	 )
        ((if-p machine)
	 ;; (and PO (if test leftH1 rightH1))
         (push-proof-log 'case-analysis index 2)
	 ;; (if test (and PO leftH1) (and PO rightH1))
         (log-induction-phase-2-aux formula
				    vars
				    (if-left machine)
                                    po
                                    (if-left-index)
                                    (if-left h1)
                                    h2
                                    measured-quants
                                    renames)
	 ;; (if test PO (and PO rightH1))
         (log-induction-phase-2-aux formula
				    vars
				    (if-right machine)
                                    po
                                    (if-right-index)
                                    (if-right h1)
                                    h2
                                    measured-quants
                                    renames)
	 ;; (if test PO PO)
         (push-proof-log 'if-equal index)
	 ;; PO
	 )
	((if-p po)
	 ;; (and (if test leftPO rightPO) H1)
	 (push-proof-log 'case-analysis index 1)
	 ;; (if test (and leftPO H1) (and rightPO H1))
         (log-induction-phase-2-aux formula
				    vars
				    machine
                                    (if-left po)
                                    (if-left-index)
                                    (if-left h1)
                                    h2
                                    measured-quants
                                    renames)
	 ;; (if test leftPO (and rightPO H1))
         (log-induction-phase-2-aux formula
				    vars
				    machine
                                    (if-right po)
                                    (if-right-index)
                                    (if-right h1)
                                    h2
                                    measured-quants
                                    renames)
	 ;; (if test leftPO rightPO)
         ;; (push-proof-log 'if-equal index)
	 ;; PO
	 )
        ((all-p machine)
	 ;; (and po h1)
	 ;; where h1 is of the form (all (v) expr)
         (cond ((member-eq (all-var h1) measured-quants)
                (push-proof-log 'rename-universal (and-right-index)
                                (all-var h1) (all-var po))
                (push-proof-log 'syntax index)
                (push-proof-log 'is-boolean (if-left-index) t)
                (push-proof-log 'all-case-analysis index t)
		(log-coerce-expr-for-boolean-or-bool-p
		 (all-expr h1) (cons 2 (all-expr-index))
		 (make-context-for-bool-p
		  (make-all (all-vars h1) *true*) index))
                (push-proof-log 'syntax (all-expr-index) t)
                (log-induction-phase-2-aux formula
					   vars
					   (all-expr machine)
                                           (all-expr po)
                                           (all-expr-index)
                                           (subst-eq (all-var po) (all-var h1)
                                                     (all-expr h1))
                                           h2
                                           measured-quants
                                           (cons (cons (all-var h1)
                                                       (all-var po))
                                                 renames)))
               (t (log-coerce-expr-for-boolean-or-bool-p
		   po (and-left-index)
		   (make-context-for-bool-p (make-and po h1) index))
		  (push-proof-log 'remove-universal (and-left-index)
                                  (all-vars h1) t)
                  (push-proof-log 'syntax index)
                  (push-proof-log 'is-boolean (if-left-index) t)
                  (push-proof-log 'all-case-analysis index t)
		  (log-coerce-expr-for-boolean-or-bool-p
		   (all-expr h1) (cons 2 (all-expr-index))
		   (make-context-for-bool-p
		    (make-all (all-vars h1) *true*) index))
                  (push-proof-log 'syntax (all-expr-index) t)
		  ;; (all (v) (and PO expr))
                  (log-induction-phase-2-aux
		   formula vars
                   (all-expr machine) po (all-expr-index) (all-expr h1) h2
                   measured-quants renames)
		  ;; (all (v) PO)
                  (push-proof-log 'remove-universal index)
		  ;; *** Assumes PO is always Boolean.
                  (push-proof-log 'is-boolean index t))))
        ((and-p po)
	 (log-induction-phase-2-aux-and
	  formula vars machine po index h1 h2 measured-quants renames))
        ;; BUT because of merging, we might have a conjunction of
        ;; lists of substitutions
        ((and-p machine)
	 ;; (and leaf-po h1-is-and)
         (push-proof-log 'syntax index)
	 ;; (if leaf-po (if (and h1a h1b ...) (true) (false)) (false))
         (log-induction-phase-2-aux-aux
	  formula vars machine po (cons 1 (if-left-index)) h1 h2)
	 ;; (if leaf-po (if (true) (true) (false)) (false))
         (push-proof-log 'if-true (if-left-index))
         (push-proof-log 'is-boolean index t)

	 ;; leaf-po

	 )
        ;; List of substitutions
        (t
	 ;; (and leaf-po leaf-h1)
         (push-proof-log 'syntax index)
	 ;; (if po (if h1 (true) (false)) (false))
         (push-proof-log 'if-equal (if-left-index) po t)
	 ;; (if po
	 ;;     (if po
	 ;;         (if h1 (true) (false))
	 ;;         (if h1 (true) (false)))
	 ;;     (false))
	 (log-if-to-and-or
	  (make-if po (make-if h1 *true* *false*) (make-if h1 *true* *false*))
	  (if-left-index))
	 ;; (if po
	 ;;     (and (or (not po) (if h1 (true) (false)))
	 ;;          (or po (if h1 (true) (false))))
	 ;;     (false))
         (push-proof-log 'syntax (cons 1 (if-left-index)))
	 ;; (if po
	 ;;     (and (if (not po)
	 ;;              (true)
	 ;;              (if (if h1 (true) (false)) (true) (false)))
	 ;;          (or po (if h1 (true) (false))))
	 ;;     (false))
	 (log-remove-bool-coercion-from-if-test (list* 3 1 (if-left-index)))
	 ;; (if po
	 ;;     (and (if (not po)
	 ;;              (true)
	 ;;              (if h1 (true) (false)))
	 ;;          (or po (if h1 (true) (false))))
	 ;;     (false))
	 (push-proof-log 'syntax (list* 1 1 (if-left-index)))
	 ;; (if po
	 ;;     (and (if (if po (false) (true))
	 ;;              (true)
	 ;;              (if h1 (true) (false)))
	 ;;          (or po (if h1 (true) (false))))
	 ;;     (false))
         (push-proof-log 'case-analysis (cons 1 (if-left-index)) 1)
	 ;; (if po
	 ;;     (and (if po
	 ;;              (if (false) (true) (if h1 (true) (false)))
	 ;;              (if (true) (true) (if h1 (true) (false))))
	 ;;          (or po (if h1 (true) (false))))
	 ;;     (false))
         (push-proof-log 'if-false (list* 2 1 (if-left-index)))
         (push-proof-log 'if-true (list* 3 1 (if-left-index)))
	 ;; (if po
	 ;;     (and (if po
	 ;;              (if h1 (true) (false))
	 ;;              (true))
	 ;;          (or po (if h1 (true) (false))))
	 ;;     (false))
         (push-proof-log 'syntax (cons 1 (if-left-index)) t)
         ;; At this point, we have
         ;; (if PO
         ;;     (and (implies PO H1)
         ;;          (or PO (if H1 (true) (false))))
         ;;     (false))
         (push-proof-log 'look-up (list* 1 2 (if-left-index)) *true*)
	 ;; (if PO
         ;;     (and (implies PO H1)
         ;;          (or (true) (if H1 (true) (false))))
         ;;     (false))
	 (push-proof-log 'syntax (cons 2 (if-left-index)))
	 (push-proof-log 'if-true (cons 2 (if-left-index)))
	 ;; (if PO (and (implies PO H!) (true)) (false))
	 (push-proof-log 'syntax (if-left-index) t)
         ;; At this point, we have
         ;; (if PO
         ;;     (and (implies PO H1))
         ;;     (false))
         (push-proof-log 'if-equal (if-left-index) h2 t)
	 ;;
	 (log-if-to-and-or
	  (make-if h2
		   (list 'and (make-implies po h1))
		   (list 'and (make-implies po h1)))
	  (if-left-index))
         (push-proof-log 'syntax (cons 1 (if-left-index)))
         ;; At this point, we have
         ;; (if PO
         ;;     (and (if (not H2)
         ;;              (true)
         ;;              (if (and (implies PO H1)) (true) (false)))
         ;;          (or H2 (and (implies PO H1))))
         ;;     (false))
         (linearize-and-log-universal-instantiations
          (mapcar #'make-= (list-of-leading-universals h2)
                  (sublis-eq renames (cdr machine)))
          (list* 1 1 1 (if-left-index)))
         ;; At this point, we have
         ;; (if PO
         ;;     (and (if (not (if H2[vs] H2 (false)))
         ;;              (true)
         ;;              (if (and (implies PO H1)) (true) (false)))
         ;;          (or H2 (and (implies PO H1))))
         ;;     (false))
         (push-proof-log 'look-up (list* 2 1 1 1 (if-left-index)) *true*)
	 ;; the *true* in make-not is just a fake argument
	 ;; the value is irrelevant for
	 ;; log-remove-bool-coercion-from-inside-connective
	 (log-remove-bool-coercion-from-inside-connective
	  (make-not *true*) 1 (list* 1 1 (if-left-index)))
         ;; At this point, we have
         ;; (if PO
         ;;     (and (if (not H2[vs])
         ;;              (true)
         ;;              (if (and (implies PO H1)) (true) (false)))
         ;;          (or H2 (and (implies PO H1))))
         ;;     (false))
         (push-proof-log 'look-up (list* 1 1 1 1 (if-left-index)) *true*)
	 ;; (if PO
         ;;     (and (if (not (implies (true) Phi[vs]))
         ;;              (true)
         ;;              (if (and (implies PO H1)) (true) (false)))
         ;;          (or H2 (and (implies PO H1))))
         ;;     (false))
         (log-implies-to-or (list* 1 1 1 (if-left-index)))
	 ;; (if PO
         ;;     (and (if (not (or (not (true)) Phi[vs]))
         ;;              (true)
         ;;              (if (and (implies PO H1)) (true) (false)))
         ;;          (or H2 (and (implies PO H1))))
         ;;     (false))

	 (push-proof-log 'syntax (list* 1 1 1 1 (if-left-index)))
	 (push-proof-log 'if-true (list* 1 1 1 1 (if-left-index)))

	 (log-or-false 1 2 (list* 1 1 1 (if-left-index)))
	 ;; (if PO
         ;;     (and (if (not (or Phi[vs1]))
         ;;              (true)
         ;;              (if (and (implies PO H1)) (true) (false)))
         ;;          (or H2 (and (implies PO H1))))
         ;;     (false))
	 (log-or-1 (list* 1 1 1 (if-left-index)))
	 ;; (if PO
	 ;;     (and (if (not (if Phi[vs1] (true) (false)))
	 ;;              (true)
	 ;;              (if (and (implies PO H1)) (true) (false)))
	 ;;          (or H2 (and (implies PO H1))))
	 ;;     (false))

	 (push-proof-log 'syntax (list* 1 1 (if-left-index)))
	 
	 ;; (if PO
         ;;     (and (if (if (if Phi[vs1] (true) (false)) (false) (true))
         ;;              (true)
         ;;              (if (and (implies PO H1)) (true) (false)))
         ;;          (or H2 (and (implies PO H1))))
         ;;     (false))
	 (log-remove-bool-coercion-from-if-test (list* 1 1 (if-left-index)))
         (push-proof-log 'case-analysis (cons 1 (if-left-index)) 1)
	 ;; (if PO
	 ;;     (and (if Phi[vs1]
	 ;;              (if (false)
	 ;;                  (true)
	 ;;                  (if (and (implies PO H1)) (true) (false)))
	 ;;              (if (true)
	 ;;                  (true)
	 ;;                  (if (and (implies PO H1)) (true) (false))))
         ;;          (or H2 (and (implies PO H1))))
         ;;     (false))
         (push-proof-log 'look-up (list* 2 1 1 3 2 1 (if-left-index)) *true*)
         (log-implies-to-or (list* 1 1 3 2 1 (if-left-index)))
	 ;; (if PO
	 ;;     (and (if Phi[vs1]
	 ;;              (if (false)
	 ;;                  (true)
	 ;;                  (if (and (or (not PO) (true))) (true) (false)))
	 ;;              (if (true)
	 ;;                  (true)
	 ;;                  (if (and (implies PO H1)) (true) (false))))
         ;;          (or H2 (and (implies PO H1))))
         ;;     (false))
	 (push-proof-log 'syntax (list* 1 1 3 2 1 (if-left-index)))
	 (push-proof-log 'if-true (list* 3 1 1 3 2 1 (if-left-index)))
	 (push-proof-log 'if-equal (list* 1 1 3 2 1 (if-left-index)))
	 (push-proof-log 'syntax (list* 1 3 2 1 (if-left-index)))
	 (push-proof-log 'syntax (list* 1 3 2 1 (if-left-index)))
	 (push-proof-log 'if-true (list* 1 3 2 1 (if-left-index)))
	 (push-proof-log 'if-true (list* 1 3 2 1 (if-left-index)))
	 (push-proof-log 'if-true (list* 3 2 1 (if-left-index)))
         (push-proof-log 'if-equal (list* 2 1 (if-left-index)))
         (push-proof-log 'if-true (list* 3 1 (if-left-index)))
         (push-proof-log 'if-equal (cons 1 (if-left-index)))
	 ;; (if PO (and (true) (or H2 (and (implies PO H1)))) (false))
	 (push-proof-log 'look-up (list* 1 2 (if-left-index)) *true*)
	 (push-proof-log 'syntax (cons 2 (if-left-index)))
	 (push-proof-log 'if-true (cons 2 (if-left-index)))
	 ;; (if PO (and (true) (true)) (false))
	 (push-proof-log 'syntax (if-left-index))
	 (push-proof-log 'if-true (if-left-index))
	 (push-proof-log 'if-true (if-left-index))
         ;; At this point we have (if (m< mu[vs1] mu[vs]) (true) (false))
         ;; Assuming m< always returns a boolean, remove the boolean
         ;; coercion.
         (push-proof-log 'is-boolean index t)
         )))

(defun log-and-trues (n index)
  (cond ((> n 2)
	 (push-proof-log 'syntax index)
	 ;; (and (true) (and (true) ...))
	 (push-proof-log 'syntax index)
	 ;; (if (true) (if (and (true) ...) (true) (false)) (false))
	 (push-proof-log 'if-true index)
	 (push-proof-log 'is-boolean index t)
	 (log-and-trues (- n 1) index))
	((= n 2)
	 ;; (and (true) (true))
	 (push-proof-log 'syntax index)
	 (push-proof-log 'if-true index)
	 (push-proof-log 'if-true index)
	 ;; (true)
	 )
	(t
	 ;; (and (true)) or (and)
	 (push-proof-log 'syntax index)
	 (push-proof-log 'syntax index)
	 (push-proof-log 'if-true index)
	 (push-proof-log 'if-true index)
	 )))

(defun log-induction-phase-2-aux-and
    (formula vars machine po index h1 h2 measured-quants renames)
  ;; (and (and POL POR) (and H1L H1R))
  (cond
   ((and (all-p (and-left machine))
	 (not (member-eq (all-var (and-left h1)) measured-quants)))
    ;; (and PO (and (all (v) H1Lexpr) H1R)
    ;; Need to move quantifier out
    (log-coerce-expr-for-boolean-or-bool-p
     po (and-left-index) (make-context-for-bool-p (make-and po h1) index))
    (log-coerce-expr-for-boolean-or-bool-p
     (and-right h1) (cons 2 (and-right-index))
     (make-context-for-bool-p h1 (and-right-index)))
    ;; (and (if PO (true) (false))
    ;;      (and (all (v) H1Lexpr) (if H1R (true) (false)))))
    (push-proof-log 'remove-universal (cons 2 (and-right-index))
		    (all-vars (and-left h1)) t)
    ;; (and (if PO (true) (false)) (and (all (v) H1Lexpr) (all (v) H1R)))
    (push-proof-log 'syntax (and-right-index))
    (push-proof-log 'is-boolean (cons 2 (and-right-index)) t)
    (push-proof-log 'all-case-analysis (and-right-index) t)
    ;; (and (if PO (true) (false)) (all (v) (if H1Lexpr H1R (false))))
    (push-proof-log 'remove-universal (and-left-index)
		    (all-vars (and-left h1)) t)
    (push-proof-log 'syntax index)
    (push-proof-log 'is-boolean (if-left-index) t)
    ;; (if (all (v) PO)
    ;;     (all (v) (if H1Lexpr H1R (false)))
    ;;     (false))
    (push-proof-log 'all-case-analysis index t)
    ;; (all (v) (if PO (if H1Lexpr H1R (false)) (false)))
    (log-coerce-expr-in-boolean-context
     (make-context-for-bool-p (make-all (all-vars (and-left h1)) *true*) index)
     (cons 2 (all-expr-index)))
    (push-proof-log 'syntax (all-expr-index) t)
    ;; (all (v) (and PO (if H1Lexpr H1R (false))))
    (log-coerce-expr-in-boolean-context
     (make-context-for-bool-p
      (make-and po (make-if (all-expr (and-left h1)) (and-right h1) *false*))
      (all-expr-index))
     (list* 2 2 (all-expr-index)))
    (push-proof-log 'syntax (cons 2 (all-expr-index)) t)
    ;; (all (v) (and PO (and H1Lexpr H1R)))
    (log-induction-phase-2-aux
     formula vars
     (make-and (all-expr (and-left machine)) (and-right machine))
     po (all-expr-index)
     (make-and (all-expr (and-left h1)) (and-right h1))
     h2 measured-quants renames)
    ;; (all (v) PO)
    (push-proof-log 'remove-universal index)
    ;; *** Assumes PO is always Boolean.
    (push-proof-log 'is-boolean index t))
   ((and-p (and-left machine))
    ;; (and (and POL POR) (and (and H1LL H1LR) H1R))
    (log-associate-and-right h1 (and-right-index))
    (log-induction-phase-2-aux
     formula vars
     (make-and (and-left (and-left machine))
	       (make-and (and-right (and-left machine)) (and-right machine)))
     po
     index
     (make-and (and-left (and-left h1))
	       (make-and (and-right (and-left h1)) (and-right h1)))
     h2 measured-quants renames))
   (t
    ;; (and (and POL POR) (and H1L H1R))
    (log-pair-up-ands po h1 index)
    ;; (and (POL H1L) (POR H1R))
    (log-induction-phase-2-aux
     formula vars (and-left machine) (and-left po) (and-left-index)
     (and-left h1) h2 measured-quants renames)
    ;; (and POL (POR H1R))
    (log-induction-phase-2-aux
     formula vars (and-right machine) (and-right po) (and-right-index)
     (and-right h1) h2 measured-quants renames)
    ;; (and POL POR)
    )))


(defun log-induction-phase-2-aux-aux (formula vars machine po index h1 h2)
  (when *debug-checker*
    (push-proof-log 'marker index '(log-induction-phase-2-aux-aux)))
  (cond ((and-p machine)
	 ;; (and h1a h1b ...)
	 
         (loop for m in (cdr machine)
               for h in (cdr h1)
               for i = 1 then (+ i 1)
               do (log-induction-phase-2-aux-aux
		   formula vars m po (cons i index) h h2))

	 ;;
	 (log-and-trues (length (cdr machine)) index))
        (t
	 ;; h1
         (push-proof-log 'if-equal index po t)
	 (log-if-to-and-or (make-if po h1 h1) index)
	 ;; (and (or (not po) h1) (or po h1))
         (push-proof-log 'syntax (cons 1 index))
	 ;; (and (if (not po) (true) (if h1 (true) (false))) (or po h1))
	 (push-proof-log 'syntax (list* 1 1 index))
	 ;; (and (if (if po (false) (true)) (true) (if h1 (true) (false)))
	 ;;      (or po h1))
         (push-proof-log 'case-analysis (cons 1 index) 1)
         (push-proof-log 'if-false (list* 2 1 index))
         (push-proof-log 'if-true (list* 3 1 index))
	 ;; (and (if po (if h1 (true) (false)) (true))
	 ;;      (or po h1))
         (push-proof-log 'syntax (cons 1 index) t)
	 ;; (and (implies po h1) (or po h1))
         (push-proof-log 'look-up (list* 1 2 index) *true*)
	 (push-proof-log 'syntax (and-right-index))
	 (push-proof-log 'if-true (and-right-index))
	 (push-proof-log 'syntax index t)
	 ;; (and (implies po h1))
         (push-proof-log 'if-equal index h2 t)
	 ;; (if h2 (and (implies po h1)) (and (implies po h1)))
	 (log-if-to-and-or
	  (make-if h2
		   (list 'and (make-implies po h1))
		   (list 'and (make-implies po h1)))
	  index)
	 ;; (and (or (not h2) (and (implies po h1)))
	 ;;      (or h2 (and (implies po h1))))
         (push-proof-log 'syntax (cons 1 index))
	 ;; (and (if (not h2) (true) (if (and (implies po h1)) (true) (false)))
	 ;;      (or h2 (and (implies po h1))))
         (linearize-and-log-universal-instantiations
          (mapcar #'make-= (list-of-leading-universals h2) (cdr machine))
          (list* 1 1 1 index))
	 ;; (and (if (not (if H2[vs] H2 (false)))
	 ;;          (true)
	 ;;          (if (and (implies po h1)) (true) (false)))
	 ;;      (or h2 (and (implies po h1))))
         (push-proof-log 'look-up (list* 2 1 1 1 index) *true*)
	 ;; (and (if (not (if H2[vs1] (true) (false)))
	 ;;          (true)
	 ;;          (if (and (implies po h1)) (true) (false)))
	 ;;      (or h2 (and (implies po h1))))
	 (log-remove-bool-coercion-from-inside-connective
	  (make-not *true*) 1 (list* 1 1 index))
	 ;; (and (if (not H2[vs1])
	 ;;          (true)
	 ;;          (if (and (implies po h1)) (true) (false)))
	 ;;      (or h2 (and (implies po h1))))
         (push-proof-log 'look-up (list* 1 1 1 1 index) *true*)
	 ;; (and (if (not (implies (true) Phi[vs1]))
	 ;;          (true)
	 ;;          (if (and (implies po h1)) (true) (false)))
	 ;;      (or h2 (and (implies po h1))))
         (log-implies-to-or (list* 1 1 1 index))
	 ;; (and (if (not (or (not (true)) Phi[vs1]))
	 ;;          (true)
	 ;;          (if (and (implies po h1)) (true) (false)))
	 ;;      (or h2 (and (implies po h1))))
	 (push-proof-log 'syntax (list* 1 1 1 1 index))
	 (push-proof-log 'if-true (list* 1 1 1 1 index))
	 ;; (and (if (not (or (false) Phi[vs1]))
	 ;;          (true)
	 ;;          (if (and (implies po h1)) (true) (false)))
	 ;;      (or h2 (and (implies po h1))))
	 (push-proof-log 'syntax (list* 1 1 1 index))
	 (push-proof-log 'if-false (list* 1 1 1 index))
	 ;; (and (if (not (if Phi[vs1] (true) (false)))
	 ;;          (true)
	 ;;          (if (and (implies po h1)) (true) (false)))
	 ;;      (or h2 (and (implies po h1))))
	 (push-proof-log 'syntax (list* 1 1 index))
	 ;; (and (if (if (if Phi[vs1] (true) (false)) (false) (true))
	 ;;          (true)
	 ;;          (if (and (implies po h1)) (true) (false)))
	 ;;      (or h2 (and (implies po h1))))
	 (log-remove-bool-coercion-from-if-test (list* 1 1 index))
	 ;; (and (if (if Phi[vs1] (false) (true))
	 ;;          (true)
	 ;;          (if (and (implies po h1)) (true) (false)))
	 ;;      (or h2 (and (implies po h1))))
         (push-proof-log 'case-analysis (cons 1 index) 1)
	 ;; (and (if Phi[vs1]
	 ;;          (if (false)
	 ;;              (true)
	 ;;              (if (and (implies po h1)) (true) (false)))
	 ;;          (if (true)
	 ;;              (true)
	 ;;              (if (and (implies po h1)) (true) (false))))
	 ;;      (or h2 (and (implies po h1))))
         (push-proof-log 'look-up (list* 2 1 1 3 2 1 index) *true*)
	 ;; (and (if Phi[vs1]
	 ;;          (if (false)
	 ;;              (true)
	 ;;              (if (and (implies po (true))) (true) (false)))
	 ;;          (if (true)
	 ;;              (true)
	 ;;              (if (and (implies po h1)) (true) (false))))
	 ;;      (or h2 (and (implies po h1))))
         (log-implies-to-or (list* 1 1 3 2 1 index))
	 ;; (and (if Phi[vs1]
	 ;;          (if (false)
	 ;;              (true)
	 ;;              (if (and (or (not po) (true))) (true) (false)))
	 ;;          (if (true)
	 ;;              (true)
	 ;;              (if (and (implies po h1)) (true) (false))))
	 ;;      (or h2 (and (implies po h1))))
	 (log-or-true 2 2 (list* 1 1 3 2 1 index))
	 ;; (and (if Phi[vs1]
	 ;;          (if (false)
	 ;;              (true)
	 ;;              (if (and (true)) (true) (false)))
	 ;;          (if (true)
	 ;;              (true)
	 ;;              (if (and (implies po h1)) (true) (false))))
	 ;;      (or h2 (and (implies po h1))))
	 (push-proof-log 'syntax (list* 1 3 2 1 index))
	 (push-proof-log 'syntax (list* 1 3 2 1 index))
	 (push-proof-log 'if-true (list* 1 3 2 1 index))
	 (push-proof-log 'if-true (list* 1 3 2 1 index))
	 ;; (and (if Phi[vs1]
	 ;;          (if (false) (true) (if (true) (true) (false)))
	 ;;          (if (true)
	 ;;              (true)
	 ;;              (if (and (implies po h1)) (true) (false))))
	 ;;      (or h2 (and (implies po h1))))
         (push-proof-log 'if-true (list* 3 2 1 index))
         (push-proof-log 'if-equal (list* 2 1 index))
         (push-proof-log 'if-true (list* 3 1 index))
	 ;; (and (if Phi[vs1] (true) (true)
	 ;;      (or h2 (and (implies po h1))))
         (push-proof-log 'if-equal (cons 1 index))
	 ;; (and (true) (or h2 (and (implies po h1))))
	 (push-proof-log 'look-up (list* 1 2 index) *true*)
	 (push-proof-log 'syntax (and-right-index))
	 (push-proof-log 'if-true (and-right-index))
	 ;; (and (true) (true))
	 (push-proof-log 'syntax index)
	 (push-proof-log 'if-true index)
	 (push-proof-log 'if-true index)
	 )))

;;; Log the conversion of (and (and a1 a2) (and b1 b2)) to
;;; (and (and a1 b1) (and a2 b2))

(defun log-pair-up-ands (left right index)
  (let ((a1 (and-left left))
	(a2 (and-right left))
	(b1 (and-left right))
	(b2 (and-right right)))
    (push-proof-log 'if-equal index a1 t)
    ;; (if a1 (and (and a1 a2) (and b1 b2)) (and (and a1 a2) (and b1 b2)))
    (cond ((bool-p a1) (log-look-up-false (list* 1 1 (if-right-index))))
	  (t
	   (log-coerce-to-bool-inside-connective
	    left 1 (cons 1 (if-right-index)))
	   (log-look-up-false-for-coercion (list* 1 1 (if-right-index)))))
    (log-and-false 1 2 (cons 1 (if-right-index)))
    (log-and-false 1 2 (if-right-index))
    ;; (if a1 (and (and a1 a2) (and b1 b2)) (false))
    (push-proof-log 'look-up (cons 1 (cons 1 (if-left-index))) *true*)
    ;; (if a1 (and (and (true) a2) (and b1 b2)) (false))
    (push-proof-log 'syntax (cons 1 (if-left-index)))
    (push-proof-log 'if-true (cons 1 (if-left-index)))
    ;; (if a1 (and (if a2 (true) (false)) (and b1 b2)) (false))
    (log-remove-bool-coercion-from-inside-connective-strict
     (make-and (make-if a2 *true* *false*) right) 1 (if-left-index))
    ;; (if a1 (and a2 (and b1 b2)) (false))
    (push-proof-log 'if-equal (if-left-index) (and-left right) t)
    ;; (if a1 (if b1 (and a2 (and b1 b2)) (and a2 (and b1 b2))) (false))
    (cond ((bool-p b1) (log-look-up-false (list* 1 2 3 (if-left-index))))
	  (t
	   (log-coerce-to-bool-inside-connective
	    right 1 (list* 2 3 (if-left-index)))
	   (log-look-up-false-for-coercion (list* 1 2 3 (if-left-index)))))
    (log-and-false 1 2 (list* 2 3 (if-left-index)))
    (log-and-false 2 2 (list* 3 (if-left-index)))
    ;; (if a1 (if b1 (and a2 (and b1 b2)) (false)) (false))
    (push-proof-log 'look-up (list* 1 2 2 (if-left-index)) *true*)
    ;; (if a1 (if b1 (and a2 (and (true) b2)) (false)) (false))
    (push-proof-log 'syntax (list* 2 2 (if-left-index)))
    (push-proof-log 'if-true (list* 2 2 (if-left-index)))
    ;; (if a1 (if b1 (and a2 (if b2 (true) (false))) (false)) (false))
    (log-remove-bool-coercion-from-inside-connective-strict
     (make-and a2 (make-if b2 *true* *false*)) 2 (cons 2 (if-left-index)))
    ;; (if a1 (if b1 (and a2 b2) (false)) (false))
    (push-proof-log 'if-false (if-right-index) (make-and a2 b2) t)
    ;; (if a1 (if b1 (and a2 b2) (false)) (if (false) (and a2 b2) (false)))
    (push-proof-log 'case-analysis index 1 t)
    ;; (if (if a1 b1 (false)) (and a2 b2) (false))
    (log-coerce-if-test-to-bool index)
    (push-proof-log 'case-analysis (if-test-index) 1)
    (push-proof-log 'if-false (cons 3 (if-test-index)))
    ;; (if (if a1 (if b1 (true) (false)) (false)) (and a2 b2) (false))
    (push-proof-log 'syntax (if-test-index) t)
    ;; (if (and a1 b1) (and a2 b2) (false))
    (push-proof-log 'is-boolean (if-left-index))
    (push-proof-log 'syntax index t)
    ;; (and (and a1 b1) (and a2 b2))
    ))
  
	   

;;; log-induction-phase-3 logs inferences that convert
;;; (all vs (implies H2 Phi))
;;; to
;;; (all m (implies (all m1 (implies (m< m1 m)
;;;                                  (all vs1 (implies (= m1 (mu[vs1]))
;;;                                                    Phi[vs1]))))
;;;                 (all vs (implies (= m (mu[vs])) Phi))))
;;; vs is vars
;;; Phi is formula

(defun log-induction-phase-3 (formula h2 vars measure m m1 index)
  (when *debug-checker*
    (push-proof-log 'marker index '(log-induction-phase-3)))
  (let ((inner-index (append (mapcar #'(lambda (u) u 2) vars) index))
        (substitutions (mapcar #'cons vars (list-of-leading-universals h2))))
    (log-label inner-index m measure)
    (log-label (append (mapcar #'(lambda (u) u 2) vars)
		       (list* 1 2 inner-index))
	       m1
	       (sublis-eq substitutions measure))
    ;; We now have
    ;; (all vs (if (some m (= m (mu[vs])))
    ;;             (implies (all vs1 (if (some m1 (= m1 (mu[vs1])))
    ;;                                   (implies (m< (mu[vs1]) (mu[vs]))
    ;;                                            Phi[vs1])
    ;;                                   (true)))
    ;;                      Phi)
    ;;             (true)))
    (push-proof-log 'is-boolean (cons 2 inner-index))
    (push-proof-log 'syntax inner-index t)
    ;; We now have
    ;; (all vs (implies (some m (= m (mu[vs])))
    ;;                  (implies (all vs1 (if (some m1 (= m1 (mu[vs1])))
    ;;                                        (implies (m< (mu[vs1]) (mu[vs]))
    ;;                                                 Phi[vs1])
    ;;                                        (true)))
    ;;                           Phi)))
    (push-proof-log 'syntax inner-index)
    ;; We now have
    ;; (all vs (if (some m (= m (mu[vs])))
    ;;             (if (implies (all vs1 (if (some m1 (= m1 (mu[vs1])))
    ;;                                       (implies (m< (mu[vs1]) (mu[vs]))
    ;;                                                Phi[vs1]))
    ;;                                       (true)))
    ;;                          Phi)
    ;;                 (true)
    ;;                 (false))
    ;;             (true)))
    ;; inner-index points to the outer if

    (let ((muvs1 (sublis-eq substitutions measure))
    	  (phivs1 (sublis-eq substitutions formula))
	  (vs1 (list-of-leading-universals h2)))
      (log-all-uncase-analysis-2
       (make-if (make-some-single m (make-= m measure))
		(make-if (make-implies
			  (universally-quantify
			   vs1
			   (make-if (make-some-single m1 (make-= m1 muvs1))
				    (make-implies (make-m< muvs1 measure)
						  phivs1)
				    *true*))
			  formula)
			 *true*
			 *false*)
    		*true*)
       inner-index))

        
    ;; We now have:
    ;; (all vs
    ;;      (all m (if (= m (mu[vs]))
    ;;                 (implies (all vs1 (if (some m1 (= m1 (mu[vs1])))
    ;;                                       (implies (m< (mu[vs1]) (mu[vs]))
    ;;                                                Phi[vs1])
    ;;                                       (true)))
    ;;                          Phi)
    ;;                 (true))))
    (let ((idx (append (mapcar #'(lambda (u) u 2) vars)
		       (list* 1 2 2 inner-index))))
      (push-proof-log 'is-boolean (cons 2 idx)))
    ;; We now have:
    ;; (all vs
    ;;      (all m (if (= m (mu[vs]))
    ;;                 (implies
    ;;                   (all vs1 (if (some m1 (= m1 (mu[vs1])))
    ;;                                (if (implies (m< (mu[vs1]) (mu[vs]))
    ;;                                             Phi[vs1])
    ;;                                    (true)
    ;;                                    (false))
    ;;                                (true)))
    ;;                   Phi)
    ;;                 (true))))
    
    (let ((muvs1 (sublis-eq substitutions measure))
    	  (phivs1 (sublis-eq substitutions formula))
	  (vs1 (list-of-leading-universals h2)))
      (log-all-uncase-analysis-2
       (make-if (make-some-single m1 (make-= m1 muvs1))
		(make-if (make-implies (make-m< muvs1 measure) phivs1)
			 *true*
			 *false*)
		*true*)
       (append (mapcar #'(lambda (u) u 2) vars) (list* 1 2 2 inner-index))))

    ;; We now have:
    ;; (all vs
    ;;      (all m (if (= m (mu[vs]))
    ;;                 (implies
    ;;                   (all vs1
    ;;                        (all m1 (if (= m1 (mu[vs1]))
    ;;                                    (implies (m< (mu[vs1]) (mu[vs]))
    ;;                                             Phi[vs1])
    ;;                                    (true))))
    ;;                   Phi)
    ;;                 (true))))
    (push-proof-log 'look-up
                    (list* 1 1 2 2 (append (mapcar #'(lambda (u) u 2) vars)
                                           (list* 1 2 2 inner-index)))
                    m1)
    (push-proof-log 'look-up
                    (list* 2 1 2 2 (append (mapcar #'(lambda (u) u 2) vars)
                                           (list* 1 2 2 inner-index)))
                    m)
    ;; We now have:
    ;; (all vs
    ;;      (all m (if (= m (mu[vs]))
    ;;                 (implies
    ;;                   (all vs1
    ;;                        (all m1 (if (= m1 (mu[vs1]))
    ;;                                    (implies (m< m1 m) Phi[vs1])
    ;;                                    (true))))
    ;;                   Phi)
    ;;                 (true))))
    (log-move-universal-out (length vars) index)
    (log-move-universal-out (length vars) (list* 1 2 2 inner-index))
    ;; We now have:
    ;; (all m
    ;;      (all vs (if (= m (mu[vs]))
    ;;                  (implies
    ;;                    (all m1
    ;;                         (all vs1 (if (= m1 (mu[vs1]))
    ;;                                      (implies (m< m1 m) Phi[vs1])
    ;;                                      (true))))
    ;;                    Phi)
    ;;                  (true))))
    (push-proof-log 'is-boolean (list* 2 2 inner-index))
    (push-proof-log 'syntax (cons 2 inner-index) t)
    ;; We now have:
    ;; (all m
    ;;      (all vs (implies (= m (mu[vs]))
    ;;                       (implies
    ;;                         (all m1
    ;;                              (all vs1 (if (= m1 (mu[vs1]))
    ;;                                           (implies (m< m1 m) Phi[vs1])
    ;;                                           (true))))
    ;;                         Phi))))
    (log-unnest-implies formula (cons 2 inner-index))
    (let ((muvs1 (sublis-eq substitutions measure))
    	  (phivs1 (sublis-eq substitutions formula))
	  (vs1 (list-of-leading-universals h2)))
      (let ((left (make-= m measure))
	    (right (make-all-single
		    m1
		    (universally-quantify
		     vs1
		     (make-if (make-= m1 muvs1)
			      (make-implies (make-m< m1 m) phivs1)
			      *true*)))))
	(log-use-axiom-as-rewrite
	 (make-and left right) 'and.commutative
	 (list (make-= '|)X| left) (make-= '|)Y| right))
	 (list* 1 2 inner-index))))
    ;; (push-proof-log 'commute-and (list* 1 2 inner-index))
    ;; We now have:
    ;; (all m
    ;;      (all vs (implies
    ;;                (and (all m1
    ;;                          (all vs1 (if (= m1 (mu[vs1]))
    ;;                                       (implies (m< m1 m) Phi[vs1])
    ;;                                       (true))))
    ;;                     (= m (mu[vs])))
    ;;                Phi)))
    (push-proof-log 'syntax (list* 1 2 inner-index))
    (push-proof-log 'syntax (cons 2 inner-index))
    ;; We now have:
    ;; (all m
    ;;      (all vs (if (if (all m1
    ;;                           (all vs1 (if (= m1 (mu[vs1]))
    ;;                                        (implies (m< m1 m) Phi[vs1])
    ;;                                        (true))))
    ;;                      (if (= m (mu[vs])) (true) (false))
    ;;                      (false))
    ;;                  (if Phi (true) (false))
    ;;                  (true))))
    (push-proof-log 'case-analysis (cons 2 inner-index) 1)
    (push-proof-log 'if-false (list* 3 2 inner-index))
    ;; We now have:
    ;; (all m
    ;;      (all vs (if (all m1
    ;;                       (all vs1 (if (= m1 (mu[vs1]))
    ;;                                    (implies (m< m1 m) Phi[vs1])
    ;;                                    (true))))
    ;;                  (if (if (= m (mu[vs])) (true) (false))
    ;;                      (if Phi (true) (false))
    ;;                      (true))
    ;;                  (true))))

    ;; (repeat-log-all-case-analysis-1 (length vars) (all-expr-index))

    (let ((displacement (mapcar #'(lambda (u) u 2) vars))
	  (vs1 (list-of-leading-universals h2))
	  (muvs1 (sublis-eq substitutions measure))
	  (phivs1 (sublis-eq substitutions formula)))
      (repeat-log-all-case-analysis-1
       (make-if (make-all (list m1)
			  (make-series-of-quantification
			   'all vs1
			   (make-if (make-= m1 muvs1)
				    (make-implies (make-m< m1 m) phivs1)
				    *true*)))
		(make-if (make-if (make-= m measure) *true* *false*)
			 (make-if formula *true* *false*)
			 *true*)
		*true*)
       (reverse vars) nil displacement (all-expr-index)))
    
    
    (log-remove-universals (length vars) (cons 3 (all-expr-index)))
    ;; We now have:
    ;; (all m
    ;;      (if (all m1 (all vs1 (if (= m1 (mu[vs1]))
    ;;                               (implies (m< m1 m) Phi[vs1])
    ;;                               (true))))
    ;;          (all vs (if (if (= m (mu[vs])) (true) (false))
    ;;                      (if Phi (true) (false))
    ;;                      (true))
    ;;          (true)))
    (push-proof-log 'is-boolean (cons 2 (all-expr-index)))
    (push-proof-log 'syntax (all-expr-index) t)
    ;; (all m
    ;;    (implies
    ;;          (all m1 (all vs1 (if (= m1 (mu[vs1]))
    ;;                               (implies (m< m1 m) Phi[vs1])
    ;;                               (true))))
    ;;          (all vs (if (if (= m (mu[vs])) (true) (false))
    ;;                      (if Phi (true) (false))
    ;;                      (true)))))
    ;; The use of (list* 2 2 inner-index) just happens to work.
    ;; Should really be (append inner-index '(2 2))
    (log-remove-bool-coercion-from-if-test (list* 2 2 inner-index))
    (push-proof-log 'syntax (list* 2 2 inner-index) t)
    ;; We now have:
    ;; (all m (implies (all m1 (all vs1 (if (= m1 (mu[vs1]))
    ;;                                      (implies (m< m1 m) Phi[vs1])
    ;;                                      (true))))
    ;;                 (all vs (implies (= m (mu[vs])) Phi))))
    (push-proof-log 'is-boolean
		    (cons 2 (append (mapcar #'(lambda (u) u 2) vars)
				    (list* 2 1 2 index))))
    (push-proof-log 'syntax
                    (append (mapcar #'(lambda (u) u 2) vars)
                            (list* 2 1 2 index))
		    t)
    (log-unnest-implies (sublis-eq substitutions formula)
			(append (mapcar #'(lambda (u) u 2) vars)
				(list* 2 1 2 index)))
    (let* ((muvs1 (sublis-eq substitutions measure))
	   (left (make-= m1 muvs1))
	   (right (make-m< m1 m)))
      (log-use-axiom-as-rewrite
       (make-and left right) 'and.commutative
       (list (make-= '|)X| left) (make-= '|)Y| right))
       (cons 1 (append (mapcar #'(lambda (u) u 2) vars) (list* 2 1 2 index)))))
    ;; (push-proof-log 'commute-and
    ;;                (cons 1 (append (mapcar #'(lambda (u) u 2) vars)
    ;;                                (list* 2 1 2 index))))
    ;; We now have:
    ;; (all m (implies (all m1
    ;;                      (all vs1 (implies (and (m< m1 m) (= m1 (mu[vs1])))
    ;;                                        Phi[vs1])))
    ;;                 (all vs (implies (= m (mu[vs])) Phi))))
    (push-proof-log 'syntax
                    (cons 1 (append (mapcar #'(lambda (u) u 2) vars)
                                    (list* 2 1 2 index))))
    (push-proof-log 'syntax
                    (append (mapcar #'(lambda (u) u 2) vars)
                            (list* 2 1 2 index)))
    ;; We now have:
    ;; (all m (implies (all m1
    ;;                      (all vs1 (if (if (m< m1 m)
    ;;                                       (if (= m1 (mu[vs1]))
    ;;                                           (true)
    ;;                                           (false))
    ;;                                       (false))
    ;;                                   (if Phi[vs1] (true) (false))
    ;;                                   (true))))
    ;;                 (all vs (implies (= m (mu[vs])) Phi))))
    (push-proof-log 'case-analysis
                    (append (mapcar #'(lambda (u) u 2) vars)
                            (list* 2 1 2 index))
		    1)
    (push-proof-log 'if-false
     (cons 3 (append (mapcar #'(lambda (u) u 2) vars) (list* 2 1 2 index))))
    ;; We now have:
    ;; (all m (implies (all m1
    ;;                      (all vs1 (if (m< m1 m)
    ;;                                   (if (if (= m1 (mu[vs1]))
    ;;                                           (true)
    ;;                                           (false))
    ;;                                       (if Phi[vs1] (true) (false))
    ;;                                       (true))
    ;;                                   (true))))
    ;;                 (all vs (implies (= m (mu[vs])) Phi))))
    
    ;; (repeat-log-all-case-analysis-1 (length vars) (list* 2 1 2 index))

    (let ((displacement (mapcar #'(lambda (u) u 2) vars))
	  (vs1 (list-of-leading-universals h2))
	  (muvs1 (sublis-eq substitutions measure))
	  (phivs1 (sublis-eq substitutions formula)))
      (repeat-log-all-case-analysis-1
       (make-if (make-m< m1 m)
		(make-if (make-if (make-= m1 muvs1) *true* *false*)
			 (make-if phivs1 *true* *false*)
			 *true*)
		*true*)
       (reverse vs1) nil displacement (list* 2 1 2 index)))
    
    (log-remove-universals (length vars) (list* 3 2 1 2 index))
    ;; We now have:
    ;; (all m (implies (all m1
    ;;                      (if (m< m1 m)
    ;;                          (all vs1 (if (if (= m1 (mu[vs1]))
    ;;                                           (true)
    ;;                                           (false))
    ;;                                       (if Phi[vs1] (true) (false))
    ;;                                       (true)))
    ;;                          (true)))
    ;;                 (all vs (implies (= m (mu[vs])) Phi))))
    (log-remove-bool-coercion-from-if-test
     (append (mapcar #'(lambda (u) u 2) vars) (list* 2 2 1 2 index)))
    (push-proof-log 'syntax
                    (append (mapcar #'(lambda (u) u 2) vars)
                            (list* 2 2 1 2 index))
		    t)
    (push-proof-log 'is-boolean (list* 2 2 1 2 index))
    (push-proof-log 'syntax (list* 2 1 2 index) t)
    ;; We now have:
    ;; (all m (implies (all m1 (implies (m< m1 m)
    ;;                                  (all vs1 (implies (= m1 (mu[vs1]))
    ;;                                                    Phi[vs1]))))
    ;;                 (all vs (implies (= m (mu[vs])) Phi))))

    ))


    ;;      (all vs (if (all m1
    ;;                       (all vs1 (if (= m1 (mu[vs1]))
    ;;                                    (implies (m< m1 m) Phi[vs1])
    ;;                                    (true))))
    ;;                  (if (if (= m (mu[vs])) (true) (false))
    ;;                      (if Phi (true) (false))
    ;;                      (true))
    ;;                  (true)))

(defun repeat-log-all-case-analysis-1
    (formula reversed-vars processed-vars displacement base-index)
  (unless (null displacement)
    ;; (all () (if test left right))
    (let ((index (append (cdr displacement) base-index))
	  (left (make-series-of-quantification
		  'all processed-vars (if-left formula)))
	  (right (make-series-of-quantification
		  'all processed-vars (if-right formula))))
      (log-all-case-analysis-1
       (make-all (list (car reversed-vars))
		 (make-if (if-test formula) left right))
       index)
      ;; (if test (all (trailingvars) left) (all (trailingvars) right))
      (repeat-log-all-case-analysis-1
       formula
       (cdr reversed-vars)
       (cons (car reversed-vars) processed-vars)
       (cdr displacement)
       base-index)))
  )

(defun log-remove-universals (n index)
  (unless (zerop n)
    (log-remove-universals (- n 1) (all-expr-index))
    (push-proof-log 'remove-universal index)
    ;; result is assumed to be Boolean
    (push-proof-log 'is-boolean index t)))

;;; This is like log-flip-universals except it moves a quantifier out
;;; instead of in.

(defun log-move-universal-out (number-of-vars index)
  (unless (zerop number-of-vars)
    (log-move-universal-out (- number-of-vars 1) (all-expr-index))
    (push-proof-log 'flip-universals index)))

;;; Convert ((tests1 hyp1) (tests2 hyp2) ...) to IF form.
(defun if-form-machine (machine)
  (cond ((null machine) nil)
        (t (multiple-value-bind (formula rest-machine)
             (if-form-machine-aux (first (car machine))
                                  1
                                  (second (car machine))
                                  (cdr machine))
             (when (null rest-machine) formula)))))

(defun if-form-machine-aux (tests depth hyp machine)
  (cond ((null tests) (values (or hyp *true*) machine))
        (t (let (left right rest-machine)
	     ;; recur to make left
             (multiple-value-setq
	      (left rest-machine)
	      (if-form-machine-aux (cdr tests) (+ depth 1) hyp machine))
	     ;; recur to make right
             (multiple-value-setq
	      (right rest-machine)
	      (if-form-machine-aux (nthcdr depth (first (car rest-machine)))
				   (+ depth 1)
				   (second (car rest-machine))
				   (cdr rest-machine)))
	     ;; make (if first-test left right)
             (values (make-if (car tests) left right) rest-machine)))))

	 
;;; Log transformation of (implies H1 formula) to
;;; the result of apply-induction-template-to-formula.

(defun log-apply-machine (machine template vars formula index bool-p)
  (cond ((= (length template) 1)
	 (let ((h1 (substitute-induction-pattern-in-machine
		    machine vars formula)))
	   (when (and-p h1)
	     (really-flatten-ands h1 (implies-left-index)))))
	(t (log-cases-if-hypothesis machine vars formula index bool-p))))

(defun log-cases-if-hypothesis (machine vars formula index bool-p)
  (when *debug-checker*
    (push-proof-log 'marker index '(log-cases-if-hypothesis)))
  (cond
   ((if-p machine)
    ;; (implies (if t1 H1l H1r) Phi)
    (push-proof-log 'case-analysis index 1)
    ;; (if t1 (implies H1l Phi) (implies H1r Phi))
    (log-cases-if
     (make-if (if-test machine)
	      (make-implies
	       (substitute-induction-pattern-in-machine
		(if-left machine) vars formula)
	       formula)
	      (make-implies
	       (substitute-induction-pattern-in-machine
		(if-right machine) vars formula)
	       formula))
     nil
     index)
    ;; (and (implies t1 (implies H1l Phi)) (implies (not t1) (implies H1r Phi)))
    (let ((left-test
	   (if (and-p (if-test machine))
	       (cdr (if-test machine))
	     (list (if-test machine)))
	   )
	  (right-test
	   (cond ((not-p (if-test machine))
		  (log-not-not (cons 1 (and-right-index)))
		  ;; (and (implies t1 (implies H1l Phi)
		  ;;      (implies (if t1test (true) (false))
		  ;;               (implies H1r Phi)))
		  (push-proof-log 'syntax (and-right-index))
		  ;; (and (implies t1 (implies H1l Phi))
		  ;;      (if (if t1test (true) (false))
		  ;;          (if (implies H1r Phi) (true) (false))
		  ;;          (true)))
		  (log-remove-bool-coercion-from-if-test (and-right-index))
		  (push-proof-log 'syntax (and-right-index) t)
		  ;; (and (implies t1 (implies H1l Phi))
		  ;;      (implies t1test (implies H1r Phi)))
		  (if (and-p (not-expr (if-test machine)))
		      (cdr (not-expr (if-test machine)))
		    (list (not-expr (if-test machine)))))
		 (t (list (make-not (if-test machine))))))
	  ;; (and (implies left-test (implies H1l Phi))
	  ;;      (implies right-test (implies H1r Phi)))
	  ;; left is result of processing (implies H1l Phi)
	  (left-list
	   (log-cases-if-hypothesis
	    (if-left machine) vars formula (cons 2 (and-left-index))
	    (make-context-for-bool-p
	     (make-implies
	      (if-test machine)
	      (make-implies
		(substitute-induction-pattern-in-machine
		 (if-left machine) vars formula)
		formula))
	     (and-left-index))))
	  ;; right is result of processing (implies H1r Phi)
          (right-list
	   (log-cases-if-hypothesis
	    (if-right machine) vars formula (cons 2 (and-right-index))
	    (make-context-for-bool-p
	     (make-implies
	      (if (not-p (if-test machine))
		   (not-expr (if-test machine))
		 (make-not (if-test machine)))
	      (make-implies
		(substitute-induction-pattern-in-machine
		 (if-left machine) vars formula)
		formula))
	     (and-right-index)))))
      ;; (and (implies left-test left)
      ;;      (implies right-test right))
      (let ((left-result
	     (cond
	      ((= (length left-list) 1)
	       ;; left-list is ((hyp)),
	       ;; left is (implies hyp Phi),
	       ;; (and (implies left-test (implies hyp Phi))
	       ;;      (implies right-test right))
	       (list
		(log-cases-if-hypothesis-aux
		 left-test (car left-list) formula (and-left-index)))
	       ;; (and (implies (and left-test hyp) Phi)
	       ;;      (implies right-test right))
	       )
	      (t
	       ;; left-list is (hyp1 hyp2 ...)
	       ;; left is (and (implies hyp1 Phi) (implies hyp2 Phi) ...)
	       ;; (and (implies left-test (and (implies hyp1 Phi) ...))
	       ;;      (implies right-test Phi))
	       (log-cases-implies left-list (and-left-index))
	       ;; (and (and (implies left-test (implies hyp1 Phi))
	       ;;           (implies left-test (implies hyp2 Phi))
	       ;;             ...)
	       ;;      (implies right-test right))
	       (loop for l in left-list
		     for i = 1 then (+ i 1)
		     collect (log-cases-if-hypothesis-aux
			      left-test l formula (cons i (and-left-index))))
	       ;; (and (and (implies (and left-test hyp1) Phi)
	       ;;           (implies (and left-test hyp2) Phi)
	       ;;            ...)
	       ;;      (implies right-test right))
	       )))
	    (right-result
	     (cond
	      ((= (length right-list) 1)
	       (list
		(log-cases-if-hypothesis-aux
		 right-test (car right-list) formula (and-right-index))))
	      (t
	       (log-cases-implies right-list (and-right-index))
	       (loop for r in right-list
		     for i = 1 then (+ i 1)
		     collect
		     (log-cases-if-hypothesis-aux
		      right-test r formula (cons i (and-right-index))))
	       ;; (and (and (implies (and left-test hyp1) Phi)
	       ;;           (implies (and left-test hyp2) Phi)
	       ;;            ...)
	       ;;      (and (implies (and right-test rhyp1) Phi)
	       ;;           (implies (and right-test rhyp2) Phi)
	       ;;            ...))
	       ))))
	;; Log the AND unexpansions performed by
	;; apply-induction-template-to-formula.
	;; Seems to expect (and (implies ...) (implies ...))
	(really-flatten-ands
	 (make-and
	  (if (= (length left-result) 1)
	      (let ((h (append ; left-test
			nil
			       (car left-result))))
		(make-implies (if (> (length h) 1) (cons 'and h) (car h))
			      formula))
	    (cons
	     'and
	     (loop for hyps in left-result
		   collect
		   (let ((h (append ; left-test
			     nil
			     hyps)))
		     (make-implies (if (> (length h) 1) (cons 'and h) (car h))
				   formula)))))
	  (if (= (length right-result) 1)
	      (let ((h (append ; right-test
			nil
			(car right-result))))
		(make-implies (if (> (length h) 1) (cons 'and h) (car h))
			      formula))
	    (cons
	     'and
	     (loop for hyps in right-result
		   collect
		   (let ((h (append ; right-test
			     nil
			     hyps)))
		     (make-implies (if (> (length h) 1) (cons 'and h) (car h))
				   formula))))))
	 index)
	;; (and (implies (and left-test hyp1) Phi)
	;;      (implies (and left-test hyp2) Phi)
	;;      ...
	;;      (implies (and right-test rhyp1) Phi)
	;;      (implies (and right-test rhyp2) Phi)
	;;      ...)
	(append left-result right-result))
      ;;
      ))
   ((true-p machine)
    ;; (implies (true) Phi)
    (push-proof-log 'syntax index)
    (push-proof-log 'if-true index)
    ;; (if Phi (true) (false))
    (when (or (bool-p formula) bool-p) ;; almost certain but just in case
      (log-remove-coercion-for-boolean-or-bool-p formula index bool-p))
    '(()))
   ((and (consp machine) (eq (car machine) *induction-pattern*))
    ;; (P ...)
    (let ((substs (mapcar #'cons vars (cdr machine))))
      (list (list (sublis-eq substs formula)))))
   ((and-p machine)
    (list (mapcar #'(lambda (u)
		      (substitute-induction-pattern-in-machine u vars formula))
		  (cdr machine))))
   (t (list (list (substitute-induction-pattern-in-machine
		   machine vars formula))))
   ;; (t (list (list machine)))
   ))



(defun log-cases-implies (hyp-list index)
  (when *debug-checker*
    (push-proof-log 'marker index '(log-cases-implies)))
  ;; hyp-list is a list of lists of conjuncts
  ;; (implies test (and (implies hyp1 Phi) (implies hyp2 Phi) ...))
  (push-proof-log 'syntax index)
  (push-proof-log 'is-boolean (if-left-index) t)
  ;; (if test (and (implies hyp1 Phi) (implies hyp2 Phi) ...) (true))
  (log-convert-true-to-and (length hyp-list) (if-right-index))
  ;; (if test
  ;;     (and (implies hyp1 Phi) (implies hyp2 Phi) ...)
  ;;     (and (true) (true) ...))
  (push-proof-log 'case-analysis index 0 t)
  ;; (and (if test (implies hyp1 Phi) (true))
  ;;      (if test (implies hyp2 Phi) (true))
  ;;      ...)
  (loop for i from 1 to (length hyp-list)
        do
	(progn (push-proof-log 'is-boolean (list* 2 i index))
	       (push-proof-log 'syntax (cons i index) t)))
  ;; (and (implies test (implies hyp1 Phi))
  ;;      (implies test (implies hyp2 Phi))
  ;;      ...)
  )

;;; test is a list of conjuncts
;;; hyp is a list of conjuncts

(defun log-cases-if-hypothesis-aux (test hyp formula index)
  (when *debug-checker*
    (push-proof-log 'marker index '(log-cases-if-hypothesis-aux)))
  (cond
   ((null hyp) test)
   (t
    ;; (implies test (implies (and hyp) Phi))
    (log-unnest-implies formula index)
    ;; (implies (and test (and hyp)) Phi)
    ;; Log the AND unexpansions performed by make-induction-lemma-case.
    (let ((result
	   (really-flatten-ands
	    (list 'and
		  (if (= (length test) 1)
		      (car test)
		    (cons 'and test))
		  (if (= (length hyp) 1)
		      (car hyp)
		    (cons 'and hyp)))
	    (implies-left-index))))
      (cond ((and-p result) (cdr result))
	    ((and (if-p result) (true-p (if-left result))
		  (false-p (if-right result)) (bool-p (if-test result)))
	     (push-proof-log 'is-boolean (implies-left-index) t)
	     (list (if-test result)))
	    (t (list result)))))))

(defun substitute-induction-pattern-in-machine (machine vars formula)
  (cond ((consp machine)
	 (cond ((eq (car machine) *induction-pattern*)
		(let ((subst (mapcar #'cons vars (cdr machine))))
		  (sublis-eq subst formula)))
	       (t
		(cons (car machine)
		      (loop for m in (cdr machine)
			    collect
			    (substitute-induction-pattern-in-machine
			     m vars formula))))))
	(t machine)))

