
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


;;; ========== Data Structures for Egraph and Tableau ==========


;;; --------------- Flags ---------------

;;; Set to T if inconsistency caused by assumptions detected.
(defvar *inconsistent* nil)

;;; Simplifier options.
(defvar *simplifier-substitutes-equalities-flag* t)
(defvar *simplifier-instantiates-variables-flag* t)

;;; --------------- End of Flags ---------------


;;; --------------- Globals ---------------

;;; Needed so that operations can be undone in a LIFO manner.
(defvar *undo-stack* nil)

;;; --------------- End of Globals ---------------



;;; =============== Data Structures for the Egraph ===============


;;; Structure for an e-node, representing a well formed expression.

(defstruct (e-node
	    (:constructor
	     make-e-node
	     (ecar ecdr size attribute type tableau-entry chain-rules
		   &optional root eqclass samecar samecdr forbid e-pred
		   aux-pred back witness-link witness-info operation
		   variable not-shifted grules-applied-p))
	    :named :predicate)
  ecar                ;an e-node
  ecdr                ;an aux-node
  size                ;size of equivalence class (accurate for root)
  attribute           ;expression that it represents
  type                ;*bool-node*, *int-node* or T
  tableau-entry       ;an array of size 4
  chain-rules         ;an array of size 1
  root                ;an e-node (root of equivalence class)
  eqclass             ;an e-node (pointer to next in equivalence class)
  samecar             ;an e-node (with same ecar)
  samecdr             ;an e-node (with same ecdr)
  forbid              ;nil or an fnode
  e-pred              ;nil or an e-node
  aux-pred            ;nil or an aux-node
  back                ;nil, an e-node, or aux-node (for temporary marking)
  witness-link        ;nil or an e-node
  witness-info        ;nil or justification for merge
  operation           ;nil or function applied if expression is application
  variable            ;nil or T if expression is a variable
  not-shifted         ;nil or T if integer inequality not shifted
  grules-applied-p    ;list of grules applied
  )

;;; Structure for an auxiliary node, representing arguments of
;;; function application.

(defstruct (aux-node
	    (:constructor
	     make-aux-node
	     (ecar ecdr size &optional root eqclass samecar samecdr e-pred
		   aux-pred back))
	    :named :predicate)
  ecar       ;an e-node
  ecdr       ;an aux-node
  size       ;size of eqclass
  root       ;an aux-node
  eqclass    ;an aux-node
  samecar    ;an-aux-node
  samecdr    ;an aux-node
  e-pred     ;nil or an e-node
  aux-pred   ;nil or an aux-node
  back       ;nil, an e-node, or aux-node (for temporary marking)
  )

;;; Construct an e-node with appropriate initial values.
(defun make-an-e-node (its-ecar its-ecdr its-attribute its-type)
  (let ((new-node (make-e-node its-ecar its-ecdr 1 its-attribute its-type
                               (make-array '(4) :initial-element nil)
                               (make-array '(2) :initial-element nil))))
    ;; Set root, eqclass, samecar and samecdr to itself.
    (setf (e-node-root new-node) new-node)
    (setf (e-node-eqclass new-node) new-node)
    (setf (e-node-samecar new-node) new-node)
    (setf (e-node-samecdr new-node) new-node)))

;;; Construct an auxiliary with appropriate initial values.
(defun make-auxiliary-node (its-ecar its-ecdr)
  (let ((new-node (make-aux-node its-ecar its-ecdr 1)))
    ;; Set root, eqclass, samecar and samecdr to itself.
    (setf (aux-node-root new-node) new-node)
    (setf (aux-node-eqclass new-node) new-node)
    (setf (aux-node-samecar new-node) new-node)
    (setf (aux-node-samecdr new-node) new-node)))

;;; Return the first argument node given an e-node representing a
;;; function application.
(defsubst arg-1-node (node)
  (aux-node-ecar (e-node-ecdr node)))

;;; Return the second argument node given an e-node representing a
;;; function application.
(defsubst arg-2-node (node)
  (aux-node-ecar (aux-node-ecdr (e-node-ecdr node))))

;;; Return the third argument node given an e-node representing a
;;; function application.
(defsubst arg-3-node (node)
  (aux-node-ecar (aux-node-ecdr (aux-node-ecdr (e-node-ecdr node)))))



;;; Macros to construct a list from a circular list of nodes given the link
;;; name and a starting node. The second macro excludes the starting node.

(defmacro make-node-list (link node)
  (let ((next (gensym))
	(lst (gensym)))
    `(do ((,next (,link ,node) (,link ,next))
	  (,lst nil (cons ,next ,lst)))
	 ((eq ,next ,node) (cons ,next ,lst)))))

(defmacro make-node-list-excluding (link node)
  (let ((next (gensym))
	(lst (gensym)))
    `(do ((,next (,link ,node) (,link ,next))
	  (,lst nil (cons ,next ,lst)))
	 ((eq ,next ,node) ,lst))))

;;; Macros to loop over a circular list of nodes. The second macro excludes
;;; the starting node.

(defmacro loop-over-nodes ((id node link) &body body)
  (let ((flag (gensym)))
    `(do ((,flag nil t)
	  (,id ,node (,link ,id)))
	 ((and ,flag (eq ,id ,node)) nil)
       . ,body)))

(defmacro loop-over-nodes-excluding ((id node link) &body body)
  `(do ((,id (,link ,node) (,link ,id)))
       ((eq ,id ,node) nil)
     . ,body))

;;; Predicates to determine whether a node is a leaf.

(defun is-a-leaf (node)
  (and (null (e-node-ecar node)) (null (e-node-ecdr node))))

(defun is-a-leaf-aux (node)
  (and (null (aux-node-ecar node)) (null (aux-node-ecdr node))))



;;; Structure for forbid node.

(defstruct (fnode
                  (:constructor
                   make-fnode (enode justification &optional link))
                  :named :predicate)
  enode
  justification
  link
  )

;;; Construct an fnode with appropriate initial values.
(defun makefnode (v justification)
  (let ((new-fnode (make-fnode v justification)))
    (setf (fnode-link new-fnode) new-fnode)	; set its link to itself.
    new-fnode))

;;; Add the forbid of e2 with justification to e1.
(defun add-forbid (e1 e2 justification)
  (let ((f1 (e-node-forbid e1))
	(f2 (makefnode e2 justification)))		; put the forbid in f2.
    (if (null f1)
	(setf (e-node-forbid e1) f2)	; either f2  becomes the only entry,
	(let ((f1-link (fnode-link f1)))
	  (when (neq f1 f1-link)
	    (setf (fnode-link f2) f1-link))
	  (setf (fnode-link f1) f2)))))	; or f2 becomes the second entry.



;;;     Egraph variables and initializations.

;;; Task list for the egraph.
(defvar *merge-list* nil)

;;; Symbols that are variables.
(defvar *variable-symbols* nil)

;;; The egraph version of NIL.
(defvar *enil* (make-auxiliary-node nil nil))


;;; ===== Tables

;;; Tables are used to speed up access to egraph representations of
;;; expressions.

;;; ---------- Table for Symbols ----------

(defvar *integrated-symbols* nil)

(defun put-symbol-expression-table (key value)
  (push key *integrated-symbols*)
  (setf (get key 'e-node) value))

(defsubst get-symbol-expression-table (key)
  (get key 'e-node))

(defsubst remove-symbol-expression-table (key)
  (remprop key 'e-node)
  (setq *integrated-symbols* (remove-eq key *integrated-symbols* 1)))

(defun clear-symbol-expression-table ()
  (dolist (key *integrated-symbols*)
    (remprop key 'e-node))
  (setq *integrated-symbols* nil))

;;; ---------- End of Table for Symbols ----------


;;; ---------- Table for Integers ----------

(defparameter integer-expression-table-size 1023)

(defvar *integrated-integers*
  (make-array integer-expression-table-size :initial-element nil))

(defun put-integer-expression-table (key value)
  (let ((index (mod key integer-expression-table-size)))
    (setf (aref *integrated-integers* index)
          (cons (cons key value) (aref *integrated-integers* index)))
    value))

(defsubst get-integer-expression-table (key)
  (cdr (assoc-equal 
        key
        (aref *integrated-integers* (mod key integer-expression-table-size)))))

(defun remove-assoc-equal (key assoc-list)
  (cond ((null assoc-list) nil)
        ((equal key (caar assoc-list)) (cdr assoc-list))
        (t (cons (car assoc-list)
                 (remove-assoc-equal key (cdr assoc-list))))))

(defsubst remove-integer-expression-table (key)
  (let ((index (mod key integer-expression-table-size)))
    (setf (aref *integrated-integers* index)
          (remove-assoc-equal key (aref *integrated-integers* index)))))

(defun clear-integer-expression-table ()
  (dotimes (index integer-expression-table-size)
    (setf (aref *integrated-integers* index) nil)))

;;; ---------- End of Table for Integers ----------


;;; ---------- Table for Debruijn Expressions ----------

;;; Debruijn expressions are temporary expressions that represent
;;; quantified expressions in canonical form.

(defvar *debruijn-table* nil)

(defsubst put-debruijn-table (key value)
  (push (cons key value) *debruijn-table*))

(defsubst get-debruijn-table (key)
  (cdr (assoc-equal key *debruijn-table*)))

(defsubst remove-debruijn-table (key)
  (delete-equal (assoc-equal key *debruijn-table*) *debruijn-table*))

(defun clear-debruijn-table ()
  (setq *debruijn-table* nil))

;;; ---------- End of Table for Debruijn Expressions ----------


;;; ---------- Table for Quantified Expressions ----------

;;; Table for quantified expressions.

(defvar *quantification-table* nil)

(defsubst put-quantification-table (key value)
  (push (cons key value) *quantification-table*))

(defsubst get-quantification-table (key)
  (cdr (assoc-equal key *quantification-table*)))

(defsubst remove-quantification-table (key)
  (delete-equal (assoc-equal key *quantification-table*)
                *quantification-table*))

(defun clear-quantification-table ()
  (setq *quantification-table* nil))

;;; ---------- End of Table for Quantified Expressions ----------



;;; ---------- Predefined e-nodes ----------

;;; Function to make special predefined e-nodes.
(defun make-special-node (name type)
  (let ((node (make-an-e-node nil nil name type)))
    (put-symbol-expression-table name node)
    (let ((e-node (make-an-e-node node *enil* (list name) type)))
      (setf (e-node-e-pred node) e-node)
      (cond ((null (aux-node-e-pred *enil*))
	     (setf (aux-node-e-pred *enil*) e-node))
	    (t (let ((done (aux-node-e-pred *enil*)))
		 (do ((next (e-node-samecdr done) (e-node-samecdr next))
		      (current done (e-node-samecdr current)))
		     ((eq next done)
		      (setf (e-node-samecdr current) e-node)
		      (setf (e-node-samecdr e-node) done))))))
      (setf (e-node-operation e-node) name)
      e-node)))

(defvar *bool-node*
  (make-special-node 'bool (make-an-e-node nil nil (gensym) nil)))
(defvar *int-node*
  (make-special-node 'int (make-an-e-node nil nil (gensym) nil)))

(defvar *true-node* (make-special-node 'true *bool-node*))
(defvar *false-node* (make-special-node 'false *bool-node*))

(defun make-type-of-node ()
  (let ((node (make-an-e-node nil nil 'type-of *univ-type*)))
    (put-symbol-expression-table 'type-of node)))

(defvar *type-of-node* (make-type-of-node))

(defun make-zero-node ()
  (let ((node (make-an-e-node nil nil 0 *int-node*)))
    (put-integer-expression-table 0 node)))

(defun make-one-node ()
  (let ((node (make-an-e-node nil nil 1 *int-node*)))
    (put-integer-expression-table 1 node)))

(defvar *zero-node* (make-zero-node))
(defvar *one-node* (make-one-node))

;;; ---------- End of Predefined e-nodes ----------

;;; =============== End of Data Structures for the Egraph ===============



;;; =============== Data Structures for the Tableau ===============


;;; Structure for row headers.

(defstruct (row
                (:constructor
                 make-row
                 (index &optional owners restriction reason-restricted
                        reason-killed rnext mark sums))
                :named :predicate)
  index               ; index of row header in array.
  owners              ; list of dotted pairs (index . e-node).
  restriction         ; nil, 'restricted or 'dead.
  reason-restricted   ; justification for 'restricted.
  reason-killed       ; justification for 'dead.
  rnext               ; nil or element.
  mark                ; marker used by tableau when propagating facts.
  sums                ; list of sums.
  )

;;; Structure for column headers.

(defstruct (col
                (:constructor
                 make-col
                 (index &optional owners restriction reason-restricted
                        reason-killed cprev sums))
                :named :predicate)
  index               ; index of row header in array.
  owners              ; list of dotted pairs (index . e-node).
  restriction         ; nil, 'restricted or 'dead.
  reason-restricted   ; justification for 'restricted.
  reason-killed       ; justification for 'dead.
  cprev               ; nil or element.
  sums                ; list of sums.
  )

;;; Structure for elements of sparse matrix.

(defstruct (element :named :predicate)
  row col rnext cprev coeff)

(defparameter *initial-row-size* 128.)

;;; Make and initialize rows.
(defun initialize-rows ()
  (let ((rows (make-array *initial-row-size* :adjustable t :fill-pointer 1))
        ;; Initially there is only one row - the zero row.
	(h-row (make-row 0 nil 'dead)))
    (setf (aref rows 0) h-row)
    (setf (row-reason-killed h-row) 'zero-row)
    rows))

(defparameter *initial-col-size* 32.)

;;; Make and initialize columns.
(defun initialize-columns ()
  (let ((cols (make-array *initial-col-size* :adjustable t :fill-pointer 1))
        ;; Initially there is only one column - the one (constant) column.
	(h-col (make-col 0 nil 'constant)))
    (setf (aref cols 0) h-col)
    cols))



;;; Sums are stored in sums slot of row/col headers. The order in
;;; which the sums are stored is the same as the order in which
;;; the respective owners are stored in the owners slot.

;;; Return appropriate sum. Only called by itself and by sum-of-node.
;;; - key represents owner and is a dotted pair (index . e-node)
;;;   where index is 0, 1, 2 or 3.
;;; - key-list is a list of owners.
;;; - entry-list is a list of entries, ehere each entry is a sum.
(defun sum-of-node-aux (key key-list entry-list)
  (cond ((null key-list) nil)
	((equal key (car key-list)) (car entry-list))
	(t (sum-of-node-aux key (cdr key-list) (cdr entry-list)))))

;;; Return the appropriate sum given an e-node and an index.
(defun sum-of-node (e-node index)
  (let ((entry (aref (e-node-tableau-entry e-node) index)))
    (cond ((row-p entry)
	   (sum-of-node-aux
	     (cons index e-node)
	     (row-owners entry)
	     (row-sums entry)))
	  ((col-p entry)
	   (sum-of-node-aux
	     (cons index e-node)
	     (col-owners entry)
	     (col-sums entry))))))

;;; Increase the size of array of row headers by one and return new row.
(defun add-row (a)
  ;; Must create a header for the new row.
  (let ((h-row (make-row (fill-pointer a))))
    (vector-push-extend h-row a)
    h-row))

;;; Increase the size of array of column headers by one and return new
;;; column.
(defun add-column (a)
  ;; Must create a header for the new column.
  (let ((h-col (make-col (fill-pointer a))))
    (vector-push-extend h-col a)
    h-col))

;;; Delete last element of array.
(defun decrease-size-of-array (a)
  (vector-pop a)
  (setf (aref a (fill-pointer a)) nil))

;;; Globals

(defvar *rows*)	             ; The row headers.
(defvar *cols*)              ; The column headers.
(defvar *tableau-list* nil)  ; Task list for the tableau.

;;; =============== End of Data Structures for the Tableau ===============



;;; Structure for subgoal used for backchaining

(defstruct (subgoal (:type list) (:constructor make-subgoal (form sense)))
  form sense)

;;; Globals for backchaining and automatic instantiations in the
;;; simplifier.

(defvar *instantiation-list* nil)

(defvar *substitution-list* nil)

;;; ========== Bags

;;; A bag is simply a list of factors.

;;; Make a bag from an expression.
(defun make-bag (expr)
  (if (and (consp expr) (eq (first expr) '*))
      (append (make-bag (second expr)) (make-bag (third expr)))
    (list expr)))

;;; Make a corresponding expression given a bag.
(defun make-times-from-bag (bag)
  (make-times-from-bag-aux (car bag) (cdr bag)))

(defun make-times-from-bag-aux (left bag)
  (if (null bag)
      left
    (make-* left
            (make-times-from-bag-aux (car bag) (cdr bag)))))

;;; Determine if bag-1 is "smaller" bag-2. This gives an ordering relation.
(defun smaller-bag-p (bag-1 bag-2)
  (let ((length-1 (length bag-1))
	(length-2 (length bag-2)))
    (cond ((< length-1 length-2) t)
	  ((> length-1 length-2) nil)
	  (t (smaller-bag-p-aux bag-1 bag-2)))))

(defun smaller-bag-p-aux (bag-1 bag-2)
  (or (and (equal (car bag-1) (car bag-2))
	   (smaller-bag-p-aux (cdr bag-1) (cdr bag-2)))
      (lexically-smaller-p (car bag-1) (car bag-2))))



;;; ========== Lexically-based Ordering

;;; Determine the rank of an expression.
(defun rank (expression)
  (cond ((integerp expression) 4)
	((symbolp expression)
         (if (member-eq expression *variable-symbols*) 0 3))
	((consp expression) 1)
	(t 2)))

;;; Return t if the first argument is lexically smaller than the second
;;; argument, and return nil otherwise.
(defun lexically-smaller-p (operand-1 operand-2)
  (let ((rank-1 (rank operand-1))
	(rank-2 (rank operand-2)))
    (or (< rank-2 rank-1)
	(and (= rank-1 rank-2)
	     (if (= rank-1 1)
		 (or (< (length operand-1) (length operand-2))
		     (and (= (length operand-1) (length operand-2))
			  (lexically-smaller-p-aux operand-1 operand-2)))
		 (if (= rank-1 4)
		     (let ((abs-1 (abs operand-1))
			   (abs-2 (abs operand-2)))
		       (or (< abs-1 abs-2)
			   (and (= abs-2 abs-1) (> operand-1 operand-2))))
		     (string-lessp (string operand-1) (string operand-2))))))))

(defun lexically-smaller-p-aux (operand-1 operand-2)
  (and operand-1
       (or (lexically-smaller-p (car operand-1) (car operand-2))
	   (and (equal (car operand-1) (car operand-2))
		(lexically-smaller-p-aux (cdr operand-1) (cdr operand-2))))))




;;; ========================= Undo Stack =========================

;;;     push-undo pushes its argument onto the undo stack.

(defsubst push-undo (x)
  (push x *undo-stack*)
  nil)

(defun pop-undo ()
  (catch 'exit-pop-undo
    (when *undo-stack*
      (let ((top (pop *undo-stack*)))
	(apply (car top) (cdr top))))
    (not *inconsistent*)))

(defun undo-push-var ()
  (pop *variable-symbols*))

(defun undo-push ()
  (throw 'exit-pop-undo (not *inconsistent*)))

(defparameter *undo-push-mark* (list #'undo-push))

(defparameter *undo-push-var-mark* (list #'undo-push-var))

;;; Wrapper which undoes egraph and tableau operations and resets the
;;; instantiation list if execution of the body is unsuccessful (if it
;;; returns nil).
(defmacro with-undo (&body body)
  `(let ((undo-stack *undo-stack*)
	 (i-list *instantiation-list*))
     (push-undo *undo-push-mark*)
     (or (progn . ,body)
	 (progn (setq *instantiation-list* i-list)
		(loop until (eq undo-stack *undo-stack*)
		      do (pop-undo))))))

;;; Wrapper which always undoes egraph and tableau operations
;;; performed when executing body.
(defmacro with-recover-undo-stack-always (&body body)
  `(let ((undo-stack *undo-stack*))
     (push-undo *undo-push-mark*)
     (prog1 (progn . ,body)
	    (loop until (eq undo-stack *undo-stack*)
		  do (pop-undo)))))

;;; Set *inconsistent* that is undoable.
(defun set-inconsistent (justification)
  (push-undo (list #'undo-inconsistent *inconsistent*))
  (setq *inconsistent* (or justification t)))




;;; ========== More Predicates on Nodes.

;;; return non-nil if two types are the same
(defsubst same-etype (type-0 type-1)
  (eq (e-node-root type-0) (e-node-root type-1)))

(defsubst int-etype-p (type)
  (and (e-node-p type) (same-etype type *int-node*)))

(defsubst bool-etype-p (type)
  (and (e-node-p type) (same-etype type *bool-node*)))

(defsubst node-bool-p (node)
  (and (e-node-p (e-node-type node))
       (eq (e-node-root (e-node-type node)) (e-node-root *bool-node*))))

(defsubst node-int-p (node)
  (and (e-node-p (e-node-type node))
       (eq (e-node-root (e-node-type node)) (e-node-root *int-node*))))

;;; ---------- Produce arg aux-nodes for e-node.

(defun arg-nodes (node)
  (arg-nodes-aux (e-node-ecdr node)))

(defun arg-nodes-aux (auxnode)
  (cond ((eq auxnode *enil*) nil)
        (t (cons (aux-node-ecar auxnode)
                 (arg-nodes-aux (aux-node-ecdr auxnode))))))

;;; ========== Reversing witness links.
;;; Before: witness links from e-node-1 to e-node-2.
;;; After: witness links from e-node-2 to e-node-1.

(defun reverse-witness-links (e-node-1 e-node-2)
  (cond ((eq e-node-1 e-node-2) e-node-1)
        (t (let ((next (reverse-witness-links (e-node-witness-link e-node-1)
                                              e-node-2)))
             (setf (e-node-witness-link next) e-node-1)
             (setf (e-node-witness-info next) (e-node-witness-info e-node-1))
             e-node-1))))
