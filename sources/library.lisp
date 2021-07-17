
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


;;; ====================== The Library Facility =======================


;;; Information about library unit types. Each list element is of the
;;; form (unit-type description-string file-extension).

(defvar *unit-type-alist* '((spec "specification" "spec")
			    (model "model" "model")
			    (freeze "freeze" "frz")))


;;; Struct for library unit descriptors
;;; Main concepts for descendants and ancestors:
;;; - Direct decendants of a unit Unit are spec units loaded by Unit.
;;; - Direct ancestors of a (spec) unit Unit are units that load Unit.
;;; - Indirect decendants of a (spec) unit represent logical dependency.
;;;   They are the corresponding model unit plus its direct decendants.
;;; - Indirect ancestors of a unit Unit:
;;;   If Unit is a model unit - the corresponding spec unit.
;;;   If Unit is a spec unit - the corresponding spec units of
;;;   model units that load Unit.

(defstruct (unit (:type list))
  (ident nil)                ; unit identifier (name and unit type)
  (pathname nil)             ; pathname of unit
  (descendants nil)          ; identifiers of direct descendants
  (direct-descendants nil)   ; spec units loaded by unit
  (direct-ancestors nil)     ; units that load this one
  (indirect-descendants nil) ; model unit plus its direct descendants
  (indirect-ancestors nil)   ; units that indirectly load this one
  (label)                    ; label for cycle checking
  )



;;; List of unit structures for units in the library.

(defvar *units* nil)

;;; Current library name (a string; the name of the library directory).

(defvar *current-library* nil)

;;; Pathname of library directory file for current library.

(defvar *current-library-directory-pathname* nil)

;;; Create the name of a library component, given its name and type.

(defun make-unit-pathname (unit-name unit-type)
  (make-pathname :name (string unit-name)
		 :type (third (assoc-eq unit-type *unit-type-alist*))
		 :defaults *current-library*))


;;; Interface functions.

;;; Initialize the library manager and set the current library. No I/O
;;; operations are done until an actual library operation. Returns the pathname
;;; of the library directory if no errors were found, :error otherwise.

(defun set-library-directory (filename)
  (unless (stringp filename)
    (print-error 'filename-not-string filename)
    (return-from set-library-directory :error))
  (let ((dirname (if (equal (aref filename (- (string-length filename) 1)) #\/)
		     filename
		   (string-append filename "/"))))
    (setq *units* nil)
    (setq *current-library* dirname)
    (setq *current-library-directory-pathname*
	  (make-pathname :name "libdir"
			 :type "txt"
			 :defaults dirname))))

;;; Return the current library, or nil if it has not been set.

(defun current-library ()
  *current-library*)

;;; Create a new library unit. A unit identified by unit-name
;;; and unit-type must not already exist.  Returns the pathname of
;;; the unit if no errors where encountered, :error otherwise.

(defun create-unit (unit-name unit-type descendants)
  (unless (library-check-args unit-name unit-type)
    (return-from create-unit :error))
  (let ((unit (find-library-unit unit-name unit-type)))
    (cond
      ((eq unit :error)
       (return-from create-unit :error))
      (unit
       (print-error 'unit-exists (list unit-name unit-type))
       (return-from create-unit :error)))
    (setq unit (make-unit :ident (list unit-name unit-type)
			      :pathname
			      (make-unit-pathname unit-name unit-type)
			      :descendants descendants))
    (add-unit unit)
    (unless (dependency-graph-acyclic)
      (remove-unit unit)
      (print-error 'circular-dependency unit-name)
      (return-from create-unit :error))
    (update-library)
    (unit-pathname unit)))

;;; Get the pathname of a unit in the library. The unit must exist if
;;; probe-p is nil.  If the unit exists, the pathname if the unit is
;;; returned. If probe-p is t and the unit does not exist, nil is
;;; returned. Otherwise :error is returned.

(defun get-unit (unit-name unit-type &optional probe-p)
  (unless (library-check-args unit-name unit-type)
    (return-from get-unit :error))
  (let ((unit (find-library-unit unit-name unit-type)))
    (cond
      ((eq unit :error)
       :error)
      ((null unit)
       (cond
	 (probe-p nil)
	 (t
	  (print-error 'unit-does-not-exist (list unit-name unit-type))
	  :error)))
      (t (unit-pathname unit)))))

;;; Delete a library unit. The unit must exist. If no errors were
;;; detected, returns nil, :error otherwise.

(defun delete-unit (unit-name unit-type)
  (unless (library-check-args unit-name unit-type)
    (return-from delete-unit :error))
  (let ((unit (find-library-unit unit-name unit-type)))
    (cond
      ((eq unit :error)
       (return-from delete-unit :error))
      ((null unit)
       (print-error 'unit-does-not-exist (list unit-name unit-type))
       (return-from delete-unit :error)))
    (remove-unit unit)
    (update-library)
    nil))

;;; Get the (list of) identifiers for the direct descendants of the unit
;;; identified by unit-name and unit-type. Returns :error if an error
;;; was encountered.

(defun get-descendants (unit-name unit-type)
  (unless (library-check-args unit-name unit-type)
    (return-from get-descendants :error))
  (let ((unit (find-library-unit unit-name unit-type)))
    (cond
      ((eq unit :error)
       :error)
      ((null unit)
       (print-error 'unit-does-not-exist (list unit-name unit-type))
       :error)
      (t
       (map-descendants #'unit-ident unit)))))

;;; Get the (list of) identifiers for the direct ancestors of the unit
;;; identified by unit-name and unit-type. Returns :error if an error
;;; was encountered.

(defun get-ancestors (unit-name unit-type)
  (unless (library-check-args unit-name unit-type)
    (return-from get-ancestors :error))
  (let ((unit (find-library-unit unit-name unit-type)))
    (cond
      ((eq unit :error)
       :error)
      ((null unit)
       (print-error 'unit-does-not-exist (list unit-name unit-type))
       :error)
      (t
       (map-ancestors #'unit-ident unit)))))

;;; Get the (list of) identifiers of units in the library.
;;; Returns :error if an error was encountered.

(defun get-units (&optional empty-units)
  (unless *current-library*
    (print-error 'library-not-set)
    (return-from get-units :error))
  (unless (read-library)
    (return-from get-units :error))
  (loop for obj in *units*
	for ident = (unit-ident obj)
	when (or (assoc-eq (second ident) *unit-type-alist*) empty-units)
	collect (list (first ident) (second ident))))



;;; Perform error checking for arguments passed to interface routines.
;;; Returns t if no errors were found, nil otherwise.

(defun library-check-args (unit-name unit-type)
  (let ((error t))
    (unless *current-library*
      (print-error 'library-not-set unit-name)
      (setq error nil))
    (unless (symbolp unit-name)
      (print-error 'unit-name-not-symbol unit-name)
      (setq error nil))
    (unless (assoc-eq unit-type *unit-type-alist*)
      (print-error 'invalid-unit-type unit-type)
      (setq error nil))
    error))

;;; Find the unit identified. Returns unit if found, nil if not
;;; found, :error if an error was encountered.

(defun find-library-unit (unit-name unit-type)
  (if (read-library)
      (assoc-equal (list unit-name unit-type) *units*)
      :error))

;;; Read the directory file of the current library from the file system,
;;; if it is not already read in, and build the dependency graph.
;;; Returns t if successful, nil otherwise.

(defun read-library ()
  ;; If *units* is non-nil, the library has already been read in, or has
  ;; already been determined to be empty.
  (when *units*
    (return-from read-library t))
  ;; If there is no library directory file, the library is new.
  ;; Nothing to read in.
  (unless (probe-file *current-library-directory-pathname*)
    (return-from read-library t))
  ;; Read the directory file and add the units specified. We can't depend
  ;; on the order of the units in the directory file because units
  ;; may have been rearranged by deletions and updates, so we have to sort
  ;; the units so that dependant units follow the units they load.
  (let ((units nil))
    (with-open-file (str *current-library-directory-pathname*)
      (unless str
	(file-error "open" *current-library-directory-pathname*)
	(return-from read-library nil))
      (read str nil 'eof)
      (loop for ident = (read str nil 'eof)
	    until (eq ident 'eof)
	    do (push (make-unit :ident ident
				  :pathname
				  (make-unit-pathname (first ident)
							(second ident))
				  :descendants (read str))
		     units)))
    (setq units
	  (sort units #'(lambda (x y)
			    (member-equal (unit-ident x)
					  (unit-descendants y)))))
    (mapc #'add-unit units))
  t)

;;; Add unit to *units* set up the descendant/ancestor links.
;;; The descendant/ancestor links must point to existing units.

(defun add-unit (unit)
  (let ((deplist nil)
	(ident (unit-ident unit)))
    ;; Ensure that all the descendants exist, and find their unit structures.
    (loop for d in (unit-descendants unit)
	  for obj = (assoc-equal d *units*)
	  if obj do (push obj deplist)
	  else do (error "unit ~A on which ~A depends not found"
			 d
			 (unit-ident unit)))
    (push unit *units*)
    ;; Make direct descendant and ancestor links between the new unit
    ;; and its direct descendants.
    (setf (unit-direct-descendants unit) deplist)
    (loop for obj in deplist do (pushnew unit (unit-direct-ancestors obj)))
    ;; Make direct descendant links between the direct ancestors of the
    ;; new unit and the new unit. Similarly for indirect ancestors.
    ;; This is just in case add-unit is being used to update an unit.
    (loop for obj in (unit-direct-ancestors unit)
	  do (pushnew unit (unit-direct-descendants obj)))
    (loop for obj in (unit-indirect-ancestors unit)
	  do (pushnew unit (unit-indirect-descendants obj)))
    ;; If the new unit is a spec unit that has a corresponding
    ;; model unit, make indirect descendant and ancestor links
    ;; between the new unit and its indirect descendants.
    ;; The indirect descendants are the corresponding model unit
    ;; plus all direct descendants of the model unit.
    (when (eq (second ident) 'spec)
      (let* ((indirect-ident (list (first ident) 'model))
	     (indirect-unit (assoc-equal indirect-ident *units*)))
	(when indirect-unit
	  (setf (unit-indirect-descendants unit)
		(copy-list (unit-direct-descendants indirect-unit)))
	  (loop for obj in (unit-direct-descendants indirect-unit)
		do (pushnew unit (unit-indirect-ancestors obj))))))
    ;; If the new unit is a model unit that has a corresponding
    ;; spec unit, make indirect descendant and ancestor links between
    ;; the spec unit and the direct descendants of the new unit.
    (when (eq (second ident) 'model)
      (let* ((indirect-ident (list (first ident) 'spec))
	     (indirect-unit (assoc-equal indirect-ident *units*)))
	(when indirect-unit
	  (setf (unit-indirect-descendants indirect-unit)
		(unit-direct-descendants unit))
	  (loop for obj in (unit-direct-descendants unit)
		do (pushnew indirect-unit (unit-indirect-ancestors obj))))))
    t))

;;; Remove unit from *units* and from the dependency graph. The unit
;;; itself is not modified, so that its ancestors can still be reached from it.

(defun remove-unit (unit)
  (let ((ident (unit-ident unit)))
    ;; Remove direct ancestor links to unit from its direct descendants.
    (loop for obj in (unit-direct-descendants unit)
	  do (setf (unit-direct-ancestors obj)
		   (remove-eq unit (unit-direct-ancestors obj))))
    ;; Remove direct descendent links to unit from its direct ancestors. 
    (loop for obj in (unit-direct-ancestors unit)
	  do (setf (unit-direct-descendants obj)
		   (remove-eq unit (unit-direct-descendants obj))))
    ;; Remove indirect ancestor links to unit from its indirect descendants. 
    (loop for obj in (unit-indirect-descendants unit)
	  do (setf (unit-indirect-ancestors obj)
		   (remove-eq unit (unit-indirect-ancestors obj))))
    ;; Remove indirect descendant links to unit from its indirect ancestors. 
    (loop for obj in (unit-indirect-ancestors unit)
	  do (setf (unit-indirect-descendants obj)
		   (remove-eq unit (unit-indirect-descendants obj))))
    ;; Currently indirect units are spec counterparts of model units.
    (when (eq (second ident) 'model)
      (let* ((indirect-ident (list (first ident) 'spec))
	     (indirect-unit (assoc-equal indirect-ident *units*)))
	(when indirect-unit
	  ;; spec counterpart exists
	  (loop for obj in (unit-direct-descendants unit)
		do
		(progn
		  ;; Remove indirect descendant links to unit's direct
		  ;; descendant from spec counterpart.
		  (setf (unit-indirect-descendants indirect-unit)
			(remove-eq
			 obj (unit-indirect-descendants indirect-unit)))
		  ;; Remove indirect ancestor links to spec counterpart
		  ;; from unit's direct descendant
		  (setf (unit-indirect-ancestors obj)
			(remove-eq
			 indirect-unit (unit-indirect-ancestors obj))))))))
    ;; Remove unit from *units*.
    (setf *units*
	  (remove-if #'(lambda (obj) (equal (unit-ident unit) (car obj)))
		     *units*))))

;;; Check the dependency graph for circularity. Returns t if the graph is
;;; acyclic, nil otherwise.

(defun dependency-graph-acyclic ()
  ;; Mark all the nodes in the graph as :new.
  (mapc #'(lambda (x)
	    (setf (unit-label x) :new))
	*units*)
  ;; For each new node in the graph, check for cycles in the part of the
  ;; graph rooted at that node.
  (dolist (unit *units*)
    (when (eq (unit-label unit) :new)
      (unless (dependency-graph-acyclic-1 unit)
	(return-from dependency-graph-acyclic nil))))
  t)

;;; Check a connected subgraph of the dependency graph for circularity.
;;; Returns t if the subgraph is acyclic, nil otherwise.

(defun dependency-graph-acyclic-1 (unit)
  (case (unit-label unit)
    (:new
      ;; Mark this node as visited, and look at the direct and indirect
      ;; descendants.
      (setf (unit-label unit) :visited)
      (dolist (d (unit-direct-descendants unit))
	(unless (dependency-graph-acyclic-1 d)
	  (return-from dependency-graph-acyclic-1 nil)))
      (dolist (d (unit-indirect-descendants unit))
	(unless (dependency-graph-acyclic-1 d)
	  (return-from dependency-graph-acyclic-1 nil)))
      ;; At this point, it is known that none of the descendants lead to
      ;; a cycle, so this node can be marked as dead.
      (setf (unit-label unit) :dead)
      t)
    (:dead
      ;; There are no more links from this node, so it can't be part of
      ;; a cycle.
      t)
    (:visited
      ;; We have seen this node already, so there must be a cycle in the
      ;; subgraph.
      nil)))

;;; Call func on all transitive direct descendants of unit, once.
;;; Returns a list of the results.

(defun map-descendants (func unit)
  (when (unit-direct-descendants unit)
    (let ((visited (cons nil nil)))
      (mapcan #'(lambda (x)
		  (map-descendants-1 func x visited))
	      (unit-direct-descendants unit)))))

;;; Do the real work of map-descendants - a depth-first traversal of the
;;; dependency graph.

(defun map-descendants-1 (func unit visited)
  (unless (member-eq unit (car visited))
    (push unit (car visited))
    (append (mapcan #'(lambda (x)
			(map-descendants-1 func x visited))
		    (unit-direct-descendants unit))
	    (list (funcall func unit)))))

;;; Call func on all transitive direct ancestors of unit, once.
;;; Returns a list of the results.

(defun map-ancestors (func unit)
  ;; Mark all the nodes in the graph as :new, then do the actual work.
  (when (unit-direct-ancestors unit)
    (let ((visited (cons nil nil)))
      (mapcan #'(lambda (x)
		  (map-ancestors-1 func x visited))
	      (unit-direct-ancestors unit)))))

;;; Do the real work of map-ancestors - a depth-first traversal of the
;;; dependency graph.

(defun map-ancestors-1 (func unit visited)
  (unless (member-eq unit (car visited))
    (push unit (car visited))
    (append (mapcan #'(lambda (x)
			(map-ancestors-1 func x visited))
		    (unit-direct-ancestors unit))
	    (list (funcall func unit)))))

;;; Update the directory file of the current library on disk.
;;; Deletes the old one
;;; first if it exists.

(defun update-library ()
  (when (probe-file *current-library-directory-pathname*)
    (delete-file *current-library-directory-pathname*))
  (with-open-file (str *current-library-directory-pathname* :direction :output
		       :if-exists :supersede)
    (unless str
      (file-error "create" *current-library-directory-pathname*)
      (return-from update-library nil))
    (format str "NIL~%")
    (loop for obj in *units*
	  do (format str "~S ~S~%"
		     (unit-ident obj)
		     (unit-descendants obj)))))



;;; Functions for adding loads.

;;; top level function for creating new loads

(defun create-load (event-name)
  (when (without-errors (event-name)
	  (check-event event-name))
    (let ((history *history*)
	  (exit nil))
      (unwind-protect (catch 'error
			(funcall (get 'uload 'add)
				 (make-uload :name event-name
					     :kind 'loadf
					     :prop nil
					     :unit event-name
					     :formula *true*
					     :proof nil	;an assumption
					     :proven t)) ;indicated here
			(setq exit 'normal-exit))
	(with-abort-disabled
	  (cond ((eq exit 'normal-exit) event-name)
		(t (loop until (eq *history* history)
			 do (undo-event))
		   nil)))))))

;;; Command to load a SPEC unit from the current library.  If a SPEC
;;; with the same name has been loaded then this has no effect.

(defcmd uload (event-name)
  ((:string "Load the library")
   (:event-name spec)
   (:string "unit")
   (:command-argument event-name)
   (:string "from the current library.  The unit's events are
loaded into the prover database as subsidiary events of the")
   (:command-name uload)
   (:string "event.  However, if the library unit has already been loaded,
it is not reloaded and the operation is not recorded."))
  (unless (and (symbolp event-name) (uload-p (get-event event-name)))
    (create-load event-name)))



;;; The workhorse for loading library units.  It loads an unit by
;;; reading in a compressed representation of a sequence of events,
;;; adding the events as they are read, and then folding the events
;;; together under the uload event.  This function is called by the add
;;; function for uload.

(defun load-library-unit (load)
  (let ((pathname (get-unit (uload-unit load) 'spec)))
    (case pathname
      (:error
	(throw 'error nil))
      (t (read-compressed-file pathname nil t)
	 load))))


;;; Command to make a unit in the current library from the current session.

(defcmd make (unit-name unit-type)
  ((:string "Write the contents of the prover database
as an unit called")
   (:command-argument unit-name)
   (:string "in the current library.  The argument")
   (:command-argument unit-type)
   (:string "determines whether the unit is to be a
specification (if it has the value")
   (:event-name spec)
   (:punctuation "),")
   (:string "an implementation (if it has the value")
   (:event-name model)
   (:punctuation "),")
   (:string "or simply represent the state of the prover
database (if it has the value")
   (:event-name freeze)
   (:punctuation ").")
   (:string "For a specification unit, stubs are allowed and")
   (:command-name procedure)
   (:punctuation "s")
   (:string "must be stubs.  For an implementation
unit, stubs are prohibited."))
  (update-proof-status)				;save proof in progress
  (case unit-type
    (spec
      (when (without-errors (nil)
	      (check-consistency unit-name 'spec))
	(write-library-unit unit-name 'spec (history-descendants))))
    (model
      (when (without-errors (nil)
	      (check-unproven-events)
	      (check-consistency unit-name 'model))
	(write-library-unit unit-name 'model (history-descendants))))
    (freeze
      (write-library-unit unit-name 'freeze (history-descendants)))
    (t (print-error 'invalid-unit-type unit-type))))

;;; Code to perform consistency check in case the unit's counterpart
;;; is already in the library.

(defun check-consistency (unit-name unit-type)
  (let ((pathname (get-unit unit-name
			      (if (eq unit-type 'spec) 'model 'spec)
			      t)))
    (cond
      ((null pathname)
       nil)
      ((eq pathname :error)
       (setq *parse-error-flag* t)
       nil)
      (t
       (check-consistency-of-unit pathname unit-type)))))



;;; Write a library unit.  It is assumed that stub checking and
;;; consistency checking have been performed.  However, it may still
;;; fail because of circularity, because the unit is already in
;;; the specified library, or because of other library errors.

(defun write-library-unit (unit-name unit-type descendants)
  (let ((pathname (create-unit unit-name unit-type descendants)))
    (unless (eq pathname :error)
      (write-compressed-file pathname unit-name (eq unit-type 'spec)))))

(defun history-descendants ()
  (mapcar #'(lambda (u) (list (uload-name u) 'spec))
	  (remove-if-not #'uload-p (group-user-history))))



;;; Check for unproven events.

(defun check-unproven-events ()
  (let ((unproven-list (select-unproven-events)))
    (when unproven-list
      (parse-error 'declarations-unproven unproven-list))))

;;; Command to edit a unit in the current library.

(defcmd edit (unit-name unit-type)
  ((:string "The library unit specified is loaded into the
database. This puts the database in the same state as when the")
   (:command-name make)
   (:string "of the unit was performed (unless the unit is a
specification, in which case proofs are deleted)."))
  (let ((pathname (get-unit unit-name unit-type)))
    (case pathname
      (:error nil)
      (t (let ((exit nil))
	   (reset)
	   (unwind-protect
	       (catch 'error (setq exit (read-compressed-file pathname t nil)))
	     (with-abort-disabled
	       (cond ((null exit) (reset))
		     ((eq exit pathname) pathname)))))))))


;;; Command to print the status of the current library.

(defcmd print-library-status (&optional unit-name unit-type)
  ((:string "Print the status of the current library.
If the arguments")
   (:command-argument unit-name)
   (:string "and")
   (:command-argument unit-type)
   (:string "are given then the status of the specified unit is
printed instead."))
  (when (current-library)
    (printer `((:newline) (:newline)
	       (:string "Status of library")
	       (:formula ,(current-library)))))
  (cond
    ((null (current-library))
     (printer '((:newline)
		(:string "There is no current library."))))
    ((null unit-name)
     (let ((units (get-units)))
       (cond
	 ((null units)
	  (printer '((:newline)
		     (:string "The library is empty."))))
	 ((listp units)
	  (printer '((:newline)))
          (let ((names (sort (unique (mapcar #'first units))
                             #'alphalessp)))
            (loop for name in names
                  do (let ((kinds (sort (get-unit-kinds name units)
                                        #'alphalessp)))
                       (printer (cons (list :event-name name)
                                      (mapcar #'(lambda (u)
                                                  (list :event-name u))
                                              kinds))))))))))
    (t
     (let ((unit (get-unit unit-name unit-type)))
       (unless (eq unit :error)
	 (let ((ancestors (get-ancestors unit-name unit-type))
	       (descendants (get-descendants unit-name unit-type)))
	   (print-library-status-aux "Unit ancestors:" ancestors)
	   (print-library-status-aux "Unit descendants:" descendants)))))))

;;; Collect the kinds of units matching the name.

(defun get-unit-kinds (name units)
  (loop for unit in units
        when (eq (first unit) name)
        collect (second unit)))

(defun print-library-status-aux (header units)
  (printer `((:newline) (:newline)
	     (:string ,header)
	     . ,(and (null units) '((:string "Nothing")))))
  (dolist (obj units)
    (printer `((:event-name ,(first obj))
	       (:event-name ,(second obj))))))



;;; Command to delete a unit from the current library.

(defcmd delete (unit-name unit-type)
  ((:string "Delete the library unit specified.  Other units
that depend on this unit are also deleted. You will be asked
to confirm this operation before it is performed."))
  (let ((pathname (get-unit unit-name unit-type)))
    (case pathname
      (:error nil)
      (t
	(let ((ancestors (get-ancestors unit-name unit-type))
	      (current-loads
		(mapcar #'(lambda (u)
			    (list (uload-unit u) 'spec))
			(remove-if-not #'uload-p (group-user-history)))))
	  (cond ((intersection-equal
		   (cons (list unit-name unit-type) ancestors)
		   current-loads)
		 (parse-error 'units-loaded
			      (cons unit-name
				    (mapcar #'first
					    (intersection-equal
					      ancestors current-loads)))))
		(t (when ancestors
		     (print-library-status-aux
		       "The following units will also be deleted:"
		       ancestors))
		   (when (yes-or-no-p "Confirm ")
		     (let ((pnames (cons pathname
					 (mapcar #'(lambda (x)
						     (get-unit (first x)
								 (second x)))
						 ancestors))))
		       (with-abort-disabled
			 (dolist (obj ancestors)
			   (delete-unit (first obj) (second obj)))
			 (delete-unit unit-name unit-type))
		       (mapc #'(lambda (u) (delete-file u)) pnames))
		     pathname))))))))


(defhelp libraries extra-help
  ((:newline)
   (:string "The library facility allows for the storage, retrieval and
deletion of units from libraries.  The main purpose of this facility
is to provide a modularization mechanism.  Libraries may contain")
   (:event-name spec)
   (:string "(specification) units, which may be loaded
into the prover database using the")
   (:command-name uload)
   (:string "command.  When loaded, events created by these units
are assumed to be proven elsewhere.  More specifically, they must be
proven in their corresponding")
   (:event-name model)
   (:string "(implementation) units.  By loading only the
specification (which may be somewhat abstract), the prover
will perform proofs at the specification level, which may
be less complex than if the proofs are done at the level of the
implementation.")
   (:paragraph)
   (:string "The user may store the contents of the prover database as a")
   (:event-name spec)
   (:string "or")
   (:event-name model)
   (:string "unit in a library using the")
   (:command-name make)
   (:string "command.  In the former case, stub declarations are allowed,
while in the latter case, they are prohibited.  In either case, a
circularity check is performed and, if the unit's counterpart is already
in the specified library, a syntactic consistency check is also performed.
Only if these checks are successful is the unit stored in the library.")
   (:paragraph)
   (:string "In addition to the above operations, the user may also
edit an unit using the")
   (:command-name edit)
   (:string "command.  This has the effect of thawing the unit into
the prover database (see the")
   (:command-name thaw)
   (:string "command).  The user may also delete units from libraries
using the")
   (:command-name delete)
   (:string "command.  Libraries are created using the")
   (:command-name create)
   (:string "command.  The command")
   (:command-name print-library-status)
   (:string "is also provided to show the status of a library or
library unit.")))


;;; Command to set the current library. The directory name must
;;; be a string with a trailing slash.

(defcmd set-library (directory-name)
  ((:string "Set the current library to be the one stored in
the specified directory. If any units have already been loaded from the
previous library, the prover is reset."))
  (set-library-directory directory-name)
  (when (history-descendants)
        (reset)
        t))




;;; ===== Renaming Functions for the Library


;;; Identifier and variable renaming.

;;; The alist of names in the library unit to be renamed.

(defvar *rename-list*)

;;; If non-nil, then variable names will be prefixed with *variable-prefix*.

(defvar *rename-vars*)

(defparameter *variable-prefix* ")")

;;; Renaming of identifiers and variables.

(defmacro rename-ident (ident)
  `(or (cdr (assoc-eq ,ident *rename-list*))
      ,ident))

(defmacro rename-idents (idents)
  `(sublis-eq *rename-list* ,idents))

(defmacro rename-var (var)
  `(if *rename-vars*
       (intern (string-append *variable-prefix* ,var) *zk-package*)
       ,var))

(defmacro rename-vars (vars)
  `(if *rename-vars*
       (mapcar #'(lambda (x)
		   (intern (string-append *variable-prefix* x) *zk-package*))
	       ,vars)
       ,vars))

;;; Top-level renaming function.

(defun rename-zk-sexp (rename-list sexp &optional (rename-vars nil))
  (let ((*rename-list* rename-list)
	(*rename-vars* rename-vars))
    (rename-zk-sexp-aux sexp)))

(defun rename-zk-sexp-aux (sexp)
  (funcall (get (car sexp) 'library-rename-function) sexp))

;;; Functions.

(defpropfun (function library-rename-function) (decl)
  (list 'FUNCTION
	(rename-ident (second decl))
	(rename-vars (third decl))
	(mapcar #'rename-annotation (fourth decl))
	(rename-expression (fifth decl))))

(defpropfun (zf-function library-rename-function) (decl)
  (list 'ZF-FUNCTION
	(rename-ident (second decl))
	(rename-vars (third decl))
	(rename-zf-body (fourth decl))))

(defpropfun (function-stub library-rename-function) (stub)
  (list 'FUNCTION-STUB
	(rename-ident (second stub))
	(rename-vars (third stub))))

(defun rename-zf-body (body)
  (case (first body)
    (MAP
      (list* 'MAP
	     (rename-expression (second body))
	     (mapcar #'(lambda (x)
			 (list (rename-vars (first x))
			       (rename-expression (second x))))
		     (cddr body))))
    (SELECT
      (list 'SELECT
	    (list (rename-var (first (second body)))
		  (rename-expression (second (second body))))
	    (rename-expression (third body))))
    (THAT
      (list 'THAT
	    (rename-var (second body))
	    (rename-expression (third body))))))

;;; Axioms.

(defpropfun (axiom library-rename-function) (decl)
  (list 'AXIOM
	(rename-ident (second decl))
	(rename-vars (third decl))
	(rename-expression (fourth decl))))

(defpropfun (rule library-rename-function) (decl)
  (list 'RULE
	(rename-ident (second decl))
	(rename-vars (third decl))
	(rename-expression (fourth decl))))

(defpropfun (frule library-rename-function) (decl)
  (list 'FRULE
	(rename-ident (second decl))
	(rename-vars (third decl))
	(rename-expression (fourth decl))))

(defpropfun (grule library-rename-function) (decl)
  (list 'GRULE
	(rename-ident (second decl))
	(rename-vars (third decl))
	(rename-expression (fourth decl))))

;;; Expressions.

(defun rename-expression (expr)
  (cond
    ((symbolp expr)
     (rename-var expr))
    ((or (integerp expr) (characterp expr) (stringp expr))
     expr)
    ((member-eq (first expr) '(ALL SOME))
     (list (first expr)
	   (rename-vars (second expr))
	   (rename-expression (third expr))))
    (t
     (rename-function-application expr))))

(defun rename-function-application (expr)
  (list* (rename-ident (first expr))
	 (mapcar #'rename-expression (cdr expr))))

(defun rename-case-label (label)
  (if (and (listp label) (eq (first label) 'RANGE))
      (rename-range label)
      (rename-expression label)))

(defun rename-range (range)
  (list 'RANGE
	(rename-expression (second range))
	(rename-expression (third range))))

(defun rename-annotation (annotation)
  (case (first annotation)
    ((PRE POST MEASURE INVARIANT)
     (list (first annotation)
	   (rename-expression (second annotation))))
    (INITIAL
      (list* 'INITIAL
	     (mapcar #'(lambda (x)
			 (list
			   (rename-var (first x))
			   (rename-expression (second x))))
		     (cdr annotation))))))

;;; Library and system commands.

(defpropfun ((delete edit load make print-library-status back
	      conjunctive contradict disjunctive end-script
	      help
              print-formula print-history print-recent-declarations
	      print-status prove prove-by-cases prove-by-induction
	      prove-by-rearrange quit read rearrange reduce
	      reset retry rewrite
	      set-library script simplify
	      trivial-rewrite trivial-simplify trivial-reduce undo)
	     library-rename-function) (cmd)
  cmd)

(defpropfun (apply library-rename-function) (cmd)
  (if (null (third cmd))
      (list 'apply (rename-ident (second cmd)))
    (list 'apply (rename-ident (second cmd)) (rename-expression (third cmd)))))

(defpropfun ((print-declaration print-proof print-proof-summary
	      undo-back-thru undo-back-to)
	     library-rename-function) (cmd)
  (if (second cmd)
      (list (first cmd)
	    (rename-ident (second cmd)))
      cmd))

(defpropfun (delete-hypotheses library-rename-function) (cmd)
  (cons (car cmd)
        (mapcar #'rename-expression (cdr cmd))))

(defpropfun ((equality-substitute induct label split suppose)
             library-rename-function) (cmd)
  (if (second cmd)
      (list (first cmd)
	    (rename-expression (second cmd)))
      cmd))

(defpropfun (prenex library-rename-function) (cmd)
  (if (second cmd)
      (list (first cmd) (rename-vars (second cmd)))
    cmd))

(defpropfun ((invoke print-rules-about rules-about try)
             library-rename-function)
  (cmd)
  (list (first cmd)
	(if (symbolp (second cmd))
	    (rename-ident (second cmd))
	    (rename-expression (second cmd)))))

(defpropfun (instantiate library-rename-function) (cmd)
  (list* 'instantiate
	 (rename-instantiation-list (cdr cmd))))

(defpropfun (use library-rename-function) (cmd)
  (list* 'use
	 (rename-ident (second cmd))
	 (rename-instantiation-list (cddr cmd))))

(defun rename-instantiation-list (list)
  (mapcar #'(lambda (x)
	      (list (rename-var (first x))
		    (rename-expression (second x))))
	  list))

(defpropfun (with-subexpression library-rename-function) (sexp)
  `(with-subexpression (,(rename-expression (first (second sexp))))
     ,(rename-zk-sexp-aux (third sexp))))

(defpropfun ((with-disabled with-enabled) library-rename-function) (sexp)
  `(,(first sexp) ,(mapcar #'(lambda (u) (rename-ident u)) (second sexp))
    ,(rename-zk-sexp-aux (third sexp))))

(defpropfun ((disabled with-instantiation without-instantiation
		       with-case-analysis without-case-analysis
		       with-normalization without-normalization)
	     library-rename-function)
	    (sexp)
  `(,(first sexp) ,(rename-zk-sexp-aux (second sexp))))

;;; ===== End of Renaming Functions for the Library



;;; ===== Read/Write, Compression/Decompression

(defun write-gzipped-sexp (sexp comp)
  (cond ((atom sexp) (write-gzipped-atom sexp comp))
	(t
	 (salza2:compress-octet 40 comp)
	 (write-gzipped-sexp (car sexp) comp)
	 (write-gzipped-rest (cdr sexp) comp))))

(defun write-gzipped-rest (rest comp)
  (cond ((null rest) (salza2:compress-octet 41 comp))
	((atom rest)
	 ;; dotted pair
	 (salza2:compress-octet-vector
	  (flexi-streams:string-to-octets " . ")
	  comp)
	 (write-gzipped-atom rest comp)
	 (salza2:compress-octet 41 comp))
	(t
	 (salza2:compress-octet 32 comp)
	 (write-gzipped-sexp (car rest) comp)
	 (write-gzipped-rest (cdr rest) comp))))

(defun write-gzipped-atom (atom comp)
  (salza2:compress-octet-vector
   (flexi-streams:string-to-octets (format nil "~S" atom))
   comp))

(defun write-gzipped-file (pathname sexp)
  (with-open-file
   (output pathname :direction :output :if-exists :supersede
	   :element-type '(unsigned-byte 8))
   (salza2:with-compressor
    (comp 'salza2:gzip-compressor
	  :callback (salza2:make-stream-output-callback output))
    (write-gzipped-sexp sexp comp))))



;;; Writes the current session out to a file in compressed form.

(defun write-compressed-file (pathname prefix spec-p)
  (let ((version *zk-version*)
	(timestamp (get-decoded-date))
	(vars *variables*)
	(renames (and prefix (freeze-renames prefix)))
	(decls (mapcar #'(lambda (u)
			   (zk-output-form
			     (zk-format-event (group-event u))))
		       (reverse (user-history))))	;need correct order
	(proofs (and (not spec-p)
		     (mapcar #'(lambda (u)
				 (list u (mapcar #'freeze-display
						 (event-proof (get-event u)))))
			     (select-proof-events)))))
    (write-gzipped-file
     pathname
     (list version timestamp vars renames decls proofs))
    pathname))



;;; Return true if the argument version string is a compatible library file
;;; version, false otherwise.

(defun compatible-library-version-p (v)
  (compatible-library-version-p-aux v *compatible-zk-versions*))

(defun compatible-library-version-p-aux (v l)
  (cond
   ((null l)
    nil)
   (t
    (or (string-equal v (car l))
	(compatible-library-version-p-aux v (cdr l))))))

(defun read-gzipped-file (pathname)
  (with-open-file
   (str pathname :direction :input :element-type '(unsigned-byte 8))
   (let ((stream (chipz:make-decompressing-stream 'chipz:gzip str)))
     (let ((in (flexi-streams:make-flexi-stream stream :external-format
						:utf-8)))
       (read in)))))

;;; Read in a compressed file into the current session. If reset-p is
;;; non-nil then the session is reset before the read events are added.
;;; If reset-p is nil then after all the events have been added they
;;; are folded under the first event (which is presumably a LOAD).

(defun read-compressed-file (pathname reset-p rename-p)
  (with-open-file
   (stream pathname :direction :input :element-type '(unsigned-byte 8))
   (unless stream
     (file-error "open" pathname)
     (return-from read-compressed-file nil)))
  (let ((n 1)
	(db
	 (handler-case
	  (read-gzipped-file pathname)
	  (error (c) nil))))
    (when (null db)
	(parse-error 'file-not-compressed pathname)
	(throw 'error reset-p))
    (unless (compatible-library-version-p (car db))
	(parse-error 'file-not-valid pathname)
	(throw 'error reset-p))
    (let ((timestamp (cadr db))
	  (vars (third db))
	  (renames (fourth db))
	  (decls (fifth db))
	  (proofs (sixth db)))
      (let ((exit
	     (catch-abort			;needed for thaw
		 (mapcar #'input-variable-p vars)
		 (dolist (decl decls)
		   (let ((renamed-decl
			  (rename-zk-sexp (and rename-p renames) decl)))
		     (if (zk-to-lisp renamed-decl)
			 (incf n)
			 (let ((cmd (strip-modifiers decl)))
			   (unless (and (eq (first cmd) 'load)
					(uload-p (get-event (second cmd))))
			     (throw 'error nil))))))
		 (unless reset-p (fold-events n))
		 (mapc #'(lambda (u)
			   (let ((event (get-event (first u))))
			     (setf (event-proof event)
				   (mapcar #'(lambda (v) (thaw-display event v))
					   (second u)))
			     (setf (event-proven event)
				   (and (true-p (display-formula
						 (car (event-proof event))))
					(null (display-caseof
					       (car (event-proof event))))))))
		       proofs)
		 'normal-exit)))
	(unless (eq exit 'normal-exit) (throw 'error nil))	;always recover
	pathname))))



;;; freeze-renames constructs a substitution list used to rename
;;; user defined symbols such that each starts with the prefix
;;; qualifier.

(defparameter *load-separator* "!")

(defun freeze-renames (prefix)
  (when prefix (freeze-renames-aux prefix (user-history) nil)))

(defun freeze-renames-event (prefix event result)
  (cond ((atom event)
	 (cons (cons (event-name event)
		     (genname prefix *load-separator* (event-name event)))
	       result))
	((uload-p (car event)) result)
	(t (freeze-renames-event
	    prefix (car event)
	    (freeze-renames-aux prefix (cdr event) result)))))

(defun freeze-renames-aux (prefix history result)
  (cond ((null history) result)
	(t (freeze-renames-event
	    prefix (car history)
	    (freeze-renames-aux prefix (cdr history) result)))))




(defun flatten-decls (decls)
  (cond ((null decls) decls)
	((or (eq (caar decls) 'function-group)
	     (eq (caar decls) 'procedure-group))
	 (append (cddar decls) (flatten-decls (cdr decls))))
	(t (cons (car decls) (flatten-decls (cdr decls))))))

(defun get-matching-decl (name decls)
  (cond ((null decls) nil)
	((eq name (second (car decls))) (car decls))
	(t (get-matching-decl name (cdr decls)))))

(defun decl-fields-consistent-p (spec-fields model-fields)
  (cond ((null spec-fields) t)
	((equal (car spec-fields) (car model-fields))
	 (decl-fields-consistent-p (cdr spec-fields) (cdr model-fields)))
	(t nil)))

(defun decl-arities-consistent-p (spec-args model-args)
  (= (length spec-args) (length (mapcan #'car model-args))))

(defun decls-consistent-p (spec model)
  (cond ((equal spec model) t)
	(t (case (first spec)
	     (axiom (and (or (eq (first model) 'rule)
			     (eq (first model) 'frule)
			     (eq (first model) 'grule))
			 (equal (cddr spec) (cddr model))))
	     (rule (and (or (eq (first model) 'axiom)
			    (eq (first model) 'frule)
			    (eq (first model) 'grule))
			(equal (cddr spec) (cddr model))))
	     (frule (and (or (eq (first model) 'axiom)
			     (eq (first model) 'rule)
			     (eq (first model) 'grule))
			 (equal (cddr spec) (cddr model))))
	     (grule (and (or (eq (first model) 'axiom)
			     (eq (first model) 'rule)
			     (eq (first model) 'frule))
			 (equal (cddr spec) (cddr model))))
	     (function-stub (and (or (eq (first model) 'function)
				     (eq (first model) 'zf-function))
				 (decl-fields-consistent-p (cddr spec)
							   (cddr model))))))))



;;; Consistency check for a unit being created when its counterpart
;;; already exists.

(defun check-consistency-of-unit (pathname unit-type)
  (with-open-file
   (stream pathname :direction :input :element-type '(unsigned-byte 8))
   (unless stream
     (file-error "open" pathname)
     (return-from check-consistency-of-unit nil)))
  (let ((n 1)
	(db
	 (handler-case
	  (read-gzipped-file pathname)
	  (error (c) nil))))
    (when (null db)
	(parse-error 'file-not-compressed pathname)
	(throw 'error nil))
    (unless (compatible-library-version-p (car db))
	(parse-error 'file-not-valid pathname)
	(throw 'error nil))
    (let ((spec-decls (flatten-decls (mapcar #'strip-modifiers (fifth db))))
	  (model-decls
	   (flatten-decls
	    (mapcar #'(lambda (u)
			(strip-modifiers
			 (zk-output-form
			  (zk-format-event
			   (group-event u)))))
		    (user-history))))
	  (unimplemented-list nil)
	  (inconsistent-list nil))
      ;; The above bindings of spec-decls and model-decls assumes
      ;; the unit being created is a model.  We need to swap the
      ;; bindings if that is not the case.
      (when (eq unit-type 'spec) (swapf spec-decls model-decls))
      (loop for spec in spec-decls
	    for model = (get-matching-decl (second spec) model-decls)
	    do (cond ((null model)
		      (push (second spec) unimplemented-list))
		     ((not (decls-consistent-p spec model))
		      (push (second spec) inconsistent-list))))
      (when inconsistent-list
	(parse-error 'declarations-inconsistent inconsistent-list))
      (when unimplemented-list
	(parse-error 'declarations-unimplemented unimplemented-list))
      (or inconsistent-list unimplemented-list))))

