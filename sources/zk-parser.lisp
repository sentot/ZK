
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


;;; ==================== ZK Parser ====================


;;; The ZK parser uses Lisp read to get an sexp and then ensures that
;;; the sexp is a syntactically correct declaration or command. No
;;; need for a lexer. However, syntax for hexadecimal uses #x or #X
;;; instead of #h or #H.

;;; Separators for names imported from libraries and created by the system.

(defconstant library-separator-char #\!)
(defconstant system-separator-char #\.)

;;; Identifiers that cannot be introduced by a declaration or variable binding.

(defparameter *invalid-declared-identifiers* '(ALL SOME))

;;; ---- Characters that can be part of an identifier.

(defvar *identifier-class*)

;;; Just large enough to be able to properly make *identifier-class*.
(defconstant max-char-code 127)

;;; Set up the identifier class table.

(defun make-identifier-class-table ()
  (setq *identifier-class* (make-array max-char-code
				      :initial-element nil))
  (setf (aref *identifier-class* (char-code #\!)) t)
  (setf (aref *identifier-class* (char-code #\#)) t)
  (setf (aref *identifier-class* (char-code #\$)) t)
  (setf (aref *identifier-class* (char-code #\%)) t)
  (setf (aref *identifier-class* (char-code #\&)) t)
  (setf (aref *identifier-class* (char-code #\*)) t)
  (setf (aref *identifier-class* (char-code #\+)) t)
  (setf (aref *identifier-class* (char-code #\-)) t)
  (setf (aref *identifier-class* (char-code #\.)) t)
  (setf (aref *identifier-class* (char-code #\/)) t)
  (setf (aref *identifier-class* (char-code #\0)) t)
  (setf (aref *identifier-class* (char-code #\1)) t)
  (setf (aref *identifier-class* (char-code #\2)) t)
  (setf (aref *identifier-class* (char-code #\3)) t)
  (setf (aref *identifier-class* (char-code #\4)) t)
  (setf (aref *identifier-class* (char-code #\5)) t)
  (setf (aref *identifier-class* (char-code #\6)) t)
  (setf (aref *identifier-class* (char-code #\7)) t)
  (setf (aref *identifier-class* (char-code #\8)) t)
  (setf (aref *identifier-class* (char-code #\9)) t)
  (setf (aref *identifier-class* (char-code #\<)) t)
  (setf (aref *identifier-class* (char-code #\=)) t)
  (setf (aref *identifier-class* (char-code #\>)) t)
  (setf (aref *identifier-class* (char-code #\?)) t)
  (setf (aref *identifier-class* (char-code #\@)) t)
  (setf (aref *identifier-class* (char-code #\A)) t)
  (setf (aref *identifier-class* (char-code #\B)) t)
  (setf (aref *identifier-class* (char-code #\C)) t)
  (setf (aref *identifier-class* (char-code #\D)) t)
  (setf (aref *identifier-class* (char-code #\E)) t)
  (setf (aref *identifier-class* (char-code #\F)) t)
  (setf (aref *identifier-class* (char-code #\G)) t)
  (setf (aref *identifier-class* (char-code #\H)) t)
  (setf (aref *identifier-class* (char-code #\I)) t)
  (setf (aref *identifier-class* (char-code #\J)) t)
  (setf (aref *identifier-class* (char-code #\K)) t)
  (setf (aref *identifier-class* (char-code #\L)) t)
  (setf (aref *identifier-class* (char-code #\M)) t)
  (setf (aref *identifier-class* (char-code #\N)) t)
  (setf (aref *identifier-class* (char-code #\O)) t)
  (setf (aref *identifier-class* (char-code #\P)) t)
  (setf (aref *identifier-class* (char-code #\Q)) t)
  (setf (aref *identifier-class* (char-code #\R)) t)
  (setf (aref *identifier-class* (char-code #\S)) t)
  (setf (aref *identifier-class* (char-code #\T)) t)
  (setf (aref *identifier-class* (char-code #\U)) t)
  (setf (aref *identifier-class* (char-code #\V)) t)
  (setf (aref *identifier-class* (char-code #\W)) t)
  (setf (aref *identifier-class* (char-code #\X)) t)
  (setf (aref *identifier-class* (char-code #\Y)) t)
  (setf (aref *identifier-class* (char-code #\Z)) t)
  (setf (aref *identifier-class* (char-code #\[)) t)
  (setf (aref *identifier-class* (char-code #\])) t)
  (setf (aref *identifier-class* (char-code #\^)) t)
  (setf (aref *identifier-class* (char-code #\_)) t)
  (setf (aref *identifier-class* (char-code #\{)) t)
  (setf (aref *identifier-class* (char-code #\})) t)
  (setf (aref *identifier-class* (char-code #\~)) t))

(defun identifier-class-p (char)
  (let ((code (char-code char)))
    (and (>= code 0)
	 (<= code max-char-code)
	 (aref *identifier-class* code))))

(defun restricted-identifier-class-p (char)
  (and (identifier-class-p char)
       (not (equal char library-separator-char))
       (not (equal char system-separator-char))))

(eval-when (:load-toplevel)
  (make-identifier-class-table))

;;; Set to non-nil if an error was encountered during parsing.

(defvar *syntax-error-flag*)

;;; Print an error message; return to top level if top-level is non-nil.

(defun syntax-error (msg &optional (top-level t))
  (printer `((:string "Syntax error:")
	     (:string ,msg)
	     (:punctuation ".")))
  (setq *syntax-error-flag* t)
  (when top-level
    (throw 'zk-syntax-error nil)))

;;; Check identifier for invalid characters. The first version is
;;; more restrictive in that the identifier must not have separator
;;; characters in it.

(defun check-decl-name (name)
  (let* ((str (string name))
	 (len (length str)))
    (when (equal (aref str 0) #\#)
      (syntax-error
       (format nil "identifier ~A starts with a '#'" name)))
    (loop for i = 0 then (+ i 1)
	  while (< i len)
	  unless (restricted-identifier-class-p (aref str i))
	  do
	  (syntax-error
	   (format nil "identifier ~A contains an invalid character" name)))))

(defun check-identifier (name)
  (let* ((str (string name))
	 (len (length str)))
    (when (equal (aref str 0) #\#)
      (syntax-error
       (format nil "identifier ~A starts with a '#'" name)))
    (loop for i = 0 then (+ i 1)
	  while (< i len)
	  unless (identifier-class-p (aref str i))
	  do
	  (syntax-error
	   (format nil "identifier ~A contains an invalid character" name)))))


;;; =============== Parsers for Declarations ===============

;;; ===== Functions.

(defpropfun (function parse-function) (sexp)
  (cond ((= (length sexp) 5)
	 (unless (symbolp (second sexp))
	   (syntax-error "function name is not a symbol"))
	 (check-decl-name (second sexp))
	 (parse-variable-list (third sexp))
	 (parse-measure (fourth sexp))
	 (parse-expression (fifth sexp)))
	(t (syntax-error "function declaration is not of proper length"))))

;;; ===== Function stubs.

(defpropfun (function-stub parse-function) (sexp)
  (cond ((= (length sexp) 3)
	 (unless (symbolp (second sexp))
	   (syntax-error "function name is not a symbol"))
	 (check-decl-name (second sexp))
	 (parse-variable-list (third sexp)))
	(t (syntax-error "function stub declaration is not of proper length"))))

;;; ===== ZF functions.

(defpropfun (zf-function parse-function) (sexp)
  (cond ((= (length sexp) 4)
	 (unless (symbolp (second sexp))
	   (syntax-error "function name is not a symbol"))
	 (check-decl-name (second sexp))
	 (parse-variable-list (third sexp))
	 (parse-zf-function-body (fourth sexp)))
	(t (syntax-error "ZF function declaration is not of proper length"))))

(defun parse-zf-function-body (sexp)
  (let ((len (proper-length sexp)))
    (unless len
      (syntax-error "ZF function body not a proper list"))
    (cond ((and (eq (car sexp) 'map) (>= len 3))
	   (parse-zf-map sexp))
	  ((and (eq (car sexp) 'select) (= len 3))
	   (parse-zf-select sexp))
	  ((and (eq (car sexp) 'that) (= len 3))
	   (parse-zf-that sexp))
	  (t (syntax-error "ZF function body is ill-formed")))))

(defun parse-zf-map (sexp)
  (parse-expression (second sexp))
  (loop for s in (cddr sexp)
	do (parse-zf-map-restriction s)))

(defun parse-zf-map-restriction (sexp)
  (unless (equal (proper-length sexp) 2)
    (syntax-error "ZF map restriction is not a list of proper length"))
  (let ((len (proper-length (car sexp))))
    (unless (and len (> len 0))
      (syntax-error "ZF map restriction variable list ill-formed"))
    (parse-variable-list (car sexp))
    (parse-expression (second sexp))))

(defun parse-zf-select (sexp)
  (unless (equal (proper-length (second sexp)) 2)
    (syntax-error "ZF selection group is not a list of proper length"))
  (parse-variable (car (second sexp)))
  (parse-expression (second (second sexp)))
  (parse-expression (third sexp)))

(defun parse-zf-that (sexp)
  (parse-variable (second sexp))
  (parse-expression (third sexp)))

;;; ===== Axioms.

(defpropfun ((axiom rule frule grule) parse-function) (sexp)
  (cond ((= (length sexp) 4)
	 (unless (symbolp (second sexp))
	   (syntax-error (format nil "~A name is not a symbol" (car sexp))))
	 (check-decl-name (second sexp))
	 (parse-variable-list (third sexp))
	 (parse-expression (fourth sexp)))
	(t (syntax-error
	    (format nil "~A declaration is not of proper length" (car sexp))))))

(defun parse-measure (sexp)
  (or (null sexp)
      (cond ((equal (proper-length sexp) 1)
	     (unless (and (equal (proper-length (car sexp)) 2)
			  (eq (caar sexp) 'measure))
	       (syntax-error "ill-formed function measure"))
	     (parse-expression (second (car sexp))))
	    (t (syntax-error
		"function measure is not a list of proper length")))))

;;; Expressions.

(defun parse-expression (sexp)
  (or (integerp sexp)
      (cond ((symbolp sexp) (check-identifier sexp))
	    (t
	     (let ((len (proper-length sexp)))
	       (unless (and len (> len 0))
		 (syntax-error "expression is not a symbol, integer or list"))
	       (cond ((or (eq (car sexp) 'all) (eq (car sexp) 'some))
		      (parse-quantification sexp))
		     (t (parse-function-call sexp))))))))

(defun parse-quantification (sexp)
  (unless (= (length sexp) 3)
    (syntax-error "quantification is ill-formed"))
  (let ((len (proper-length (second sexp))))
    (unless (and len (> len 0))
      (syntax-error "quantification variable list ill-formed"))
    (parse-variable-list (second sexp)))
  (parse-expression (third sexp)))

(defun parse-function-call (sexp)
  (loop for s in (cdr sexp)
	do (parse-expression s)))

(defun parse-variable-list (sexp)
  (unless (proper-length sexp)
    (syntax-error "variable list is not a proper list"))
  (loop for v in sexp
	do (parse-variable v)))

(defun parse-variable (sexp)
  (unless (symbolp sexp)
    (syntax-error "expected variable is not a symbol"))
  (check-identifier sexp))

(defun parse-identifier-list (sexp)
  (unless (proper-length sexp)
    (syntax-error "identifier list is not a proper list"))
  (loop for i in sexp
	do (parse-identifier i)))

(defun parse-identifier (sexp)
  (unless (symbolp sexp)
    (syntax-error "expected identifier is not a symbol"))
  (check-identifier sexp))


;;; =============== Parsers for Commands and Modifiers ===============

;;; ===== Commands with symbol argument and optional expression.

(defpropfun (apply parse-function) (sexp)
  (unless (or (= (length sexp) 2) (= (length sexp) 3))
    (syntax-error "APPLY command is not of proper length"))
  (unless (symbolp (second sexp))
    (syntax-error "applied name is not a symbol"))
  (check-identifier (second sexp))
  (when (= (length sexp) 3)
    (parse-expression (third sexp))))

;;; ===== Commands with string argument.

(defpropfun ((read script set-working-directory set-library dump-log)
	     parse-function)
  (sexp)
  (unless (= (length sexp) 2)
    (syntax-error (format nil "~A command not of proper length" (car sexp))))
  (unless (stringp (second sexp))
    (syntax-error (format nil "string argument expected for ~A" (car sexp)))))

;;; ===== Library commands with unit name and unit type.

(defpropfun ((delete edit make) parse-function) (sexp)
  (unless (= (length sexp) 3)
    (syntax-error (format nil "~A command not of proper length" (car sexp))))
  (unless (symbolp (second sexp))
    (syntax-error "library unit name is not a symbol"))
  (check-identifier (second sexp))
  (unless (or (eq (third sexp) 'spec) (eq (third sexp) 'model)
	      (eq (third sexp) 'freeze))
    (syntax-error "invalid library unit type")))

;;; ===== Commands with symbol argument.

(defpropfun ((load back-thru back-to undo-back-thru undo-back-to
		   print-declaration)
	     parse-function)
  (sexp)
  (unless (= (length sexp) 2)
    (syntax-error (format nil  "~A command not of proper length" (car sexp))))
  (unless (symbolp (second sexp))
    (syntax-error
     (format nil "name argument for ~A is not a symbol" (car sexp))))
  (check-identifier (second sexp)))

;;; ===== Commands with optional integer argument.

(defpropfun ((back browse-back undo) parse-function) (sexp)
  (unless (<= (length sexp) 2)
    (syntax-error (format nil "~A command not of proper length" (car sexp))))
  (when (= (length sexp) 2)
    (unless (integerp (second sexp))
      (syntax-error (format nil "~A argument is not an integer" (car sexp))))))

;;; ===== Commands with optional symbol argument.

(defpropfun ((browse-begin help print-proof print-proof-summary check-proof)
	     parse-function )
  (sexp)
  (unless (<= (length sexp) 2)
    (syntax-error (format nil "~A command not of proper length" (car sexp))))
  (when (= (length sexp) 2)
    (unless (symbolp (second sexp))
      (syntax-error (format nil "~A argument is not a symbol" (car sexp))))
    (check-identifier (second sexp))))

;;; ===== Commands with no argument.

(defpropfun ((browse-forward browse-down browse-up browse-print-formula
              cases conjunctive contradict
              disjunctive end-script next
	      clear-stats print-stats knuth-bendix
              log-on log-off check-all-proofs
	      print-formula print-history print-library-status
	      print-recent-declarations print-working-directory
	      print-status prove prove-by-cases prove-by-induction
	      prove-by-rearrange quit rearrange reduce
	      rebrowse reset retry rewrite simplify
	      trivial-rewrite trivial-simplify trivial-reduce
	      )
	     parse-function)
  (sexp) sexp)

;;; ===== Commands with one or more expression arguments.

(defpropfun ((delete-hypotheses) parse-function) (sexp)
  (unless (>= (length sexp) 2)
    (syntax-error (format nil "~A command not of proper length" (car sexp))))
  (loop for s in (cdr sexp)
	do (parse-expression s)))

;;; ===== Command with one or more variable instantiations.

(defpropfun (instantiate parse-function) (sexp)
  (unless (>= (length sexp) 2)
    (syntax-error "INSTANTIATE command not of proper length"))
  (loop for s in (cdr sexp)
	do (parse-variable-instantiation s)))

(defun parse-variable-instantiation (sexp)
  (unless (equal (proper-length sexp) 2)
    (syntax-error "variable instantiation ill-formed"))
  (parse-variable (car sexp))
  (parse-expression (second sexp)))

;;; ===== Commands with optional expression argument.

(defpropfun ((equality-substitute induct) parse-function)
  (sexp)
  (unless (<= (length sexp) 2)
    (syntax-error (format nil "~A command not of proper length" (car sexp))))
  (when (= (length sexp) 2)
    (parse-expression (second sexp))))

;;; ===== Commands with expression argument.

(defpropfun ((invoke label print-rules-about rules-about split suppose try)
             parse-function)
  (sexp)
  (unless (= (length sexp) 2)
    (syntax-error (format nil "~A command not of proper length" (car sexp))))
  (parse-expression (second sexp)))

;;; ===== Commands with optional variable list.

(defpropfun (prenex parse-function) (sexp)
  (unless (<= (length sexp) 2)
    (syntax-error (format nil "~A command not of proper length" (car sexp))))
  (when (= (length sexp) 2)
    (let ((len (proper-length (second sexp))))
      (unless (and len (>= len 1))
	(syntax-error "list of variables expected"))
      (parse-variable-list (second sexp)))))

;;; ===== Commands with symbol argument and optional variable instantiations.

(defpropfun ((add use) parse-function) (sexp)
  (unless (>= (length sexp) 2)
    (syntax-error
     (format nil "~A command not of proper length" (car sexp))))
  (unless (symbolp (second sexp))
    (syntax-error
     (format nil "first argument of ~A command not a symbol" (car sexp))))
  (check-identifier (second sexp))
  (loop for s in (cddr sexp)
	do (parse-variable-instantiation s)))

;;; ===== Command modifiers with subexpression.

(defpropfun (with-subexpression parse-function) (sexp)
  (unless (= (length sexp) 3)
    (syntax-error
     (format nil "~A command modifier not of proper length" (car sexp))))
  (parse-expression (second sexp))
  (parse-command (third sexp)))

;;; ===== Command modifiers with identifier-list.

(defpropfun ((with-enabled with-disabled) parse-function) (sexp)
  (unless (= (length sexp) 3)
    (syntax-error
     (format nil "~A command modifier not of proper length" (car sexp))))
  (parse-identifier-list (second sexp))
  (parse-command (third sexp)))

;;; Simple command modifiers.

(defpropfun ((disabled with-instantiation without-instantiation
		       with-case-analysis without-case-analysis
		       with-normalization without-normalization)
	     parse-function)
  (sexp)
  (unless (= (length sexp) 2)
    (syntax-error
     (format nil "~A command modifier not of proper length" (car sexp))))
  (parse-command (second sexp)))

;;; ==================== Top Level ====================

;;; ===== Read a ZK sexp and parse it.
;;; Returns one of the following pairs of values:
;;; :EOF	 NIL		end of file
;;; :PARSE-ERROR NIL            a syntax error occurred
;;; :OK          sexp           no errors found

(defun parse-zk-sexp (&optional (stream *standard-input*))
  (let ((sexp (handler-case
	       (read stream nil :eof)
	       (error (c)
		      (catch 'zk-syntax-error
			(syntax-error
			 (format nil "not a valid s-expression")))
		      :PARSE-ERROR))))
    (cond
      ((eq sexp :EOF)
       (values :EOF nil))
      ((eq sexp :PARSE-ERROR)
       (setq *syntax-error-flag* t)
       (values :PARSE-ERROR nil))
      (t
       (setq *syntax-error-flag* nil)
       (catch 'zk-syntax-error (parse-command sexp))
       (if *syntax-error-flag*
	   (values :PARSE-ERROR nil)
	 (values :OK sexp))))))

;;; ===== Dispatcher for parsing declarations and commands.

(defun parse-command (sexp)
  (let ((len (proper-length sexp)))
    (unless (and len (>= len 1))
      (syntax-error "declaration or command is not a non-empty list"))
    (unless (symbolp (car sexp))
      (syntax-error "declaration or command name is not a symbol"))
    (let ((parse-function (get (car sexp) 'parse-function)))
      (when (null parse-function)
	(syntax-error "unrecognized declaration or command"))
      (funcall parse-function sexp))))
