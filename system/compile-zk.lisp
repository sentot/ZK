
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
;;;  DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDERS BE LIABLE FOR  |
;;;  ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR           |
;;;  CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT  |
;;;  OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR |
;;;  BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF         |
;;;  LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT          |
;;;  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE  |
;;;  USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH   |
;;;  DAMAGE.                                                            |
;;;                                                                     |
;;;======================================================================

(make-package "ZK" :use nil)

(defvar *root-directory*
  (namestring (car (directory (merge-pathnames "../")))))

(defvar *source-directory* (concatenate 'string *root-directory* "sources/"))

#+CCL(defvar *object-extension* ".lx64fsl")
#+SBCL(defvar *object-extension* ".fasl")
#+ECL(defvar *object-extension* ".fas")


#+CCL(defvar *subfolder* "CCL/")
#+SBCL(defvar *subfolder* "SBCL/")
#+ECL(defvar *subfolder* "ECL/")


(defvar *salza2-directory*
  (concatenate 'string *source-directory* "salza2-2.0.9/"))

(defvar *salza2-object-directory*
  (concatenate 'string *salza2-directory* *subfolder*))

(defun salza2-load-file (filename)
  (load (concatenate 'string *salza2-object-directory*
                     filename *object-extension*)))

(defun salza2-compile-file (filename)
  (compile-file (concatenate 'string *salza2-directory* filename ".lisp")
                :output-file
		(concatenate 'string *salza2-object-directory*
			     filename *object-extension*)))

(defun salza2-compile-and-load-file (filename)
  (salza2-compile-file filename)
  (salza2-load-file filename))

(defvar *salza2-files*
  '("package" "reset" "specials" "types" "checksum" "adler32"
    "crc32" "chains" "bitstream" "matches" "compress" "huffman"
    "closures" "compressor" "utilities" "zlib" "gzip" "user"))


(defvar *chipz-directory*
  (concatenate 'string *source-directory* "chipz_0.8/"))

(defvar *chipz-object-directory*
    (concatenate 'string *chipz-directory* *subfolder*))

(defun chipz-load-file (filename)
  (load (concatenate 'string *chipz-object-directory*
		     filename *object-extension*)))

(defun chipz-compile-file (filename)
  (compile-file (concatenate 'string *chipz-directory* filename ".lisp")
		:output-file
		(concatenate 'string *chipz-object-directory*
			     filename *object-extension*)))

(defun chipz-compile-and-load-file (filename)
  (chipz-compile-file filename)
  (chipz-load-file filename))

(defvar *chipz-files*
  '("package" "constants" "types-and-tables" "crc32" "adler32"
    "conditions" "dstate" "inflate-state" "gzip" "inflate" "bzip2"
    ;; Gray stream, otherwise stream-fallback
    "decompress" "stream"
    ))


(defvar *trivial-gray-streams-directory*
  (concatenate 'string *source-directory* "trivial-gray-streams-master/"))

(defvar *trivial-gray-streams-object-directory*
  (concatenate 'string *trivial-gray-streams-directory* *subfolder*))

(defun trivial-gray-streams-load-file (filename)
  (load (concatenate 'string *trivial-gray-streams-object-directory*
		     filename *object-extension*)))

(defun trivial-gray-streams-compile-file (filename)
  (compile-file (concatenate 'string *trivial-gray-streams-directory*
			     filename ".lisp")
		:output-file
		(concatenate 'string *trivial-gray-streams-object-directory*
			     filename *object-extension*)))

(defun trivial-gray-streams-compile-and-load-file (filename)
  (trivial-gray-streams-compile-file filename)
  (trivial-gray-streams-load-file filename))

(defvar *trivial-gray-streams-files*
  '("package" "streams"
    ))


(defvar *flexi-streams-directory*
  (concatenate 'string *source-directory* "flexi-streams-1.0.18/"))

(defvar *flexi-streams-object-directory*
  (concatenate 'string *flexi-streams-directory* *subfolder*))

(defun flexi-streams-load-file (filename)
  (load (concatenate 'string *flexi-streams-object-directory*
		     filename *object-extension*)))

(defun flexi-streams-compile-file (filename)
  (compile-file (concatenate 'string *flexi-streams-directory* filename ".lisp")
		:output-file
		(concatenate 'string *flexi-streams-object-directory* filename
			     *object-extension*)))

(defun flexi-streams-compile-and-load-file (filename)
  (flexi-streams-compile-file filename)
  (flexi-streams-load-file filename))

(defvar *flexi-streams-files*
  '("packages" "mapping" "ascii" "koi8-r" "iso-8859"
    "code-pages" "specials" "util" "conditions" "external-format" "length"
    "encode" "decode" "in-memory" "stream" "output" "input" "io" "strings"
    ))


;;; Change if necessary

(defvar *examples-directory*
  (concatenate 'string *root-directory* "examples/"))

(defvar *object-directory*
        (concatenate 'string *source-directory* *subfolder*))

(defun zk-load-file (filename)
  (load (concatenate 'string *object-directory* filename *object-extension*)))

(defun zk-compile-file (filename)
  (compile-file (concatenate 'string *source-directory* filename ".lisp")
                :output-file
                (concatenate 'string *object-directory* filename
                             *object-extension*)))

(defun zk-compile-and-load-file (filename)
  (zk-compile-file filename)
  (zk-load-file filename))

#+ECL(load (concatenate 'string *source-directory* "lexicon"))
#-ECL(zk-load-file "lexicon")

(defvar *zk-files* '(
		     "utilities" "structures" "formulas"
		     "prover-macros" "printer" "errors" "help"
                     "data-structure"
                     "expression-intern" "sum-intern" "reset"
		     "database"
                     "logging" "extra-logging" "checker" "browse"
                     "pivot" "undo-functions"
		     "congruence" "tableau" "closure"
		     "quantifier" "auto-instantiate"
                     "log-integers" "log-simplifier" "assume" "lookup"
                     "ordering" "pattern-match" "trivial" "selection"
		     "reduce" "dnf" "normal"
                     "parser"
                     "commands" "instantiate" "rearrange"
		     "induction" "cases"
                     "knuth-bendix"

                     "zk-header"
                     "library" "initial" "testing"

                     "proof-obligation" "zk-to-lisp"
                     "zk-parser" "zk-wfcheck"
                     "generate-log"
                     "zk-help"
                     "zk-toplevel"

                     "raw-toplevel"))

(defvar zk::*compiling-zk* nil)

(defvar zk::*zk-examples-files*
        (concatenate 'string *examples-directory* "*.ver"))

(defvar zk::*zk-library-directory* "../library/")

(loop for filename in *trivial-gray-streams-files*
      do (trivial-gray-streams-load-file filename))

(loop for filename in *flexi-streams-files*
      do (flexi-streams-load-file filename))

(loop for filename in *salza2-files*
      do (salza2-load-file filename))

(loop for filename in *chipz-files*
      do (chipz-load-file filename))

(loop for filename in *zk-files*
      do (zk-compile-and-load-file filename))

#+CCL(setq *print-pretty* t)
