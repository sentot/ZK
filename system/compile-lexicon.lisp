
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

(zk-compile-file "lexicon")
