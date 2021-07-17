
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


;;; =============== Scheduler for Egraph and Tableau ===============

;;; Coordinate work between egraph and tableau.
;;; Needed Files: data-structure, congruence, tableau.

;;; All updates to the egraph and tableau go through compute-closure.
;;; In addition to the functions below, intern-expression also
;;; calls compute-closure. This is because grule applications are
;;; triggered by intern-expression, and grule applications
;;; require updates to the egraph and possibly tableau.

;;; When there is work to be done from a merge, forbid, restrict, or kill,
;;; make the egraph and tableau do some work, prioritizing the egraph.
(defun compute-closure ()
  (do ()
      ((and (null *merge-list*)
	    (null *tableau-list*))
       (not *inconsistent*))
    (if *merge-list* (process-merge-list) (process-tableau-list))
    (when *inconsistent* (setq *merge-list* (setq *tableau-list* nil)))))

;;; Schedule a merge and call compute-closure.
(defun merge-nodes (e-node-1 e-node-2 justification)
  (push-fifo (list 'merge e-node-1 e-node-2 justification) *merge-list*)
  (compute-closure))

;;; Schedule a forbid and call compute-closure.
(defun forbid-the-merge (e-node-1 e-node-2 justification)
  (push-fifo (list 'forbid e-node-1 e-node-2 justification) *merge-list*)
  (compute-closure))


;;; Schedule a restrict and call compute-closure.
(defun restrict-node (e-node index justification)
  (push-fifo (list 'restrict e-node index justification) *tableau-list*)
  (compute-closure))

;;; Schedule a kill and call compute-closure.
(defun kill-node (e-node justification)
  (push-fifo (list 'kill e-node justification) *tableau-list*)
  (compute-closure))
