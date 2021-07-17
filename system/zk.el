;;; File:   zk.el - Emacs major mode for ZK editing and Processing
;;; Authors: Irwin Meisels, Sentot Kromodimoeljo

;;; To use this mode, install zk.el in your Emacs lisp directory
;;; (e.g., ~/.emacs.d/lisp/), and put the following in your .emacs file:
;;;
;;; (add-to-list 'load-path "<emacs lisp directory>")
;;; (setq auto-mode-alist (append auto-mode-alist '(("\\.ver$" . zk-mode))))
;;; (autoload 'zk-mode "zk" "ZK mode." t)
;;; (autoload 'run-zk "zk" "Run ZK." t)
;;; (setq zk-program "<pathname of zk program>")

(require 'comint)
(require 'dabbrev)

;;; ZK major mode definitions and functions

(defvar zk-start-command nil
  "String for sending to ZK to start ZK mode. If nil, nothing is sent.")

(defvar zk-proof-summary-command "(print-proof-summary)"
  "String for eliciting a proof summary from ZK in ZK mode.")

(defvar zk-prompt "> *"
  "Regexp to recognize prompts from ZK in ZK mode.")

(defconst zk-proof-commands
    '(add apply back back-thru back-to browse-back browse-begin browse-down
      browse-forward browse-print-formula browse-up cases check-all-proofs
      check-proof clear-stats conjunctive contradict delete-hypotheses
      disjunctive dump-log equality-substitute
      help induct instantiate invoke label
      log-off log-on next prenex print-formula print-proof print-proof-summary
      print-stats print-working-directory
      prove prove-by-cases prove-by-induction prove-by-rearrange
      rearrange rebrowse reduce retry rewrite
      set-library set-working-directory simplify split suppose
      trivial-reduce trivial-rewrite trivial-simplify try use
      with-case-analysis with-disabled with-enabled with-instantiation
      with-normalization with-subexpression without-case-analysis
      without-instantiation without-normalization)       
  "Commands not executed if arg given to zk-evaluate-region")


(defvar zk-mode-map ())
(cond ((null zk-mode-map)
       (setq zk-mode-map (copy-keymap lisp-mode-map))
       (define-key zk-mode-map "\C-c\C-l" 'run-zk)
       (define-key zk-mode-map "\C-c\C-b" 'zk-backward-command)
       (define-key zk-mode-map "\C-c\C-e" 'zk-evaluate-command)
       (define-key zk-mode-map "\C-c\C-f" 'zk-forward-command)
       (define-key zk-mode-map "\C-c\C-r" 'zk-evaluate-region)
       (define-key zk-mode-map "\C-c\C-s" 'zk-print-proof-summary)
       (define-key zk-mode-map "\C-i" 'zk-indent-or-complete)))

(defvar zk-syntax-table nil)
(cond ((null zk-syntax-table)
       (setq zk-syntax-table (copy-syntax-table lisp-mode-syntax-table))
       (modify-syntax-entry ?! "w" zk-syntax-table)
       (modify-syntax-entry ?# "w" zk-syntax-table)
       (modify-syntax-entry ?$ "w" zk-syntax-table)
       (modify-syntax-entry ?% "w" zk-syntax-table)
       (modify-syntax-entry ?& "w" zk-syntax-table)
       (modify-syntax-entry ?* "w" zk-syntax-table)
       (modify-syntax-entry ?+ "w" zk-syntax-table)
       (modify-syntax-entry ?, "w" zk-syntax-table)
       (modify-syntax-entry ?- "w" zk-syntax-table)
       (modify-syntax-entry ?. "w" zk-syntax-table)
       (modify-syntax-entry ?/ "w" zk-syntax-table)
       (modify-syntax-entry ?: "w" zk-syntax-table)
       (modify-syntax-entry ?< "w" zk-syntax-table)
       (modify-syntax-entry ?= "w" zk-syntax-table)
       (modify-syntax-entry ?> "w" zk-syntax-table)
       (modify-syntax-entry ?? "w" zk-syntax-table)
       (modify-syntax-entry ?@ "w" zk-syntax-table)
       (modify-syntax-entry ?\[ "w" zk-syntax-table)
       (modify-syntax-entry ?\] "w" zk-syntax-table)
       (modify-syntax-entry ?> "w" zk-syntax-table)
       (modify-syntax-entry ?^ "w" zk-syntax-table)
       (modify-syntax-entry ?_ "w" zk-syntax-table)
       (modify-syntax-entry ?{ "w" zk-syntax-table)
       (modify-syntax-entry ?\| "w" zk-syntax-table)
       (modify-syntax-entry ?} "w" zk-syntax-table)
       (modify-syntax-entry ?~ "w" zk-syntax-table)
       ))

;;; Set up things for ZK mode.

(defun zk-buffer-setup ()
  (lisp-mode-variables nil)
  (set-syntax-table zk-syntax-table)
  (make-local-variable 'lisp-indent-function)
  (setq lisp-indent-function 'zk-indent-function))

(defun zk-mode ()
  "Major mode for editing ZK programs.
Commands:
Delete converts tabs to spaces as it moves back. Tab indents line if
at the start of a line, or if char before point is not a symbol character,
and completes the symbol otherwise.Blank lines separate paragraphs.
Semicolons start comments.

\\{zk-mode-map}
Entry to this mode runs the hooks on `zk-mode-hook'."
  (kill-all-local-variables)
  (use-local-map zk-mode-map)
  (setq major-mode 'zk-mode)
  (setq mode-name "ZK")
  (zk-buffer-setup)
  (run-hooks 'zk-mode-hook))

(defun zk-forward-command (arg)
  "Move forward to the beginning of the next ZK declaration or command.
With arg, move to the arg'th next one."
  (interactive "p")
  (beginning-of-defun (- arg)))

(defun zk-backward-command (arg)
  "Move backward to the beginning of the current ZK declaration or command.
With arg, move to the beginning of the arg'th previous one."
  (interactive "p")
  (beginning-of-defun arg))

;;; ZK-specific navigation functions for ZK evaluation

;;; If point is at the beginning of, inside, or at the end of a ZK command,
;;; return a cons containing the start and end points of the command.
;;; Otherwise, signals an error.

(defun zk-command-near-point ()
  (let (start end)
    (save-excursion
      (if (or (looking-at "^\\s(")
	      (beginning-of-defun))
	  (setq start (point))
	(error "Can't find start of ZK command."))
      (end-of-defun)
      (setq end (point)))
    (cons start end)))

;;; Return t if pt is inside a ZK command, nil otherwise.

(defun zk-in-command-p (pt)
  (save-excursion
    (goto-char pt)
    (if (beginning-of-defun)
	(progn
	  (forward-sexp)
	  (> (point) pt)))))

;;; Return t if there is a complete ZK command between start and end,
;;; nil otherwise.

(defun zk-command-in-region-p (start end)
  (save-excursion
    (goto-char start)
    (if (or (looking-at "^\\s(")
	    (beginning-of-defun -1))
	(progn
	  (forward-sexp)
	  (<= (point) end)))))

;;; Return non-nil if the ZK command at pt is a proof command,
;;; nil otherwise.

(defun zk-proof-command-p (pt)
  (save-excursion
    (goto-char (1+ pt))
    (forward-sexp)
    (let* ((str (buffer-substring (1+ pt) (point)))
	   (sym (intern-soft str)))
      (or (null sym)
	  (memq sym zk-proof-commands)))))

;;; Find the beginning and end points of all ZK commands in a region.
;;; Returns a list of conses.
;;; If noproof is non-nil, proof commands are ignored.

(defun zk-commands-in-region (noproof start end)
  (let ((pts nil)
	pos)
    (save-excursion
      (if (zk-in-command-p start)
	  (error "Region starts in the middle of a ZK command."))
      (if (zk-in-command-p end)
	  (error "Region ends in the middle of a ZK command."))
      (if (not (zk-command-in-region-p start end))
	  (error "Region contains no ZK commands."))
      (goto-char start)
      (let (pos)
	(while (and (or (looking-at "^\\s(")
			(beginning-of-defun -1))
		    (< (point) end))
	  (if (and noproof
		   (zk-proof-command-p (point)))
	      (end-of-defun)
	    (setq pos (point))
	    (end-of-defun)
	    (setq pts (cons (cons pos (point)) pts))))))
    (nreverse pts)))

;;; ZK indenting

(put 'all 'zk-indent-function 1)
(put 'some 'zk-indent-function 1)
(put 'function-stub 'zk-indent-function 2)
(put 'function 'zk-indent-function 3)
(put 'zf-function 'zk-indent-function 2)
(put 'map 'zk-indent-function 1)
(put 'select 'zk-indent-function 1)
(put 'that 'zk-indent-function 1)
(put 'axiom 'zk-indent-function 2)
(put 'rule 'zk-indent-function 2)
(put 'frule 'zk-indent-function 2)
(put 'grule 'zk-indent-function 2)

;;; zk-indent-function and zk-indent-specform are copied (mostly) from
;;; lisp-mode.el. Both use a global variable to hold some indenting calculation
;;; state, and the name of this variable is different in different versions
;;; of Emacs. Grumble.

(defun zk-indent-function (indent-point state)
  (let ((normal-indent (current-column))
	(last-sexp (if (boundp 'last-sexp)
		       last-sexp
		     calculate-lisp-indent-last-sexp)))
    (goto-char (1+ (elt state 1)))
    (parse-partial-sexp (point) last-sexp 0 t)
    (if (and (elt state 2)
             (not (looking-at "\\sw\\|\\s_")))
        ;; car of form doesn't seem to be a a symbol
        (progn
          (if (not (> (save-excursion (forward-line 1) (point))
                      last-sexp))
              (progn (goto-char last-sexp)
                     (beginning-of-line)
                     (parse-partial-sexp (point) last-sexp 0 t)))
          ;; Indent under the list or under the first sexp on the
          ;; same line as last-sexp.  Note that first thing on that
          ;; line has to be complete sexp since we are inside the
          ;; innermost containing sexp.
          (backward-prefix-chars)
          (current-column))
      (let ((function (buffer-substring (point)
					(progn (forward-sexp 1) (point))))
	    method)
	(setq method (or (get (intern-soft function) 'zk-indent-function)
			 (get (intern-soft function) 'zk-indent-hook)))
	(cond ((or (eq method 'defun)
		   (and (null method)
			(> (length function) 3)
			(string-match "\\`def" function)))
	       (lisp-indent-defform state indent-point))
	      ((integerp method)
	       (zk-indent-specform method state
				     indent-point normal-indent))
	      (method
		(funcall method state indent-point)))))))

(defconst zk-body-indent 2 "")

(defun zk-indent-specform (count state indent-point normal-indent)
  (let ((containing-form-start (elt state 1))
        (i count)
        body-indent containing-form-column)
    ;; Move to the start of containing form, calculate indentation
    ;; to use for non-distinguished forms (> count), and move past the
    ;; function symbol.  lisp-indent-function guarantees that there is at
    ;; least one word or symbol character following open paren of containing
    ;; form.
    (goto-char containing-form-start)
    (setq containing-form-column (current-column))
    (setq body-indent (+ zk-body-indent containing-form-column))
    (forward-char 1)
    (forward-sexp 1)
    ;; Now find the start of the last form.
    (parse-partial-sexp (point) indent-point 1 t)
    (while (and (< (point) indent-point)
                (condition-case ()
                    (progn
                      (setq count (1- count))
                      (forward-sexp 1)
                      (parse-partial-sexp (point) indent-point 1 t))
                  (error nil))))
    ;; Point is sitting on first character of last (or count) sexp.
    (if (> count 0)
        ;; A distinguished form. Use double zk-body-indent.
	(list (+ containing-form-column (* 2 zk-body-indent))
	      containing-form-start)
      ;; A non-distinguished form.  Use body-indent if there are no
      ;; distinguished forms and this is the first undistinguished form,
      ;; or if this is the first undistinguished form and the preceding
      ;; distinguished form has indentation at least as great as body-indent.
      (if (or (and (= i 0) (= count 0))
              (and (= count 0) (<= body-indent normal-indent)))
          body-indent
          normal-indent))))

(defun zk-indent-or-complete (arg)
  "If at the beginning of a line, or the char before point is not a
symbol char, indent the line. Otherwise, try to complete the symbol
before point."
  (interactive "*P")
  (if (bolp)
      (lisp-indent-line arg)
    (let ((cs (char-syntax (preceding-char))))
      (if (or (= cs (char-syntax ?a))
	      (= cs (char-syntax ?_)))
	  (dabbrev-expand arg)
	(lisp-indent-line arg)))))


(defconst zk-keywords
  '("add" "apply" "axiom" "back" "back-thru" "back-to" "browse-back"
    "browse-begin" "browse-down" "browse-forward" "browse-print-formula"
    "browse-up" "cases" "check-all-proofs" "check-proof" "clear-stats"
    "conjunctive" "contradict" "delete-hypotheses" "disjunctive" "dump-log"
    "equality-substitute" "frule" "function" "function-stub" "grule"
    "help" "induct" "instantiate" "invoke" "label" "log-off" "log-on" "next"
    "prenex" "print-formula" "print-proof" "print-proof-summary"
    "print-stats" "print-working-directory"
    "prove" "prove-by-cases" "prove-by-induction"
    "prove-by-rearrange" "rearrange" "rebrowse" "reduce" "reset"
    "retry" "rewrite" "rule" "set-library" "set-working-directory"
    "simplify" "split" "suppose" "trivial-reduce"
    "trivial-rewrite" "trivial-simplify" "try" "use" "with-case-analysis"
    "with-disabled" "with-enabled" "with-instantiation"
    "with-normalization" "with-subexpression" "without-case-analysis"
    "without-instantiation" "without-normalization" "zf-function"))

(defun zk-comint-dynamic-complete-function ()
  (let* ((bds (bounds-of-thing-at-point 'symbol))
              (beg (car bds))
              (end (cdr bds)))
    (list beg end zk-keywords)))

;;; Commands and definitions for running an inferior ZK processor.

;;; Generic ZK definitions, set to specific values by the mode start
;;; functions. The default mode start function is for ZK mode.
;;; These should not be set by the user; set the language-specific variables
;;; instead.

(defun run-zk (&optional arg)
  "Run an inferior ZK process, input and output via buffer *zk*.
With an argument, prompts for the ZK program name and options, otherwise,
uses the values of 'zk-program' and 'zk-program-options'.  The *zk*
buffer is set to ZK mode; see the documentation for zk-mode for details."
  (interactive "P")
  (when (null zk-program)
    (setq zk-program
      (expand-file-name (read-file-name "ZK program: " nil
					zk-program t))))
    (save-window-excursion
      (if (not (comint-check-proc "*zk*"))
	  (let* ((buf (make-comint "zk" zk-program))
		 (proc (get-buffer-process buf)))
            (set-buffer buf)
	    ;; In addition to comint's menu-based completion.
	    (define-key comint-mode-map "\C-i"
	      'completion-at-point)
	    (define-key comint-mode-map "\C-c\C-n"
	      'comint-dynamic-complete-filename)
	    (add-hook 'comint-dynamic-complete-functions
		      #'zk-comint-dynamic-complete-function
		      nil
		      'local)
	    (cond
	     (zk-start-command
	      (comint-send-string proc zk-start-command)
	      (comint-send-string proc "\n")))))
      (setq zk-buffer "*zk*")
      (switch-to-buffer "*zk*"))
    (pop-to-buffer "*zk*"))

;;; Returns the current ZK process, if there is one. Otherwise, signals an
;;; error.

(defun zk-proc ()
  (let ((proc (get-buffer-process "*zk*")))
    (or proc
	(error "No current ZK process."))))

;;; Break up argument string into a list of words.

(defun parse-words-from-string (str)
  (let ((start 0)
	(words nil))
    (while (string-match "[^ \t]+" str start)
      (setq words (cons (substring str (match-beginning 0) (match-end 0))
			words))
      (setq start (match-end 0)))
    (nreverse words)))

;;; Send a string to the inferior ZK process. If the string does not end
;;; in a newline, one is sent to the process.

(defun zk-send-string (cmd &optional display)
  (let ((process (zk-proc)))
    (comint-send-string process cmd)
    (if (not (= (aref cmd (1- (length cmd))) ?\n))
	(comint-send-string process "\n"))))

;;; Like zk-send-string, except a specified region is sent.

(defun zk-send-region (start end)
  (zk-send-string (buffer-substring start end)))

(defun zk-evaluate-command ()
  "Send the ZK command which starts near point to the ZK processor."
  (interactive)
  (let ((pts (zk-command-near-point)))
    (zk-send-region (car pts) (cdr pts))))

(defun zk-evaluate-region (noproof start end)
  "Send all ZK commands between point and mark to the ZK processor.
Point and mark must not be within an ZK command, and there must be
at least one complete ZK command in the region. If noproof is non-nil,
only non-proof commands will be sent to the ZK processor."
  (interactive "P\nr")
  (let ((pts (funcall #'zk-commands-in-region noproof start end)))
    (while pts
      (zk-send-region (car (car pts)) (cdr (car pts)))
      (setq pts (cdr pts)))))

(defvar proc-finished nil)

(defun zk-print-proof-summary ()
  "Insert a proof summary after point in the current buffer."
  (interactive)
  (setq proc-out nil)
  (setq proc-finished nil)
  (let ((process (zk-proc)))
    (set-process-filter process 'zk-insert-process-output)
    (zk-send-string zk-proof-summary-command)
    (while (not proc-finished)
      (accept-process-output process))))

(defun zk-insert-process-output (process str)
  "Insert output from process until zk-prompt is read."
  (insert str)
  (save-excursion
    (beginning-of-line)
    (if (looking-at zk-prompt)
	(progn
	  (replace-match "")		; delete prompt
	  (set-process-filter process 'comint-output-filter)
	  (setq proc-finished t)))))
