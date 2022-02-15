((fstar-mode
  . ((fstar-subp-prover-additional-args
      . (lambda ()
	  (require 'magit)
	  (split-string
	   (string-join
	    (cl-remove-if
	     (lambda (s) (string-match-p "^$" s))
	     (mapcar
	      (lambda (s) (replace-regexp-in-string
			   "--include "
			   (concat "--include "
				   (replace-regexp-in-string
				    "^/ssh.*:/" "/" (file-relative-name (magit-toplevel))))
			   s))
	      (mapcar
	       (lambda (s) (replace-regexp-in-string "[[:space:]]*#.*$" "" s))
	       (split-string
		(with-temp-buffer
		  (insert-file-contents
		   (concat (magit-toplevel) "fstar-args"))
		  (buffer-substring-no-properties
		   (point-min)
		   (point-max)))
		"\n" t)))) " ") " " t))))))
