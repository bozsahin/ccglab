;; this file explains how the throught experiment was conducted step by step
;; run it after you are logged on to ccglab-- it's all Lisp code
;; -cem bozsahin

(defparameter *db* '(
  (john loves mary)
  (mary loves john)
  (john knows mary)
  (mary knows john)
  (mary knows john loves mary)
  (john knows mary loves john)
  ))

(defun prepare-supervision ()
  (make-supervision "g1"))

(defun train-noqnoc ()
  (prepare-supervision)   ; creates g1.sup from g1.supervision --optional if you already have .sup file
  (lg "g1")               ; makes and loads the .ccg.lisp file  from .ccg
  (um "g1" 10 1.0 1.0 :load t)  ; updates g1.ccg.lisp after loading it, using g1.sup
  (st)			; shows training
  (save-training "g1-updated.ccg.lisp")
  )

(defun train-noqnoc-xp ()
  "in case we want to extrapolae the gradient"
  (prepare-supervision)   ; creates g1.sup from g1.supervision --optional if you already have .sup file
  (lg "g1")               ; makes and loads the .ccg.lisp file  from .ccg
  (nf-parse-on)           ; use normal form parsing
  (umxp "g1" 1.0 1.0 :load t)  ; update using extrapolation (fixed to 4 iterations)
  (show-training-xp)	    ; shows training using extrapolation
  (save-training "g1-updated-xp.ccg.lisp")
  )

(defun test-noqnoc (g)
  (lg g) ; this is the trained grammar if you called train-noqnoc before
  (format t "~%---------~%Testing the ~A grammar" g)
  (dolist (ex *db*)
    (format t "~2%======~%all derivations of ~A without ranking~%" ex)
    (p ex)
    (ders)
    (format t "~2%======~%all derivations of ~A with ranking~%" ex)
    (rank ex)
    (status) ; shows the most likely LF
    ))
