;; this file explains how the throught experiment was conducted step by step
;; run it after you are logged on to ccglab-- it's all Lisp code
;; -cem bozsahin

(defun test-noqnoc ()
  (progn
    (lg "g1")               ; loads the .ded file 
    (sg "g1.ind")           ; saves currently loaded grammar as .ind-- for modeling
    (um "g1" 10 1.0 1.0 :load t)  ; updates g1.ind after loading it, using g1.sup
    (st)			; shows training
    ))

(defun test-noqnoc-xp ()
  "in case we want to extrapolae the gradient"
  (progn
    (lg "g1")               ; loads the .ded file 
    (sg "g1.ind")           ; saves currently loaded grammar as .ind-- for modeling
    (nf-parse-on)           ; use normal form parsing
    (umxp "g1" 1.0 1.0 :load t)  ; updates g1.ind after loading it, using g1.sup
    (show-training-xp)			; shows training
    ))
