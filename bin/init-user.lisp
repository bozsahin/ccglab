;; this code is loaded last in all ccglab calls
;; useful for adding control of switches and extra code
;; in offline training.
;; It is always loaded (so don't delete it) but nothing in it is called by default.
;; Feel free to change it anyway you like.
;; -cem bozsahin, 2019



(defun beam07-app ()
  (setf *beam-exp* 0.7)
  (nf-parse-on)
  (beam-on)
  (setf *f-apply* t)   ;application
  (setf *b-apply* t)
  (setf *f-comp* t)  ;composition
  (setf *b-comp* t)
  (setf *fx-comp* nil)
  (setf *bx-comp* nil)
  (setf *f-sub* nil  )   ;substitution
  (setf *b-sub* nil)
  (setf *fx-sub* nil)
  (setf *bx-sub* nil)
  (setf *f-subbar* nil ) ;substitution bar (aka lost combinator)
  (setf *b-subbar* nil)
  (setf *fx-subbar* nil)
  (setf *bx-subbar* nil)
  (setf *f-subcomp* nil );subcomposition (i.e. D)
  (setf *b-subcomp* nil)
  (setf *fx-subcomp* nil)
  (setf *bx-subcomp* nil)
  (setf *f2-subcomp* nil) ; D^2
  (setf *f2-comp* nil )     ; B^2
  (setf *b2-comp* nil)
  (setf *fx2-comp* nil)
  (setf *bx2-comp* nil)
  (setf *f2-sub* nil )   ;S'' (not S^2 of Curry)
  (setf *b2-sub* nil)
  (setf *fx2-sub* nil)
  (setf *bx2-sub* nil)
  (setf *f3-comp* nil )  ;B^3
  (setf *b3-comp* nil)
  (setf *fx3-comp* nil)
  (setf *bx3-comp* nil)
  )

(defun nobeam-nf-apphcomp ()
  (nf-parse-on)
  (beam-off)
  (setf *f-apply* t)   ;application
  (setf *b-apply* t)
  (setf *f-comp* t)  ;composition
  (setf *b-comp* t)
  (setf *fx-comp* nil)
  (setf *bx-comp* nil)
  (setf *f-sub* nil  )   ;substitution
  (setf *b-sub* nil)
  (setf *fx-sub* nil)
  (setf *bx-sub* nil)
  (setf *f-subbar* nil ) ;substitution bar (aka lost combinator)
  (setf *b-subbar* nil)
  (setf *fx-subbar* nil)
  (setf *bx-subbar* nil)
  (setf *f-subcomp* nil );subcomposition (i.e. D)
  (setf *b-subcomp* nil)
  (setf *fx-subcomp* nil)
  (setf *bx-subcomp* nil)
  (setf *f2-subcomp* nil) ; D^2
  (setf *f2-comp* nil )     ; B^2
  (setf *b2-comp* nil)
  (setf *fx2-comp* nil)
  (setf *bx2-comp* nil)
  (setf *f2-sub* nil )   ;S'' (not S^2 of Curry)
  (setf *b2-sub* nil)
  (setf *fx2-sub* nil)
  (setf *bx2-sub* nil)
  (setf *f3-comp* nil )  ;B^3
  (setf *b3-comp* nil)
  (setf *fx3-comp* nil)
  (setf *bx3-comp* nil)
  )
  (format t "~%init-user.lisp loaded")
