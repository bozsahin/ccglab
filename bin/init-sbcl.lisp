;; some nohup-friendly test suite -- all is written offline
;; - cem bozsahin
(defun train-nohup-sbcl (gram gcmb savep out N alpha0 c)
  (progn 
    (setf (sb-ext:bytes-consed-between-gcs) (* gcmb 1024 1024))  ; specify GC cycle in MB
    ; default is 51 MB in sbcl
    (sb-ext:gc) ; make effective immediately
    (time (update-model gram N alpha0 c :load t)) ; cross your fingers
    (show-training)                     ; prayers answered
    (and savep (save-training out))     ; this is to save the grammar---session output always to names with nohup.out when called by ccglab.nohup
    ))

(defun train-nohup-sbcl-xp (gram gcmb savep out alpha0 c)
  "this is the extrapolating version."
  (progn 
    (setf (sb-ext:bytes-consed-between-gcs) (* gcmb 1024 1024))  ; specify GC cycle in MB
    ; default is 51 MB in sbcl
    (sb-ext:gc) ; make effective immediately
    (time (update-model-xp gram alpha0 c :load t)) 
    (show-training-xp)                  
    (and savep (save-training-xp out))  ; this is to save the grammar---session output always to names with nohup.out when called by ccglab.nohup
    ))

(defun nf-and-beam ()
  (basic-ccg :nf-parse t :beam t))

(format t "~%init-sbcl.lisp loaded")
