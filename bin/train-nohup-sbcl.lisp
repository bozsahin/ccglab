;; some nohup-friendly test suite -- all is written offline
;; - cem bozsahin
(defun train-nohup-sbcl (gram gcmb savep out N alpha0 c)
  (progn 
    (setf (sb-ext:bytes-consed-between-gcs) (* gcmb 1024 1024))  ; specify GC cycle in MB
    ; default is 51 MB in sbcl
    (sb-ext:gc) ; make effective immediately
    (time (update-model gram N alpha0 c :load t)) ; cross your fingers
    (show-training)                     ; prayers answered
    (which-ccglab)                      ; for the record
    (and savep (save-training out))     ; session output always to nohup.out when called by ccglab.nohup
    ))
