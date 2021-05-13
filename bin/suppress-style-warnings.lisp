;; to suppress style warnings --load before everything else
;; first form is SBCL-specific, but because of declaim it is ignored by others rather than give error.
;; CCL isn't very chatty anyway.
;; -cem bozsahin
(declaim #+sbcl(sb-ext:muffle-conditions style-warning))
(setf *load-verbose* nil)
(setf *load-print* nil)
(defmacro silent-load (stuff)  ; let defs by Nikodemus Siivola (thanks)
  `(let* ((nada (make-broadcast-stream))
       (*standard-output* nada)
       (*error-output* nada))
     (load ,stuff)))
