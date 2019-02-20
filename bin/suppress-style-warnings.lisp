;; to suppress style warnings --load before everything else
;; this is sbcl-specific, but because of declaim it is ignored by others rather than give error
;; -cem bozsahin

(declaim #+sbcl(sb-ext:muffle-conditions style-warning))
