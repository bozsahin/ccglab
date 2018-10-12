;; numbers are indexes to the paper example numbers
;; load this file in CCGlab after you do (load-grammar "fg2018") 
;; then do (db-ders) to see derivations of all examples,
;;   and (db-lfs) just to see LFs only (also reports mishaps)
;; -cem bozsahin may 2018
(defparameter *db* '(                             ; database of examples to be tested
(2 (John persuaded Mary to hit the target) s)
(2a (John persuaded Mary hit the target) s)
(2b(John persuaded Mary to hits the target) s)
(3 (John persuaded Mary to hit Harry) s)
(12a (my team scored every which way) s)
(14 (John kicked and Mary did not kick the bucket) s)
(16 (I picked the book up) s)
(16p (I picked up the book) s)
(18 (the bucket that you kicked) nil)
(19 (Mary dragged and John kicked the bucket) s)
(21a (At any rate you spilled the beans) s)
(21b (You spilled the beans at any rate) s)
(23 (You spilled and Mary cooked the beans) s)
(25 (You spilled and Mary cooked the beans) s)
(25v (You spilled and Mary spilled the beans) s)
(25alt (You spilled the beans) s)
(26 (the beans that you spilled) nil)
(29 (I twiddled my thumbs) s)
(29p (I twiddled his thumbs) s)
(32c (persuade John to do the dishes easily) nil)
))


(defun  db-ders()
  (pprint (which-ccglab))
  (pprint "showing results onto intended categories only")
  (dolist (p *db*)
    (progn (ccg-deduce (second p))
	   (format t "~%=======~%~s~%========~%" (first p))
	   (cky-show-deduction (third p)))))  ; only show results onto intended category in the *db*

(defun  db-lfs()
  (pprint (which-ccglab))
  (dolist (p *db*)
    (progn (ccg-deduce (second p))
	   (format t "~%=======~%~s~%========~%" (first p))
	   (cky-show-lf-eqv))))
