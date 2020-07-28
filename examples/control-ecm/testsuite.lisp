;; testing cecm.ccg

(defparameter *db* '(
  (1 (john persuaded mary to buy the car))
  (2 (john promised mary to buy the car))
  (3 (john wanted mary to buy the car))
  (4 (john expected mary to buy the car))
  (5 (mary considered john handsome))
  (6 (it seemed john bought the car))
  (7 (john seemed to have bought the car))
  (8bad (the car seemed John to have bought))
		     ))

(defun test ()
  (pprint (which-ccglab))
  (format t "~%========~%Testing without type raising~%")
  (lg "cecm")
  (dolist (pair *db*)
    (let ((no (first pair))
	  (exp (second pair)))
      (format t "~2%===== ~A : ~A ===== parsed? ~A~%" no exp (p exp))
      (ders))))

(defun p-aux (num expr targets onto)
  "an aux function to call the parser p. Only derivations onto are shown.
  Lowest types in targets will be eschewed by turning on type-raising."
  (type-raise-targets targets)  ;; NB this does not mean only type-raise cats in 'target'
                                ;; it means eliminate these types during parsing for demo.
  (format t "~%Lowest types ~A will be eliminated~%" targets)
  (p expr)
  (format t "~%Derivations of ~A onto ~A~2%" (list num expr) onto)
  (ders onto)) ; show the derivations onto

(defun test-tr ()
  (pprint (which-ccglab))
  (format t "~%========~%Testing with type raising~% TRC rules: TR derived from a lexical function.~% MLU rules: TR generalized from TRC/MLU rules.~%
	  TRC: type-raise compiler, MLU: most local unifier")
  (tr "cecm" '(v)) ; loads cecm.ccg.lisp and applies TR algorithm to POS=v
  (savetr "cecm-tr.ccg.lisp") ; saves the combined grammar
  (lg "cecm-tr")              ; now resets grammar to one just saved
  (dolist (pair *db*)
    (let ((no (first pair))
	  (exp (second pair)))
      (p-aux no exp '(NP VP PROPP S) 'S))))
