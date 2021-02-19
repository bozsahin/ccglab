;;; ------------------------------------------
;;; A compiler for type-raising
;;;  -- Cem Bozsahin
;;; ------------------------------------------

(defccglab *ht-tr* nil) ; hash table for derived tr rules--for subsumption check after compile
                        ; key : lex rule key value: lex rule including key as hashtable
(defccglab *VERBS-IN-GRAMMAR* NIL)
(defccglab *lex-item-TEMPLATE* `((KEY nil) (PHON nil) (MORPH nil)
		      (SYN nil)
		      (SEM (LAM P (P X))) (PARAM 1.0)
		      (TAG nil)))
(defccglab *lex-rule-TEMPLATE* `((KEY nil) (INSYN NIL)(INSEM LF)
					(OUTSYN NIL)
					(OUTSEM (LAM LF (LAM P (P LF))))  ; all auto-generated tr rules use these var names--no need for semantic unification
					(INDEX NIL)
					(PARAM 1.0)))  ;; may be different from other parameters if grammar is trained --hhcb
(defccglab *SYNS* NIL)
(defccglab *LAST-KEY-ID* NIL)
(defccglab *ARGS* NIL)
(defccglab *RAISED-LEX-RULES* NIL)
(defccglab *RAISED-LEX-ITEMS* NIL)

;--------get methods----------;

(defun get-morph (v)
  (second (assoc 'MORPH v)))

(defun get-phon (v)
  (second (assoc 'PHON v)))

(defun get-modal-of-dir (l)
	"if it is a complex cat, return the direction's modal if there is any"
	(assoc 'MODAL l))

(defun get-dir (l)
	"get the direction if it is a complex cat"
	(assoc 'DIR l))

(defun get-last-key-id (l)
	"latest key id in the structure---no guarantee that the grammarfile is ordered by key; find the max"
	(setf *LAST-KEY-ID* -1) ; no negatives in translation from .ccg to .ccg.lisp  
	(dolist (e l)
		(if (< *LAST-KEY-ID* (second (assoc 'KEY e)))
		  (setf *LAST-KEY-ID* (second (assoc 'KEY e))))))

(defun get-next-key-id ()
	"increment the last id in the structure and return it"
	(setf *LAST-KEY-ID* (+ 1 *LAST-KEY-ID*)))
	
;---------end of get methods-----------------------;

;-------------set methods-------------;
(defun set-syn (l X)
	"replaces the X in the structure (SYN X)"
	(rplacd (assoc 'syn l) (wrap X)))

(defun set-key (l X)
	"replaces the X in the structure (KEY X)"
	(rplacd (assoc 'key l) (wrap X)))

(defun set-phon (l X)
	"replaces the X in the structure (PHON X)"
	(rplacd (assoc 'phon l) (wrap X)))

(defun set-morph (l X)
	"replaces the X in the structure (MORPH X)"
	(rplacd (assoc 'morph l) (wrap X)))

(defun set-sem (l X)
	"replaces the X in the structure (SEM (LAMP P (P X)))"
	(rplacd (car (reverse (second (assoc 'sem l)))) (wrap X)))

(defun set-index (l X)
	"replaces the X in the structure (INDEX X)"
	(rplacd (assoc 'index l) (wrap X)))

(defun set-insyn (l X)
	"replaces the X in the structure (INSYN X)"
	(rplacd (assoc 'insyn l) (wrap X)))

(defun set-outsyn (l X)
	"replaces the X in the structure (OUTSYN X)"
	(rplacd (assoc 'outsyn l) (wrap X)))
;------------end of set methods-----------------;

(defun find-morph-v (ccg-grammar morphs)
	"find verb morphemes"
	(dolist (entry ccg-grammar)
		(dolist (morph morphs)
			(if (equal morph (get-morph entry))
				(push entry *VERBS-IN-GRAMMAR*)))))


(defun wrap (x)
  "wrap code in parentheses"
  (list x))

(defun is-complex-cat (cat)
	"decide if it's a complex cat"
	(handler-case (assoc 'DIR cat)
		(error (c)
    	(format t "We caught a condition.~&")
    	(values NIL c))))
	
(defun lexical-function (cat)
  "Isolate domain and range of the lexical function for input and output
  of a unary rule for TR, as resp. *ARGS* and *SYNS*.
  We do not iterate over every argument of a lexical function in cat"
  (if (not (is-complex-cat cat)) 
    (return-from lexical-function))
  (let ((dir-of-cat (get-dir cat))
	(modal-of-dir (get-modal-of-dir cat)))
    (if (equal '(DIR BS) dir-of-cat)
      (push (append (wrap (car cat)) (wrap '(DIR FS)) (wrap modal-of-dir) (wrap cat)) *SYNS*) 
      (push (append (wrap (car cat)) (wrap '(DIR BS)) (wrap modal-of-dir) (wrap cat)) *SYNS*))
    (push (car (reverse cat)) *ARGS*) 
    ))

(defun add-tr-to-grammar ()
  "add rules to the currently loaded grammar"
  (setf *ccg-grammar* (append *ccg-grammar* (reverse *RAISED-LEX-RULES*)))
  (format t "~%Type-raising rules added at the end of *ccg-grammar*"))

(defun mk-bcat (bcatht)
  (let ((feats nil)
	(bcat nil))
    (maphash #'(lambda (k v) (if (equal k 'BCAT)
			       (push (list k v) bcat)
			       (push (list k v) feats)))
	     bcatht)
    (append bcat (list (list 'FEATS feats)))))

(defun mk-nonht (ht)
  "return a list of non-hash-valued name-value pairs"
  (let ((feats nil))
    (maphash #'(lambda (k v) (if (not (hash-table-p v)) (push (list k v) feats)))
	     ht)
    (reverse feats)))

(defun mk-cat (synht &optional (res nil))
  (cond ((null synht) res)
	((basicp-hash synht) (append (mk-bcat synht) res)) ; only BCAT and other feats in same synht
	(t (append (list (mk-cat (machash 'RESULT synht)))
		   (mk-nonht synht)
		   (list (mk-cat (machash 'ARG synht)))
		   res))))

(defun mk-rule (key val)
  "turn  hashtable val back to list; for saving. INSYN and OUTSYN are hash values in val"
  (list (list 'INDEX (machash 'INDEX val))
	(list 'KEY key)
	(list 'PARAM (machash 'PARAM val))
	(list 'INSEM (machash 'INSEM val))
	(list 'OUTSEM (machash 'OUTSEM val))
	(list 'INSYN (mk-cat (machash 'INSYN val)))
	(list 'OUTSYN (mk-cat (machash 'OUTSYN val)))))

(defun save-compile (fn &optional (msg ""))
  (add-tr-to-grammar)
  (save-grammar fn)
  (format t "~%compiled~A and saved." msg))

(defun save-subsumption (fn)
  "the result of subsumption is in *ht-tr*."
  (let ((rules nil))
    (maphash 
      #'(lambda (k v)
	  (push (mk-rule k v) rules))
      *ht-tr*)
    (setf *RAISED-LEX-RULES* rules))
  (save-compile fn ", subsumed"))
	   
;;; ------------------------
;;; MLU for rule subsumption, adopted from ccglab's unification without -mlu suffix
;;; in rule subsumption, unlike in projection, we must pass on all local (i.e. basic cat-specific) unifiable features, rather than just check them.
;;; This means in projection we compute MGU, in rule subsumption we compute Most Local Unifier (MLU) to avoid
;;;   global variable generation and general unification.
;;; -hhcb
;;; ------------------------

(defun cat-match-mlu (sht1 sht2)
  (cond ((and (basicp-hash sht1) (basicp-hash sht2))
	 (maphash #'(lambda (feat1 v1)
		      (let ((v2 (machash feat1 sht2)))
			(and v1 v2 (not (var? v1)) (not (var? v2)) (not (equal v1 v2))
			     (return-from cat-match-mlu (values nil)))
			(cond ((var? v1) (remhash feat1 sht1))          ; delete uncommmon or var valued features after unif success
			      ((null v2) (remhash feat1 sht1)))))
		  sht1)
	 (values t))
	((and (complexp-hash sht1) (complexp-hash sht2)
	      (eql (machash 'DIR sht1)(machash 'DIR sht2))
	      (mod-compatiblep (machash 'MODAL sht1) (machash 'MODAL sht2)))
	 (let ((arg1 (copy-hashtable (machash 'ARG sht1)))) 
	   (multiple-value-bind (res1)
	     (cat-match-mlu arg1 (machash 'ARG sht2))  ; arg1 is modified
	     (and res1 (let ((res1 (copy-hashtable (machash 'RESULT sht1)))) 
			 (multiple-value-bind (res2)
			   (cat-match-mlu res1 (machash 'RESULT sht2)) ; arg1 is modified
			   (return-from cat-match-mlu (values res2))))))))
	(t (values nil))))

;---------------------------------------------------------------
;------------to create lex-rule entries-------------------------
;---------------------------------------------------------------

(defun g2 (pname morphs) 
  "identify lexical functions from morphs tag and generate 2nd order case function for their outermost argument"
  (setf *RAISED-LEX-RULES* NIL) ;set to default
  (setf *VERBS-IN-GRAMMAR* NIL)
  (load-grammar pname)  
  (if *error* (progn (format t "~%aborting compile; currently loaded grammar is unchanged")
		     (return-from g2)))
  (find-morph-v *ccg-grammar* morphs)
  (get-last-key-id *ccg-grammar*)
  (dolist (v-entry *VERBS-IN-GRAMMAR*)
    (lexical-function (second (assoc 'SYN v-entry)))  ; sets *SYNS* and *ARGS* --now just one entry in each
    do (let ((temp (copy-alist *lex-rule-TEMPLATE*)))
	 (set-insyn temp (pop *ARGS*))   
	 (set-outsyn temp (pop *SYNS*))
	 (set-key temp (get-next-key-id))
	 (set-index temp (gensym "_G2_"))   ; the rule is as derived by G2
	 (push temp *RAISED-LEX-RULES*)))
  t)

(defun hash-tr ()
  "creates the hash table for inferred rules"
  (setf *ht-tr* (make-hash-table :test #'equal :size (+ (length *RAISED-LEX-RULES*) 10)))
  (dolist (lexr (reverse *RAISED-LEX-RULES*))
    (setf (machash (nv-list-val 'KEY lexr) *ht-tr*) (hash-lexrule lexr))))

(defun p2 ()
  "It uses a hash-table of rules as input, so don't call it standalone.
   v1 and v2 are hash values. INSYN and OUTSYN are hash-valued SYNs due to hash-tr; cat-match needs this."
  (let ((nochange nil))
    (loop  until nochange
	   do
	   (setf nochange t)
	   (maphash 
	     #'(lambda (k1 v1)
		 (maphash 
		   #'(lambda (k2 v2)
		       (if (not (equal k1 k2))
			 (let ((in1 (copy-hashtable (machash 'INSYN v1)))) ; matching changes input, work on copy in case of failure
			   (multiple-value-bind (match1)
			     (cat-match-mlu in1 (machash 'INSYN v2))   ; arg2 is not modified 
			     (and match1
				  (let ((out1 (copy-hashtable (machash 'OUTSYN v1))))
				    (multiple-value-bind (match2)
				      (cat-match-mlu out1 (machash 'OUTSYN v2))  ; arg2 is not modified
				      (and match2     ; if both in and out do not match, they are different rules
					   (let 
					     ((newht (make-lrule-hashtable))
					      (key (get-next-key-id)))  ; keeping keys numeral to be consistent with ccglab
					     (setf (machash 'KEY newht) key)
					     (setf (machash 'INDEX newht) (gensym "_P2_"))  ; P2 derived the rule
					     (setf (machash 'PARAM newht) 1.0)  ; uniform prior for inferred rules
					     (setf (machash 'INSEM newht) 'LF)  ; always the same input abstraction by convention 
					     (setf (machash 'OUTSEM newht) '(LAM LF (LAM P (P LF)))) ; this is universal
					     (setf (machash 'INSYN newht) in1)   ; MGU of input (1st arg modified in basic cats during match)
					     (setf (machash 'OUTSYN newht) out1) ; MGU of output (1st arg modified in basic cats during match)
					     (setf (machash key *ht-tr*) newht) ; added to table as it is looped
					     (setf nochange nil)
					     (remhash k1 *ht-tr*)
					     (remhash k2 *ht-tr*))))))))))  ; cross your fingers for this destructive hash loop
		   *ht-tr*))
	     *ht-tr*))))

(defun g2p2 (gname vmorphs)
  "first finds all rules from grammar file with list of verbal POS in vmrophs, 
  then reduces the rule set to MGUs of pairs iteratively.
  We use hashtables to be compatible with MGU function cat-match---and for efficieny."
  (g2 gname vmorphs) ; result in *RAISED-LEX-RULES* in reverse order of find
  (hash-tr)         
  (p2)
  (format t "~%Number of lexical entries                    : ~A" (length *CCG-GRAMMAR*))
  (format t "~%Number of lexical functions considered       : ~A" (length *VERBS-IN-GRAMMAR*))
  (format t "~%Number of second-order functions generated   : ~A" (length *RAISED-LEX-RULES*))
  (format t "~%Number of paradigmatic functions out of them : ~A" (hash-table-count *ht-tr*))
  (format t "~%Use (mergesave-tr <pn>) to merge and save rules~% with current grammar to <pn>.ccg.lisp")
  )

(abbrevs mergesave-tr save-subsumption) ; add these to help list
(abbrevs tr g2p2)
