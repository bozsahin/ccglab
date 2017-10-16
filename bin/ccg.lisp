;;;; =========================================================================== 
;;;; == CCGlab  -Cem Bozsahin, 2015-2017, Ankara, Lisbon                      ==
;;;; ===========================================================================
;;;; 
;;;; GNU GPL license applies.
;;;;
;;;; CCGlab implements all universal rules of CCG and some experimental ones, covering all directional variants of 
;;;;     combination: application, composition, substitution, subcomposition, powers of B, S and O/D and L, 
;;;;     namely B, B^2, B^3 and S^2, and O^2. Type-raising can be implemented as a lexical rule, which 
;;;;     is provided as a mechanism. Meta-categories e.g. those in (X\X)/X of coordination, are assumed to be
;;;;     lexically headed, and allow for application only (because there is no unification, and
;;;;     we make maximal computational use of CCG's procedural neutrality, by which any two adjacent category
;;;;     can only combine one way, if we avoid meta-unifiable cats.)
;;;;
;;;; It also implements probabilistic CCG's (PCCG), including parse ranking and model training, 
;;;;     given the lexicon and its parameters.
;;;;
;;;; - It has four components:
;;;;     1) a transformer to turn paper-style CCG categories to lisp objects,
;;;;     2) a deductive component to CKY-parse a string, 
;;;;     3) an inductive component for PCCG for parse ranking.
;;;;     4) A modeling component to help set/train your parameters for the inductive component.
;;;;
;;;; Some CS-ey notes:
;;;; - It represents offline grammars serially, as lisp lists, and parse objects as hashtables, for speed.
;;;; - CCGlab uses only one Lisp tool: LALR parser of Mark Johnson. Thanks for that. The rest is standard Common Lisp.
;;;; - After seeing the LALR component, you might think CCGlab is a deterministic parser.
;;;;     The LALR subcomponent is used to parse text descriptions of lexical items and rules to Lisp structures,
;;;;     which is deterministic (and probably not SLR, so thanks to MJ again).
;;;;


;;;; ==================================================
;;;; == Lisp Top level needs and some general utilities
;;;; ==================================================

;; a path language layer for multiple gethashes, to write linearly for visibility

(defmacro machash (&rest path)
  "Instead of native (gethash 'F1 (gethash 'F2 ht)), we write (machash 'F1 'F2 ht)
  if ht table has a feature named F2 and the value has feature F1.
  NB.We cannot check at compile-time whether ht is a hashtable. No-one declares them.
  The idea is that only the outermost (F1 above) feature is not necessarily hash-valued."
  (let* ((p (reverse path))
	 (ht (first p))
	 (feats (rest p))
	 (base (list 'gethash (first feats) ht)))
    (if (null feats)
      (error "No feature in hash path:~S ~S~%" ht feats)
      (dolist (feat (rest feats))(setf base (nconc (list 'gethash feat)
						   (list base)))))
    base))

;; Some reader macros and others are defined first to avoid complaints from Lisp compilers. 
;; SBCL can be particularly chatty.
 
(set-macro-character #\!     ; turns !c to "c". Used for LF constants.
  #'(lambda (s char)
      (declare (ignore char))
      (write-to-string (read s t nil t))))

(defmethod print-object ((object hash-table) stream) ;this is for lisp printer to print hashtables, not for mortals
    (format stream "#HASH{~{~{(~A  ~A)~}~^ ~}}"
	 (loop for key being the hash-keys of object
	       using (hash-value value)
	       collect (list key value))))

(defmacro push-t (el st)
  "push element onto stack if el is not nil. eval el only once."
  `(let (($$elr ,el))(and $$elr (push $$elr ,st))))

(defmacro nv-list-val (key nvpl)
  "Returns the value of a list of (name value) pairs nvpl, where each pair's SECOND is the value"
  `(second (assoc ,key ,nvpl)))

;; macros for cky cell's key type (len pos analysis)
(defmacro cell-len (cell)
  `(first ,cell))
(defmacro cell-pos (cell)
  `(second ,cell))
(defmacro cell-ana (cell)
  `(third ,cell))
(defmacro get-cell-param (cell)
  `(machash 'PARAM (nv-list-val 'SOLUTION (machash ,cell *cky-hashtable*))))

(defmacro lex-check (l1 l2)
  "return true if l2 is true when l1 is true, true when l1 is false"
  `(or (not ,l1) ,l2))

;; macros for training table access
(defmacro get-key-param (key)
  `(first (machash ,key *training-hashtable*)))
(defmacro get-key-derivative (key)
  `(rest (machash ,key *training-hashtable*)))
(defmacro put-key-param (key param)
  `(setf (first (machash ,key *training-hashtable*)) ,param))
(defmacro put-key-derivative (key der)
  `(setf (rest (machash ,key *training-hashtable*)) ,der))
(defmacro mk-train-entry (key param der)
  `(setf (machash ,key *training-hashtable*) (cons ,param ,der)))
(defmacro get-param (val)
  `(first ,val))
(defmacro get-derivative (val)
  `(rest ,val))
(defmacro put-param (val param)
  `(setf (first ,val) ,param))
(defmacro put-derivative (key der)
  `(setf (rest (machash ,key *training-hashtable*)) ,der))

;; macros for supervision pairs (Sentence LF)
(defmacro sup-sentence (pair)
  `(first ,pair))
(defmacro sup-lf (pair)
  `(second ,pair))

;; macros for combinators
(defmacro &i ()
  "identity--used only in some LFs empirically, i.e. by the grammarian"
  `(mk-l (mk-v 'x) 'x))
(defmacro  &a (f a)
  "application, which is not a combinator, contrary to common belief, but the primitive of combinators."
  `(mk-a ,f ,a))
(defmacro &b (f g)
  "B combinator"
  `(mk-l (mk-v 'x)(mk-a ,f (mk-a ,g 'x))))
(defmacro &b2 (f g)
  "B^2 combinator"
  `(mk-l (mk-v 'x)(mk-l (mk-v 'y)(mk-a ,f (mk-a (mk-a ,g 'x)'y)))))
(defmacro &b3 (f g)
  "B^3 combinator"
  `(mk-l (mk-v 'x)(mk-l (mk-v 'y)(mk-l (mk-v 'z)(mk-a ,f (mk-a (mk-a (mk-a ,g 'x)'y)'z))))))
(defmacro &s (f g)
  "S combinator"
  `(mk-l (mk-v 'x)(mk-a (mk-a ,f 'x) (mk-a ,g 'x))))
(defmacro &sbar (f g)
  "Sbar combinator, aka the lost combinator"
  `(mk-l (mk-v 'z) (mk-l (mk-v 'w) (mk-a (mk-a ,f 'z) (mk-a ,g 'w)))))
(defmacro &s2 (f g)
  "S^2 combinator. This is actually S'' not Curry's S^2. See Bozsahin 2012"
  `(mk-l (mk-v 'x)(mk-l (mk-v 'y)(mk-a (mk-a ,f 'x) (mk-a (mk-a ,g 'x)'y)))))
(defmacro &o (f g)
  "O combinator, also called D by Hoyt & Baldridge 2008. See Bozsahin 2015 book for discussion."
  `(mk-l (mk-v 'h)(mk-a ,f (mk-l (mk-v 'x)(mk-a ,g (mk-a 'h 'x))))))

;; hash tables
(defun make-lex-hashtable ()
  "keys are: index param sem syn morph phon."
  (make-hash-table :test #'equal :size 7 :rehash-size 2 :rehash-threshold 1.0))

(defun make-lrule-hashtable ()
  "keys are: index param insem outsem insyn outsyn."
  (make-hash-table :test #'equal :size 100 :rehash-size 2 :rehash-threshold 1.0))

(defun make-basic-cat-hashtable (nfeatures)
  "keys are: bcat, and features of the basic cat"
  (make-hash-table :test #'equal :size (+ nfeatures 5) :rehash-size 2 :rehash-threshold 1.0))

(defun make-complex-cat-hashtable ()
  "keys are: dir modal lex result arg."
  (make-hash-table :test #'equal :size 6 :rehash-size 2 :rehash-threshold 1.0))

(defun make-cky-entry-hashtable ()
  "keys are: syn sem index param."
  (make-hash-table :test #'equal :size 5 :rehash-size 2 :rehash-threshold 1.0))

(defun copy-hashtable (ht)
  "To create a fresh copy of ht"
  (let ((new-table (make-hash-table :test (hash-table-test ht)
				    :size (hash-table-size ht))))
    (maphash #'(lambda(key value) 
		 (cond ((eql (type-of value) 'HASH-TABLE)
			(setf (machash key new-table) (copy-hashtable value)))
		       (t (setf (machash key new-table) value))))
	     ht)
    new-table))

(defun make-cky-hashtable (size)
  "keys are: (i j k) where i j k are integers.
  values are: (i1 j1 k1) and (i2 j2 k2), as left and right term
  pointer of combination, and one entry for analysis, with
  type cky-entry-hashtable. The key's value is an assoc list
  of 'left, 'right , and 'solution labels.
  These keys match by structure."
  (make-hash-table :test #'equal :size size :rehash-size size)) ; if data is big, dont spend too much time on rehash

(defun make-lf-hashtable (size)
  "used for finding argmax of most likely LF in the PCCG part. The keys are LF items themselves, so there
  is no search for them. Consequently, key equality can be pretty complex.
  Values are tuples (cump indexes), where cump is scalar-product of the key LF's features, and indexes
  is a list of CKY entries for the cumulative."
  (make-hash-table :test #'equal :size size :rehash-size size)) ; double the size if full; to avoid rehash trashing

(defun make-training-hashtable (n)
  "keys are: lex item keys. they are assumed to be simple symbols.
  Values are :
  for *training-hashtable*: conses, first one is current parameter value, the second one is partial derivative 
  with respect to the lex item with key for the current training pair.
  for *training-non0-hashtable*: value: whether key'd feature has nonzero count in cky parse (for inside-outside)"
  (make-hash-table :test #'equal :size (+ n 100) :rehash-size 1000 :rehash-threshold 1.0))

;;; =======
;;; globals
;;; =======

(defparameter *hash-data-size* 65536)  ; for CKY and LF argmax tables. Make IT REALLY BIG for training sets
                                       ; involving LOOOONG sentences.
				       ; default is 64K entries
;; the following two tables are created only once, and cleared before every parse. Change the variable above and reload ccglab
;; for very long examples and large unpredictable training sets

(defparameter *cky-hashtable* (make-cky-hashtable *hash-data-size*))    ; this is the CKY table keyed by cky loop indices
(defparameter *cky-lf-hashtable* (make-lf-hashtable *hash-data-size*)) ; All LFs for the solution in the cky table.

(setf *print-readably* nil) ; In case you want to look at partial results. Turn it off to avoid print errors.
                            ; (Hard to believe but there is no consistent set of print variable values in CL that
                            ; would allow us to print lists, functions and hashtables readably at the same time.)
(setf *print-pretty* t)     ; NB: defvar does not reset when you re-load this file.
(defparameter *lex-rules-table* nil)  ; this table is global to avoid loading/searching it everytime we parse.
(defparameter *cky-input* nil)        ; current input which engendered the cky-hashtable entries.  
(defparameter *cky-max* nil)          ; current highest ranking result cell in cky table.

;; for beam search in inside-outside computation 
(defparameter *beamp* t)            ; to beam or not to beam (not much of a question for big data)
(defparameter *cky-nparses* 0)      ; *beam* is that number exp'd to *beam-exp*
(defparameter *training-sorted-solutions-list* nil) ; to get out of loops by beam
(defparameter *beam* 0)             ; beam width, determined by number of solutions
(defparameter *beam-exp* 0.9)       ; must be 0 <= x <= 1 . Larger means wider beam

;; more globals
(defparameter *cky-lf-hashtable-sum* 0.0) ; sum of all result LFs inner product
(defparameter *cky-argmax-lf* nil)    ; list of solutions for most likely LF
(defparameter *cky-argmax-lf-max* nil); current highest-ranking cell in cky table for the most likely LF.
(defparameter *cky-lf* nil)           ; LF with the argmax
(defparameter *ccg-grammar* nil)      ; current ccg grammar, as a list of Lisp-translated lex specs
(defparameter *ccg-grammar-keys* nil) ; unique keys for each entry; from 1 to n
(defparameter *loaded-grammar* nil)   ; The source of currently loaded grammar

(defparameter *lfflag* t) ; whether to show intermediate LFs in the output (final one always shown)
(defparameter *abv* nil) ; list of shortcuts for common functions-- see the bottom
;; rule switches

(defparameter *f-apply* t)   ;application
(defparameter *b-apply* t)
(defparameter *f-comp* t)    ;composition
(defparameter *b-comp* t)
(defparameter *fx-comp* t)
(defparameter *bx-comp* t)
(defparameter *f-sub* t)     ;substitution
(defparameter *b-sub* t)
(defparameter *fx-sub* t)
(defparameter *bx-sub* t)
(defparameter *f-subbar* nil)  ;substitution bar (aka lost combinator)
(defparameter *b-subbar* nil)
(defparameter *fx-subbar* nil)
(defparameter *bx-subbar* nil)
(defparameter *f-subcomp* t) ;subcomposition (i.e. D/O)
(defparameter *b-subcomp* t)
(defparameter *fx-subcomp* t)
(defparameter *bx-subcomp* t)
(defparameter *f2-comp* t)   ;B^2
(defparameter *b2-comp* t)
(defparameter *fx2-comp* t)
(defparameter *bx2-comp* t)
(defparameter *f2-sub* t)    ;S'' (not S^2 of Curry)
(defparameter *b2-sub* t)
(defparameter *fx2-sub* t)
(defparameter *bx2-sub* t)
(defparameter *f3-comp* t)   ;B^3
(defparameter *b3-comp* t)
(defparameter *fx3-comp* t)
(defparameter *bx3-comp* t)

(defun switches ()
  (format t  "To change a switch, use (setf <switchname> <value>)
	      where <value> is T (on) or NIL (off)
	  *f-apply*     ~A
	  *b-apply*     ~A
	  *f-comp*      ~A
	  *b-comp*      ~A
	  *fx-comp*     ~A
	  *bx-comp*     ~A
	  *f-sub*       ~A
	  *b-sub*       ~A
	  *fx-sub*      ~A
	  *bx-sub*      ~A
          *f-subbar*    ~A
	  *b-subbar*    ~A
	  *fx-subbar*   ~A
	  *bx-subbar*   ~A
	  *f-subcomp*   ~A
	  *b-subcomp*   ~A
	  *fx-subcomp*  ~A
	  *bx-subcomp*  ~A
          *f2-comp*     ~A
	  *b2-comp*     ~A
	  *fx2-comp*    ~A
	  *bx2-comp*    ~A
	  *f2-sub*      ~A
	  *b2-sub*      ~A
	  *fx2-sub*     ~A
	  *bx2-sub*     ~A
	  *f3-comp*     ~A
	  *b3-comp*     ~A
	  *fx3-comp*    ~A
	  *bx3-comp*    ~A~%"
	  *f-apply* *b-apply* *f-comp* *b-comp* *fx-comp* *bx-comp* *f-sub* *b-sub* *fx-sub* *bx-sub*
          *f-subbar* *b-subbar* *fx-subbar* *bx-subbar* *f-subcomp* *b-subcomp* *fx-subcomp* *bx-subcomp*
          *f2-comp* *b2-comp* *fx2-comp* *bx2-comp* *f2-sub* *b2-sub* *fx2-sub* *bx2-sub* *f3-comp* *b3-comp* 
	  *fx3-comp* *bx3-comp*))

(defun status()
  (format t "~%To see rule switches, do (switches)~%")
  (format t "  To beam or not to beam    : ~A~%" *beamp*)
  (format t " *PRINT-READABLY*           : ~A~%" *print-readably*)
  (format t " *PRINT-PRETTY*             : ~A~%" *print-pretty*)
  (format t "  Currently loaded grammar  : ~A~%" *loaded-grammar*)
  (format t " *CCG-GRAMMAR*              : ~A item~:p~%" (length *ccg-grammar*))
  (format t " *LEX-RULES-TABLE*          : ~A item~:p~%" (length *lex-rules-table*))
  (format t " *CKY-HASHTABLE*            : ~A item~:p~%" (hash-table-count *cky-hashtable*))
  (format t " *CKY-INPUT* for the table  : ~A ~%" *cky-input*)
  (format t "  Most likely LF w/weight   : ~A ~%" *cky-lf*)
  (format t "  Its most likely derivation: ~A~%" *cky-argmax-lf-max*)
  (format t "  Sum of weighted counts    : ~A ~%" *cky-lf-hashtable-sum*)
  (format t "  Most likely LF's cells    : ~A ~%" *cky-argmax-lf*)
  (format t "  Number of differing LFs   : ~A ~%" (hash-table-count *cky-lf-hashtable*))
  (format t "  Most weighted derivation  : ~A ~%" *cky-max*))

(defun which-ccglab ()
  "CCGlab, version 3.4")

(defun welcome()
  (format t "~%===================================================")
  (format t "~%Welcome to ~A" (which-ccglab))
  (format t "~%---------------------------------------------------")
  (status)
  (format t "~%Please send bug reports to cem.bozsahin@gmail.com")
  (format t "~%  with subject line CCGlab: ...")
  (format t "~%Ready.~%")
  (format t "~%===================================================~%"))

(defun beam-value ()
  (format t "*Beamp* = ~A  *Beam-exp* = ~A~%" *beamp* *beam-exp*))

(defun set-beam-exp (val)
  (and (> val 1.0) (format t "Beware! unrealistic beam= ~A~%" val))
  (and (< val 0.6) (format t "Warning! Narrow beam = ~A~%" val))
  (setf *beam-exp* val)
  (beam-value))

(defun beam-off ()
  (setf *beamp* nil)(beam-value))

(defun beam-on ()
  (setf *beamp* t)(beam-value))

(defun beamer ()
  "use this to set beam only after a parse so that *cky-nparses* is known."
  (setf *beam* (ceiling (expt *cky-nparses* *beam-exp*))))

;;;; ==============================================
;;;; The lambda layer, whose syntax is given below.
;;;; ==============================================
;;;;
;;;; this is a direct import of Alessandro Cimatti's ADT for Lambda-calculus. 
;;;; Thanks for putting it on the web.
;;;; (minor addition for our purposes: singleton e can be symbol OR constant)

;;;; The ADT for expressions
;;;; e ::= v | l | a
;;;; v ::= symbolp | constantp
;;;; a ::= ( e e )
;;;; l :: = ( lam v e )

(defun mk-v (sym) sym)
(defun is-v (e) (cond ((consp e) nil)
		      ((symbolp e) t) 
		      ((constantp e) t)
		      ((special-operator-p e) t)
		      (t nil)))
(defun mk-l (v b) (list 'lam v b))
(defun is-l (e) (and (consp e) (= (length e) 3) (equal 'lam (first e)) (is-v (second e))))
(defun l-get-v (l) (second l))
(defun l-get-b (l) (third l))
(defun mk-a (f a) (list f a))
(defun is-a (e) (and (consp e) (= (length e) 2)))
(defun a-get-f (a) (first a))
(defun a-get-a (a) (second a))
(defun freshvar ()(gensym))

;; Recognizer. takes arbitrary s-exp in input

(defun is-e (e)
  (cond ((is-v e) t)
	((is-a e) (and
		    (is-e (a-get-f e))
		    (is-e (a-get-a e))))
	((is-l e) (and
		    (is-e (l-get-v e))
		    (is-e (l-get-b e))))
	(t nil)))

;; Return the free variables of an expression

(defun fv (e)
  (cond
    ((is-v e) (list e))
    ((is-a e) (append
		(fv (a-get-f e))
		(fv (a-get-a e))))
    ((is-l e) (remove
		(l-get-v e)
		(fv (l-get-b e))))
    (t (error "Unknown lambda term type"))))

(defun free-in (v e) (member v (fv e)))

;;; equivalence up to alpha conversion

(defun alpha-equivalent1 (e1 e2 rpl1 rpl2)
  (cond 
    ((is-v e1)
     (and (is-v e2)
	  (let ((new1 (cdr (assoc e1 rpl1)))
		(new2 (cdr (assoc e2 rpl2))))
	    (if (and (null new1) (null new2))
	      (equal e1 e2)
	      (equal new1 new2)))))
    ((is-a e1)
     (and (is-a e2)
	  (alpha-equivalent1 (a-get-f e1) (a-get-f e2) rpl1 rpl2) 
	  (alpha-equivalent1 (a-get-a e1) (a-get-a e2) rpl1 rpl2)))
    ((is-l e1)
     (and (is-l e2)
	  (let* ((new (freshvar))
		 (old1 (l-get-v e1))
		 (old2 (l-get-v e2))
		 (newrpl1 (cons (cons old1 new) rpl1))
		 (newrpl2 (cons (cons old2 new) rpl2)))
	    (alpha-equivalent1 (l-get-b e1) (l-get-b e2) newrpl1 newrpl2))))))

(defun alpha-equivalent (e1 e2)  (alpha-equivalent1 e1 e2 nil nil))

;;; substitution

(defun subst-with-in (x e1 exp)
  (cond 
    ((is-v exp)
     (if (equal x exp) e1 exp))
    ((is-a exp)
     (mk-a
       (subst-with-in x e1 (a-get-f exp))
       (subst-with-in x e1 (a-get-a exp))))
    ((is-l exp) ; say exp is (lam y e)
     (let ((y (l-get-v exp)) (e (l-get-b exp)))
       (cond
	 ((equal x y) exp)
	 ((not (free-in x e)) exp)
	 ((and (free-in x e) (not (free-in y e1)))
	  (mk-l y (subst-with-in x e1 e)))
	 ((and (free-in x e) (free-in y e1))
	  (let ((z (freshvar)))
	    (mk-l z (subst-with-in x e1 (subst-with-in y z e))))))))))

;;; beta reduction

(defun is-rdx (e) (and (is-a e) (is-l (a-get-f e))))
(defun rdx-get-v (rdx) (l-get-v (a-get-f rdx)))
(defun rdx-get-b (rdx) (l-get-b (a-get-f rdx)))
(defun rdx-get-a (rdx) (a-get-a rdx))

;;; Beta reduce: (a (l v e) e1) ==> [e1 / v] e

(defun beta-reduce (rdx)
  (subst-with-in 
    (rdx-get-v rdx)
    (rdx-get-a rdx)
    (rdx-get-b rdx)))

;;; Beta reduce if possible

(defun beta-reduce-if-redex (e)
  (if (is-rdx e) (beta-reduce e) e))

;;; Iterate beta reduction on outermost redex

(defun beta-reduce-outer (e &optional (lim 100))
  (cond
    ((< lim 0) e)
    ((is-rdx e)
     (beta-reduce-outer (beta-reduce e) (- lim 1)))
    ((is-v e) e)
    ((is-a e)
     (mk-a
       (beta-reduce-outer (a-get-f e))
       (beta-reduce-outer (a-get-a e))))
    ((is-l e)
     (mk-l
       (l-get-v e)
       (beta-reduce-outer (l-get-b e))))))

;;; Iterate beta reduction on innermost redex

(defun beta-reduce-inner (e &optional (lim 100))
  (cond
    ((< lim 0) e)
    ((is-v e) e)
    ((is-a e)
     (beta-reduce-if-redex
       (mk-a (beta-reduce-inner (a-get-f e) lim)
	     (beta-reduce-inner (a-get-a e) lim))))
    ((is-l e)
     (mk-l
       (l-get-v e)
       (beta-reduce-inner (l-get-b e) lim)))))

;;; Beta normalization

(defun beta-normalize-param (e fn &optional (lim 100))
  (let* ((res (apply fn (list e lim)))
	 (use-alpha-equivalent t)
	 (stop (if use-alpha-equivalent
		 (alpha-equivalent res e)
		 (equal res e))))
    (if stop
      res ; fix point reached
      (beta-normalize-param res fn))))

(defun beta-normalize-outer (e &optional (lim 100))
  (beta-normalize-param e 'beta-reduce-outer lim))

(defun beta-normalize-inner (e &optional (lim 100))
  (beta-normalize-param e 'beta-reduce-inner lim))

;;; try with the two different strategies and compare results

(defun beta-normalize (e)
  (let ((res-inner (beta-normalize-inner e 100))
	(res-outer (beta-normalize-outer e 100)))
    (if (alpha-equivalent res-outer res-inner)
      (progn 
	(format t "Results are alpha equivalent~%")
	(format t "Inner: ~A~%" res-inner)
	(format t "Outer: ~A~2%" res-outer))
      (progn 
	(format t "Results are NOT alpha-equivalent!")
	(format t "Inner: ~A~%" res-inner)
	(format t "Outer: ~A~2%" res-outer)))))
  
;;;; =============================================================================
;;;; == Part 0: common functions               			               ==
;;;; =============================================================================

(defun format-mod (modality)
  (cond ((eql modality 'CROSS) "+")
	((eql modality 'HARMONIC) "^")
	((eql modality 'STAR) "*")
	(t ""))) ; ALL is default

(defun format-dir (dir lex)
  (if lex 
    (cond ((eql dir 'BS) "\\\\")
	  ((eql dir 'FS) "//")
	  (t ""))
    (cond ((eql dir 'BS) "\\")
	  ((eql dir 'FS) "/")
	  (t ""))))

(defun input-range (len pos)
  "return a subsequence of the current input starting from pos and length long"
  (subseq *cky-input* (- pos 1) (+ (- pos 1) len)))

(defun linearize-syn (synht)
  "turns the syn hashtable synht to a string; avoids features other than BCAT DIR MODAL"
  (cond ((null synht) "")
	((machash 'BCAT synht)(write-to-string (machash 'BCAT synht)))
	(t (if (machash 'LEX synht)  ; don't print modality for LEX slash. it's * anyway.
	     (concatenate 'string
			  (cond ((machash 'DIR 'RESULT synht) "("))
			  (linearize-syn (machash 'RESULT synht))
			  (cond ((machash 'DIR 'RESULT synht) ")"))
			  (format-dir  (machash 'DIR synht) t)
			  (cond ((machash 'DIR 'ARG synht) "("))
			  (linearize-syn (machash 'ARG synht))
			  (cond ((machash 'DIR 'ARG synht) ")")))
	     (concatenate 'string
			  (cond ((machash 'DIR 'RESULT synht) "("))
			  (linearize-syn (machash 'RESULT synht))
			  (cond ((machash 'DIR 'RESULT synht) ")"))
			  (format-dir  (machash 'DIR synht) nil)
			  (format-mod (machash 'MODAL synht)) 
			  (cond ((machash 'DIR 'ARG synht) "("))
			  (linearize-syn (machash 'ARG synht))
			  (cond ((machash 'DIR 'ARG synht) ")")))))))

(defun display-lf (lf &optional (res nil))
  "shorten the keyword LAM as '\' and avoid parenths of currying."
  (cond ((null lf) res)
	((is-v lf) (cons lf res))
	((is-l lf) (let ((x (display-lf (l-get-b lf))))
		     (append (list '|\\| (l-get-v lf) '|\.|) x res)))
	((is-a lf) (let* ((f (display-lf (a-get-f lf)))
			  (y (display-lf (a-get-a lf)))
			  (a (if (and (consp y)(= (length y) 1))
			       (first y)
			       y)))
		     (append f (list a) res)))))

(defun cky-sem (cell)
  "get the lf stored in cky table's cell location. Cells are (i j k) triplets"
  (and (machash cell *cky-hashtable*)
       (machash 'SEM (nv-list-val 'SOLUTION (machash cell *cky-hashtable*)))))

(defun cky-thread (cell)
  "to show (partial) results"
  (let* ((solution (nv-list-val 'SOLUTION (machash cell *cky-hashtable*)))
	 (l (nv-list-val 'LEFT (machash cell *cky-hashtable*)))
	 (r (nv-list-val 'RIGHT (machash cell *cky-hashtable*)))
	 (lf (machash 'SEM solution))
	 (ix (machash 'INDEX solution))
	 (inputs (concatenate 'string
			      (write-to-string (input-range (cell-len l)(cell-pos l)))
			      (write-to-string (input-range (cell-len r)(cell-pos r)))))
	 (syn (linearize-syn (machash 'SYN solution))))
    (cond ((equal l r)   ; we've reached a lexical cell 
	   (cond ((> (cell-len l) 1)
		  (format t (cky-thread l)))) ; it may be a lex rule applying to a phrase
	   (if *lfflag*
	     (format nil "~%~5,,,a~6T~A := ~A~%        : ~A" ix (input-range (cell-len l)(cell-pos l)) syn lf)
	     (format nil "~%~5,,,a~6T~A := ~A" ix (input-range (cell-len l)(cell-pos l)) syn)))
	  (t (concatenate 'string 
			    (cky-thread l)
			    (cky-thread r)
			    (if *lfflag*
			      (format nil "~%~5,,,a~6T~A := ~A~%        : ~A" ix inputs syn lf)
			      (format nil "~%~5,,,a~6T~A := ~A" ix inputs syn)))))))

(defun cky-reveal-cell (cell)
  (format t (cky-thread cell))
  (format t "~2%Final LF, normal-evaluated:~2%~A =~%~A" 
	  (beta-normalize-outer (cky-sem cell))
	  (display-lf (beta-normalize-outer (cky-sem cell)))))

(defun f-param-inner-prod (pr1 pr2)
  "Implements the inner product of f and parameters of Zettlemoyer & Collins (2005) formula 1, 
  dynamic programming-style."
  (+ pr1 pr2))

(defun get-gram-items (phon)
  "given a phonological string, return a list of lex specs for the string."
  (let ((specs nil))
    (dolist (l *ccg-grammar*)
      (and (equal (nv-list-val 'PHON l) phon)(push l specs)))
    specs))

(defun mod-compatiblep (mod1 mod2)
  "checks if two lexical modalities are compatible. Returns t if they are."
  (or (eql mod1 'ALL) (eql mod2 'ALL) (eql mod1 mod2)))

(defun basicp (syntype)
  "Returns non-nil if syntype has BCAT feature at top level, which means it is basic.
  In the morphology of description, special cats are basic. They are non-basic in parsing."
  (nv-list-val 'BCAT syntype))

(defun var? (x)
  "If a feature's value is a local variable, it has the ? prefix."
  (and (symbolp x)(eql (char (symbol-name x) 0) #\?)))

(defun algebraic? (x)
  "If a basic category is an algebraic unknown (NOT a variable), it has the @ prefix.
  Keep in mind that CCG has NO VARIABLES; basic, complex, syncategorematic, or trace."
  (and (symbolp x)(eql (char (symbol-name x) 0) #\@)))

(defun specialp-hash (htsyn)
  "special cats have @ prefix on BCAT and can be complex in result but not in arg.
  This way they maintain procedural neutrality of CCG."
  (cond ((and (machash 'BCAT htsyn)(algebraic? (machash 'BCAT htsyn))))
        ((and (machash 'ARG htsyn)(null (machash 'DIR 'ARG htsyn))
	 (algebraic? (machash 'BCAT 'ARG htsyn))))))

(defun basicp-hash (htsyn)
  "Returns true iff htsyn has no DIR feature, and it is not special."
  (and (null (machash 'DIR htsyn)) (not (specialp-hash htsyn)))) 

(defun complexp-hash (htsyn)
  (and (not (basicp-hash htsyn)) (not (specialp-hash htsyn))))

(defun lexp (spec)
  "Returns non-nil if spec has PHON feature."
  (nv-list-val 'PHON spec))

(defun lexp-hash (ht)
  "Returns the PHON feature of hashtable ht, which is nil only for lexical rules."
  (machash 'PHON ht))

(defun create-syn-table (cat)
  "Creates a hash table, which may contain other hash tables if cat is complex."
  (cond ((basicp cat) 
	 (let ((ht (make-basic-cat-hashtable (length (nv-list-val 'FEATS cat)))))
	   (setf (machash 'BCAT ht) (nv-list-val 'BCAT cat))
	   (dolist (feat-val (nv-list-val 'FEATS cat))
	     (setf (machash (car feat-val) ht) (cadr feat-val)))
	   (return-from create-syn-table ht)))
	(t 		   ; the cat is complex
	  (let ((ht (make-complex-cat-hashtable)))
	    (setf (machash 'DIR ht) (nv-list-val 'DIR cat))
	    (setf (machash 'MODAL ht) (nv-list-val 'MODAL cat))
	    (and (nv-list-val 'LEX cat) (setf (machash 'LEX ht) (nv-list-val 'LEX cat))) ; no LEX feature in hashtable if nil (less consing)
	    (setf (machash 'RESULT ht) (create-syn-table (first cat)))
	    (if (nv-list-val 'LEX cat)
	      (setf (machash 'ARG ht) (create-syn-table (fifth cat))) ; after RESULT DIR MOD LEX
	      (setf (machash 'ARG ht) (create-syn-table (fourth cat)))) ; after RESULT DIR MOD
	    (return-from create-syn-table ht)))))

(defun hash-lex (lexspec)
  "This function turns a sequentially represented CCG lex entry, which consists of 
  Lisp association lists in the lexicalized grammar, to a hashtable, 
  for faster and easier parsing. Called during parsing only."
  (let ((ht (make-lex-hashtable)))
    (setf (machash 'INDEX ht) 'LEX)     ; created by not combining
    (setf (machash 'KEY ht) (nv-list-val 'KEY lexspec))
    (setf (machash 'PARAM ht) (nv-list-val 'PARAM lexspec))
    (setf (machash 'SEM ht) (nv-list-val 'SEM lexspec))
    (setf (machash 'MORPH ht) (nv-list-val 'MORPH lexspec))
    (setf (machash 'PHON ht) (nv-list-val 'PHON lexspec))
    (setf (machash 'SYN ht) (create-syn-table (nv-list-val 'SYN lexspec))) ; this is another hash table
    ht))

(defun hash-lexrule (lexspec)
  "Lexical rules are kept in a global hash table to avoid search and reload.
  This function creates a lexical rule entry to be put in that table."
  (let ((ht (make-lrule-hashtable)))
    (setf (machash 'INDEX ht) (nv-list-val 'INDEX lexspec))     ; lexical rule name
    (setf (machash 'KEY ht) (nv-list-val 'KEY lexspec))
    (setf (machash 'PARAM ht) (nv-list-val 'PARAM lexspec))
    (setf (machash 'INSEM ht) (nv-list-val 'INSEM lexspec))
    (setf (machash 'OUTSEM ht) (nv-list-val 'OUTSEM lexspec))
    (setf (machash 'INSYN ht) (create-syn-table (nv-list-val 'INSYN lexspec)))
    (setf (machash 'OUTSYN ht) (create-syn-table (nv-list-val 'OUTSYN lexspec)))
    ht))

(defun cat-match (sht1 sht2)
  "Checks to see if potentially complex syntactic cat hashtables, sht1 and sht2,
  are slash equivalent, modally compatible, and feature compatible.
  If common features have variable values on both sides, they are not instantiated
  to each other to avoid global variable passing of the HPSG kind.
  E.g. agr=?x in sht1 and agr=?y in sht2, would make first agr ?y.
  There ain't no global variables or complex features.
  There is no unification in CCG. Feature match is simply value match or lack of value.
  Returns 3 values: success of match, local variables and their values in two binding
  lists of the form (feature variable value).
  First list relates to left term, and right list to right term."
  (cond ((and (basicp-hash sht1)(basicp-hash sht2))
	 (let ((binds1 nil)
	       (binds2 nil))
	   (maphash #'(lambda (feat1 v1)  ; check sht1 feats and find binds
			(let ((v2 (machash feat1 sht2)))
			  (and v1 v2 (not (var? v1))(not (var? v2))(not (eql v1 v2)) 
			       (return-from cat-match (values nil nil nil)))
			  (and v2 (var? v1)(not (var? v2))(push (list feat1 v2) binds1))))
		    sht1)
	   (maphash #'(lambda (feat2 v2)  ; find sht2 binds, common features are by now known to match
			(let ((v1 (machash feat2 sht1)))
			  (and v1 (var? v2)(not (var? v1))(push (list feat2 v1) binds2))))
		    sht2)
	   (values t binds1 binds2)))
	((and (complexp-hash sht1)(complexp-hash sht2)
	      (eql (machash 'DIR sht1)(machash 'DIR sht2))
	      (mod-compatiblep (machash 'MODAL sht1) (machash 'MODAL sht2))
	      (multiple-value-bind (res1 b1 b2)
		(cat-match (machash 'ARG sht1)(machash 'ARG sht2))
		(and res1 (multiple-value-bind (res2 b12 b22)
			    (cat-match (machash 'RESULT sht1)(machash 'RESULT sht2))
			    (return-from cat-match (values res2 (append b12 b1) (append b22 b2))))))))
	(t (values nil nil nil))))

(defun realize-binds2 (newht binds)
  "we know that binds is non-empty."
  (cond  ((basicp-hash newht)
	  (dolist (fv binds)
	    (let ((shtval (machash (first fv) newht)))
	      (and (var? shtval)
		   (setf (machash (first fv) newht)(second fv))))))
	 (t (progn (realize-binds2 (machash 'RESULT newht) binds)
		   (realize-binds2 (machash 'ARG newht) binds))))
    newht)

(defun realize-binds (sht binds)
  "Returns the syntactic hashtable sht with matching features in it bound to list of feature-values in 
  binds if same local variable is used.
  It is important to call this function with a local binding list, otherwise we might
  create global variables in CCG. See comments on cat-match.
  It must do the update on fresh copy of sht to avoid changing constituents of combination!"
  (let ((newht (copy-hashtable sht)))
    (cond ((null binds) newht)
	  (t (realize-binds2 newht binds)))))

(defun substitute-special-cat (spht1 catht2)
  "substitutes all categories in special cat spht1 with normal cat catht2.
  To avoid HPSGisation of CCG, we must assume all basic cats in spht1 are special. This way
  we avoid reentrant unification, and this is empirically sound."
  (cond ((null (machash 'DIR spht1)) catht2)
	(t (let ((newsyn (make-complex-cat-hashtable)))
	     (setf (machash 'DIR newsyn) (machash 'DIR spht1))  ; slash projects
	     (setf (machash 'MODAL newsyn) (machash 'MODAL spht1)) 
	     (and (machash 'LEX spht1) (setf (machash 'LEX newsyn) (machash 'LEX spht1)))
	     (setf (machash 'RESULT newsyn)(substitute-special-cat (machash 'RESULT spht1) catht2)) ; arg and res substitute
	     (setf (machash 'ARG newsyn)(substitute-special-cat (machash 'ARG spht1) catht2))
	     newsyn))))

(defmacro parse/2 (words)
  "sticks in the end marker to pass on to lalrparser's overridden parse function in ccglab.
  This is the list it expects."
  `(parse (append ,words (list *ENDMARKER*))))

(defun lispify-project (pname maker)
   "reads paper-style tokenized specs for the project pname, and feeds that into 
  parse/1 to generate pname.ded"
   (let ((ofilename (concatenate 'string pname ".ded"))
	 (infilename (concatenate 'string pname ".lisptokens")))
     (case maker ;; one of these will generate .lisptokens
       (sbcl (run-program "tokens" (list pname) :search t :wait t))
       (ccl  (run-program "tokens" (list pname)))
       (clisp (run-program "tokens" :arguments (list pname) :wait t))
       (otherwise (format t "~%Reading from off-line generated ~A" infilename)))
     (with-open-file (strm infilename :direction :input :if-does-not-exist :error)
       (with-open-file (s ofilename  :direction :output :if-exists :supersede)
	 (setf *ccg-grammar-keys* 0)
	 (format s "~A" (parse/2 (read strm))))) ; this is the interface to LALR transformer's parse
     (format t "~%=========================== p r e p a r i n g ===============================~%")
     (format t "~%Project name: ~A~%  Input : ~A ~%  Output: ~A ~%Check to see if output contains any spec errors.~%Fix and re-run if it does." pname infilename ofilename)
     (format t "~%You can also re/create ~A by running 'tokens ~A' sed script offline." infilename pname)))

(defun lispify-supervision (pname maker)
   "reads semicolon-terminated supervision pairs and forms the token file pname.suptokens"
   (let ((ofilename (concatenate 'string pname ".sup"))
	 (infilename (concatenate 'string pname ".suptokens")))
     (case maker ;; one of these will generate .suptokens
       (sbcl (run-program "suptokens" (list pname) :search t :wait t))
       (ccl  (run-program "suptokens" (list pname)))
       (clisp (run-program "suptokens" :arguments (list pname) :wait t))
       (otherwise (format t "~%Reading from off-line generated ~A" infilename)))
     (with-open-file (strm infilename :direction :input :if-does-not-exist :error)
       (with-open-file (s ofilename  :direction :output :if-exists :supersede)
	 (format s "~A" (parse/2 (read strm))))) ; this is the interface to LALR transformer's parse
     (format t "~%=========================== p r e p a r i n g ===============================~%")
     (format t "~%Project name: ~A~%  Input : ~A ~%  Output: ~A ~%Check to see if output contains any spec errors.~%Fix and re-run if it does." pname infilename ofilename)
     (format t "~%You can also re/create ~A by running 'suptokens ~A' sed script offline." infilename pname)))

(defun load-project (pname pfile)
  (let* ((sname (concatenate 'string pname ".ccg"))
	 (tname (concatenate 'string pname ".lisptokens"))
	 (gname (concatenate 'string pname ".ded"))
	 (mname (concatenate 'string pname ".ind"))
	 (cname (concatenate 'string pname ".lisp"))
	 (suname (concatenate 'string pname ".sup"))
	 (lfile (if (eq pfile 'model) mname gname)))
    (format t "~%======================= l o a d i n g =======================================~%")
    (cond ((load lfile :verbose t :if-does-not-exist nil) ; this will set the *ccg-grammar* list 
	   (setf *lex-rules-table* nil)
	   (setf *loaded-grammar* lfile)
	   (dolist (l *ccg-grammar*)(and (not (lexp l)) (push-t (hash-lexrule l) *lex-rules-table*))) ; we get reversed list of rules
	   (setf *lex-rules-table* (reverse *lex-rules-table*)) ; it is important that the rules apply in the order specified
	   (format t "~%Project [~A] is assumed to consist of" pname)
           (format t "~%-----------------------------------------------------------------------------")
	   (format t "~%  CCG grammar source : ~A $" sname)
	   (format t "~%    Its token form   : ~A $" tname)
	   (format t "~%  Deduction grammar  : ~A $ (derived from ~A)" gname tname)
	   (format t "~%  Induction grammar  : ~A #" mname)
	   (format t "~%  Supervision source : ~A ^" suname)
	   (format t "~%  Model-specific code: ~A ^" cname)
	   (format t "~%   and other model-specific files you may create.")
	   (format t "~%       *CCG-GRAMMAR* : set from ~A" lfile)
	   (format t "~%  *LEX-RULES-TABLE*  : set from ~A" lfile)
	   (format t "~%Expected files       : $ for deduction, # for induction, ^ for model development")
	   (format t "~%=============================================================================~%")
	   t)
	  (t (format t "Project ~A cannot be loaded:" pname)
	     (format t "~%  *ccg-grammar* is unchanged.")
	     (format t "~%  *lex-rules-table* is unchanged.~%")
	     nil))))

(defun load-model (pname)
  (load-project pname 'model))


(defun load-grammar (pname &key (maker nil))
  "Prepares and loads a Lisp-translated CCG grammar, and prepares the lexical rule hashtable for the project."
  (and maker (lispify-project pname maker)) ; generates the .ded file and/or .lisptokens file 
  (load-project pname 'grammar))

(defun get-ht (phon ht-list)
  "returns the hashtable in ht-list that has PHON feature same as phon.
  Used for testing purposes only."
  (dolist (ht ht-list)(and (eql phon (machash 'PHON ht)) (return-from get-ht ht))))

(defun cky-pprint ()
  "Tries to pretty print cky table as much as it can. Hashtable and closure prints are
  up to your lisp printer variables and CL implementation, aka insallah printing.
  For testing purposes only."
  (maphash #'(lambda (k v) (format t "~%~A = ~A~%" k v)) *cky-hashtable*))

(defun cky-show-der (row col)
  "tries to print the derivations ending in CKY cell (row col) as humanly as possible. Only final result is
  normalized in its LF."
  (do ((m 1 (incf m)))
    ((null (machash (list row col m) *cky-hashtable*)))
    (format t "~2%Derivation ~A~%--------------" m)
    (format t (cky-thread (list row col m)))
    (format t "~2&Final LF, normal-order evaluated: ~2%    ~A =~%    ~A" 
	    (beta-normalize-outer (cky-sem (list row col m)))
	    (display-lf (beta-normalize-outer (cky-sem (list row col m))))))
  (format t "~2&Try (cky-pprint) to see the details including the features and slash modalities.")
  (format t  "~&    (cky-reveal-cell <cell>) to pretty-print the parse in <cell>."))

(defun cky-show-normal-forms (row col)
   (do ((m 1 (incf m)))
     ((null (machash (list row col m) *cky-hashtable*)))
     (format t "~2%Derivation ~A~%----------------~%" m)
     (beta-normalize (cky-sem (list row col m)))))

(defun cky-show-deduction ()
  "the answer is in first column of row n, which is the length of the string."
  (cky-show-der (length *cky-input*) 1))

(defun cky-show-lf-eqv ()
  "does one check: evaluate results in normal and applicative order, and report differences"
  (cky-show-normal-forms (length *cky-input*) 1))


;;;; ============================================================================
;;;; ==   Part 1.1 - The grammar for the LALR parser                           ==
;;;; ============================================================================

;;; load-transformer/x functions are LALR grammars for converting source x to target x
;;;   for example ccg text source to target ccg code that can be loaded, or supervision
;;;   source data to loadable data.
;;; Any transform function must specify 4 globals: grammar lexicon lexforms *endmarker*
;;;
;;; Unfortunately, lalrparser.lisp is not publicized as a package so we need to recreate
;;; grammars when we have more than one. lalr-parser function will be different in each case,
;;; but parse function is the same for our purposes.

(defun load-transformer/ccg ()
  "LALR grammar for transforming text ccg to Lisp structures"
;; LALR parser demands lexical insertion by a pre-terminal for every terminal
;; (i.e. do not use constants in the RHSs of lalr rules)
;;  NB: We must have ID tag in 'lexforms' although there is nothing with that tag in the lexicon!
;;  NB2: As much as I wanted to keep CCG's / and \ in the data, Lisp readers do
;;       implementation-dependent stuff with special symbol \, even if you enclose it within '|'s. 
;;       The parser will replace them with FS and BS. We live in sad times.
  (defparameter grammar 
    '((gram    --> start              #'(lambda (start) (list 'defparameter '*ccg-grammar* `(quote ,start))))
      (start   --> start lex END      #'(lambda (start lex END) (declare (ignore END))(append start (list lex))))
      (start   --> lex END            #'(lambda (lex END)(declare (ignore END))(list lex)))
      (lex     --> ID mtag SPECOP cat #'(lambda (ID mtag SPECOP cat)
					  (declare (ignore SPECOP))
					  (progn (incf *ccg-grammar-keys*)
									   (list (list 'KEY *ccg-grammar-keys*)
										 (list 'PHON (cadr ID)) 
										 mtag (first cat) (second cat) (list 'PARAM 1.0)))))
      (lex     --> lrule 		  #'(lambda (lrule)(progn (incf *ccg-grammar-keys*)
								  (list (list 'KEY *ccg-grammar-keys*)
									(list 'INSYN (second (first (rest (first lrule)))))
									(list 'INSEM (second (second (rest (first lrule)))))
									(list 'OUTSYN (second (second lrule)))
									(list 'OUTSEM (second (third lrule)))
									(list 'INDEX (second (first (first lrule))))  ; rule name
									(list 'PARAM 1.0)))))
      (lrule   --> LP ID RP cat1 
	       ARROW cat              #'(lambda (LP ID RP cat1 ARROW cat)
					  (declare (ignore LP RP ARROW))
					  (cons (cons ID cat1) cat))) 
      (mtag    --> ID		      #'(lambda (ID)(list 'MORPH (cadr ID))))
      (cat1    --> cat		      #'(lambda (cat)(identity cat)))
      (cat     --> syns COLON lf      #'(lambda (syns COLON lf)
					  (declare (ignore COLON))
					  (cons (list 'SYN syns) (list (list 'SEM lf)))))
      (syns    --> basic              #'(lambda (basic)(identity basic)))
      (syns    --> parentd            #'(lambda (parentd)(identity parentd)))
      (syns    --> syns slash syn     #'(lambda (syns slash syn)`(,syns ,@slash ,syn)))
      (syn     --> basic              #'(lambda (basic)(identity basic)))
      (syn     --> parentd            #'(lambda (parentd)(identity parentd)))
      (basic   --> ID feats           #'(lambda (ID feats)(list (list 'BCAT (cadr ID)) (list 'FEATS feats))))
      (parentd --> LP syns RP         #'(lambda (LP syns RP) (declare (ignore LP RP))(identity syns)))
      (slash   --> vardir varmod      #'(lambda (vardir varmod)(list vardir varmod)))
      (slash   --> vardouble          #'(lambda (vardouble)(identity vardouble)))
      (feats   --> LB eqns RB 	      #'(lambda (LB eqns RB) (declare (ignore LB RB))(identity eqns)))
      (feats                          #'(lambda () nil))
      (eqns    --> eqns COMMA eqn     #'(lambda (eqns COMMA eqn)(declare (ignore COMMA))(append  eqns (list eqn))))
      (eqns    --> eqn                #'(lambda (eqn)(list eqn)))
      (eqn     --> ID1 EQOP ID        #'(lambda (ID1 EQOP ID)(declare (ignore EQOP))(list (cadr ID1) (cadr ID))))
      (ID1     --> ID		      #'(lambda (ID) (identity ID)))
      (vardouble --> VALFS2 VALFS     #'(lambda (VALFS2 VALFS)
					  (declare (ignore VALFS2 VALFS))
					  (list (list 'DIR 'FS)(list 'MODAL 'STAR)(list 'LEX t))))
      (vardouble --> VALBS2 VALBS     #'(lambda (VALBS2 VALBS)
					  (declare (ignore VALBS2 VALBS))
					  (list (list 'DIR 'BS)(list 'MODAL 'STAR)(list 'LEX t))))
      (VALFS2  --> VALFS              #'(lambda (VALFS)(identity VALFS)))
      (VALBS2  --> VALBS              #'(lambda (VALBS)(identity VALBS)))
      (vardir  --> VALFS              #'(lambda (VALFS)(declare (ignore VALFS))(list 'DIR 'FS)))
      (vardir  --> VALBS              #'(lambda (VALBS)(declare (ignore VALBS))(list 'DIR 'BS )))
      (varmod  --> MODAL              #'(lambda (MODAL)(cond ((equalp (cadr MODAL) '^) (list 'MODAL 'HARMONIC))
							     ((equalp (cadr MODAL) '+) (list 'MODAL 'CROSS))
							     ((equalp (cadr MODAL) '*) (list 'MODAL 'STAR))
							     (t (list 'MODAL '*UNKNOWN*)))))
      (varmod  --> VALDOT             #'(lambda (VALDOT)(declare (ignore VALDOT))(list 'MODAL 'ALL)))
      (varmod  -->                    #'(lambda ()(list 'MODAL 'ALL)))
      (vardot  --> VALDOT	      #'(lambda(VALDOT)(declare (ignore VALDOT))(identity nil)))
      (vardot  -->                    #'(lambda()(identity nil)))
      (lf      --> bodys              #'(lambda (bodys)(identity bodys)))
      (lf      --> lterm              #'(lambda (lterm)(identity lterm)))
      (lterm   --> VALBS ID vardot 
	       lbody                  #'(lambda (VALBS ID vardot lbody)
					  (declare (ignore VALBS vardot))
					  (mk-l (mk-v (cadr ID)) lbody)))
      (lbody   --> lterm              #'(lambda (lterm)(identity lterm)))           ; lambda bindings are right-associative.
      (lbody   --> bodys              #'(lambda (bodys)(identity bodys)))
      (bodys   --> bodys body         #'(lambda (bodys body)(mk-a bodys body)))     ; LF concatenation is left-associative. 
      (bodys   --> body               #'(lambda (body)(identity body)))
      (body    --> LP bodys RP        #'(lambda (LP bodys RP)
					  (declare (ignore LP RP))
					  (identity bodys)))     ; in lexical specs, we don't expect inner lambdas in the LF body.
      (body    --> ID                 #'(lambda (ID)(cadr ID)))
      ))
  (defparameter lexforms '(VALFS ID MODAL END VALBS 
				 VALDOT SPECOP COLON ARROW
				 LP RP LB RB COMMA EQOP))
  (defparameter lexicon '((|/| VALFS)
			  (\\ VALBS)
			  (\^ MODAL)
			  (\* MODAL)
			  (\+ MODAL)
			  (|.| VALDOT)
			  (|,| COMMA)
			  (\; END)
			  (|:=| SPECOP)
			  (|:| COLON)
			  (|-->| ARROW)
			  (|(| LP)
	                  (|)| RP)
			  (|[| LB)
         		  (|]| RB)
			  (|=| EQOP)
			  ($ $)        ; this is for lalrparser.lisp's end of input
			  ))
  ;; if you change the end-marker, change its hardcopy above in lexicon above as well.
  ;; (because LALR parser does not evaluate its lexicon symbols---sorry.)
  (defparameter *ENDMARKER* '$)  
  ) ; of tranformer/ccg

;;; to automatically generate the parser by LALR parser generator

(defun make-lalrparser ()
  "makes the lalr-parser function used by parse below"
  (compile (eval (make-parser grammar lexforms *ENDMARKER*)))) 

(defun make-transformer/ccg ()
  (load-transformer/ccg)
  (make-lalrparser))

(make-transformer/ccg)

(defun parse (words)
  "Overriding lalrparser.lisp's parse/1 function. We must do this to return any symbol 
   which is not in the 'lexicon' list to be returned as ID type.
  This is NOT the CKY parser. It LALR parses textual definitions onto CCG specs."

  (labels ((lookup (word)
                   (cadr (assoc word lexicon)))
           (next-input ()
                       (let* ((word (pop words))
                              (cat (lookup word)))
                         (cond (cat (cons cat                     ; category if it exists, and
                                          (list cat word)))       ; value
			       ((typep word 'string)              ; a quoted multiword entry, make it Lisp string
				(cons 'ID (list 'ID (concatenate 'string "\"" word "\""))))
                               (t (cons 'ID (list 'ID word))))))  ; if not in lexicon, take as ID.
				
           (parse-error ()
                        (format nil "Error before ~A" words)))
    (lalr-parser #'next-input #'parse-error)))


;;;; ====================
;;;  = Part 1.2 LALR parser for .supervision files
;;;  ====================

(defun load-transformer/sup ()
  "LALR grammar for transforming supervision files to Lisp structures"
;; LALR parser demands lexical insertion by a pre-terminal for every terminal
;; (i.e. do not use constants in the RHSs of lalr rules)
;;  NB: We must have ID tag in 'lexforms' although there is nothing with that tag in the lexicon!
  (defparameter grammar 
    '((gram    --> start              #'(lambda (start) (identity start)))
      (start   --> start lex END      #'(lambda (start lex END) (declare (ignore END))(append start (list lex))))
      (start   --> lex END            #'(lambda (lex END)(declare (ignore END))(list lex)))
      (lex     --> ids COLON lf       #'(lambda (ids COLON lf)(declare (ignore COLON))(append (list ids) (list lf))))
      (ids     --> ids ID             #'(lambda (ids ID)(append ids (list (second ID)))))
      (ids     --> ID                 #'(lambda (ID)(list (second ID))))
      (vardot  --> VALDOT             #'(lambda(VALDOT)(declare (ignore VALDOT))(identity nil)))
      (vardot  -->                    #'(lambda()(identity nil)))
      (lf      --> bodys              #'(lambda (bodys)(identity bodys)))
      (lf      --> lterm              #'(lambda (lterm)(identity lterm)))
      (lterm   --> VALBS ID vardot 
         	       lbody          #'(lambda (VALBS ID vardot lbody)
					  (declare (ignore VALBS vardot))
					  (mk-l (mk-v (second ID)) lbody)))
      (lbody   --> lterm              #'(lambda (lterm)(identity lterm)))           ; lambda bindings are right-associative.
      (lbody   --> bodys              #'(lambda (bodys)(identity bodys)))
      (bodys   --> bodys body         #'(lambda (bodys body)(mk-a bodys body)))     ; LF concatenation is left-associative. 
      (bodys   --> body               #'(lambda (body)(identity body)))
      (body    --> LP bodys RP        #'(lambda (LP bodys RP)
					  (declare (ignore LP RP))
					  (identity bodys)))     ; in lexical specs, we don't expect inner lambdas in the LF body.
      (body    --> ID                 #'(lambda (ID)(second ID)))
      ))
  (defparameter lexforms '(ID END VALBS 
				 VALDOT COLON 
				 LP RP))
  (defparameter lexicon '((|.| VALDOT)
			  (\\ VALBS)
			  (|,| COMMA)
			  (\; END)
			  (|:| COLON)
			  (|(| LP)
	                  (|)| RP)
			  ($ $)        ; this is for lalrparser.lisp's end of input
			  ))
  ;; if you change the end-marker, change its hardcopy above in lexicon above as well.
  ;; (because LALR parser does not evaluate its lexicon symbols---sorry.)
  (defparameter *ENDMARKER* '$)  
  )

(defun make-transformer/sup ()
  (load-transformer/sup)
  (make-lalrparser))

(defun make-supervision (pname &key (maker nil))
  "Makes a lisp-ready pname.sup file from pname.supervision and pname.suptokens."
  (or maker (format t "Need a maker!~%") (return-from make-supervision))
  (let ((ofilename (concatenate 'string pname ".sup"))
	(sourcefile (concatenate 'string pname ".supervision"))
	(infilename (concatenate 'string pname ".suptokens")))
    (make-transformer/sup)
    (lispify-supervision pname maker)
    (make-transformer/ccg) ; reset to CCG input parsing because there can be one LALR grammar at any time
    (format t "~%=========================== p r e p a r i n g ===============================~%")
    (format t "~%Project name: ~A~%  Input : ~A and ~A~%  Output: ~A ~%Check to see if output contains any spec errors.~%Fix and re-run if it does." pname sourcefile infilename ofilename)
    (format t "~%You can also re/create ~A by running 'suptokens ~A' sed script offline." infilename pname)))

;;;; =============================================================================
;;;; == Part 2: The CKY parser for CCG -- the deductive component               ==
;;;; =============================================================================

;;;; CRITICAL NOTES ABOUT CCG's lambda forms and CL lambda forms:
;;;
;;;; 1) We assume the input functions are curried.
;;;; 2) CL does not like to re-define constants, hence defining LF constants as Lisp
;;;;  constants wouldn't work since it's very likely that they overlap in your lexicon. 
;;;;  (quote sleep) wouldn't work either because it only
;;;;  delays evaluation of sleep by one step, for quote itself is a function. 
;;;;  Therefore since we have many LF constants with overlapping names, we use !c to
;;;;  fake a constant c, which is actually a function that returns c as a string constant.
;;;;  Use !c in LFs wherever you need a true constant (i.e. something that evaluates to itself ALL THE TIME).
;;;; 3) PCCG component of CCGlab requires checking for LF equivalence. This is almost impossible if we
;;;;  use native lambdas of Lisp, because internal reductions will be saved by Lisp in a different format 
;;;;  (closures, functions) which we cannot penetrate. If your input sentence does not lead to an LF
;;;;  with no lambdas, the leftover lambdas would be invisible, and we cannot check for equality.
;;;;  So we implement our own lambda language, and use that for combinators and in translating your input.

;;;;  We translate all combinator instructions to lambda terms in our lambda ADT language
;;;;  so that LF normalizer only works with our lambdas.

(defun f-apply (ht1 ht2 lex2) 
  "forward application"
  (and (complexp-hash (machash 'SYN ht1))
       (eql (machash 'DIR 'SYN ht1) 'FS) ; no need to check modality, all entries qualify for application.
       (multiple-value-bind (match b1 b2)
;	 (declare (ignore b2))
	 (cat-match (machash 'ARG 'SYN ht1) (machash 'SYN ht2))
	 (and match 
	      (lex-check (machash 'LEX 'SYN ht1) lex2)  ; if we have X//Y Y , Y must be lex
	      (let ((newht (make-cky-entry-hashtable)))
		(setf (machash 'SEM newht) (&a (machash 'SEM ht1) (machash 'SEM ht2)))
		(setf (machash 'INDEX newht) '|>|)
		(and (machash 'LEX 'SYN ht1) (setf (machash 'LEX newht) t)) ; result is lexical too if X//Y Y succeeds--pass on
		(setf (machash 'SYN newht) (realize-binds (machash 'RESULT 'SYN ht1) b1))
		newht)))))

(defun b-apply (ht1 ht2 lex1) 
  "backward application"
  (and (complexp-hash (machash 'SYN ht2))
       (eql (machash 'DIR 'SYN ht2) 'BS) ; no need to check modality, all entries qualify for application.
       (multiple-value-bind (match b1 b2)
;	 (declare (ignore b1))
	 (cat-match (machash 'SYN ht1) (machash 'ARG 'SYN ht2))
	 (and match 
	      (lex-check (machash 'LEX 'SYN ht2) lex1)  ; if we have Y X\\Y, Y must be lex
	      (let ((newht (make-cky-entry-hashtable)))
		(setf (machash 'SEM newht) (&a (machash 'SEM ht2) (machash 'SEM ht1)))
		(setf (machash 'INDEX newht) '|<|)
		(and (machash 'LEX 'SYN ht2) (setf (machash 'LEX newht) t)) ; result is lexical too if Y X\\Y succeeds--pass on
		(setf (machash 'SYN newht) (realize-binds (machash 'RESULT 'SYN ht2) b2))
		newht)))))

(defun f-comp (ht1 ht2) 
  "forward composition"
  (and (complexp-hash (machash 'SYN ht1))
       (complexp-hash (machash 'SYN ht2))
       (eql (machash 'DIR 'SYN ht1) 'FS)
       (eql (machash 'DIR 'SYN ht2) 'FS)
       (member (machash 'MODAL 'SYN ht1) '(ALL HARMONIC))
       (member (machash 'MODAL 'SYN ht2) '(ALL HARMONIC))
       (multiple-value-bind (match b1 b2)
	 (cat-match (machash 'ARG 'SYN ht1) (machash 'RESULT 'SYN ht2))
	 (and match (let ((newht (make-cky-entry-hashtable))
			  (newsyn (make-complex-cat-hashtable)))
		      (setf (machash 'SEM newht) (&b (machash 'SEM ht1) (machash 'SEM ht2)))
		      (setf (machash 'INDEX newht) '|>B|) ; ht2 dir and modality projects
		      (setf (machash 'SYN newht) newsyn)
		      (setf (machash 'DIR 'SYN newht) (machash 'DIR 'SYN ht2))
		      (setf (machash 'MODAL 'SYN newht) (machash 'MODAL 'SYN ht2))
		      (setf (machash 'RESULT 'SYN newht)(realize-binds (machash 'RESULT 'SYN ht1) b1))
		      (setf (machash 'ARG 'SYN newht)(realize-binds (machash 'ARG 'SYN ht2) b2))
		      newht)))))

(defun b-comp (ht1 ht2) 
  "backward composition"
  (and (complexp-hash (machash 'SYN ht1))
       (complexp-hash (machash 'SYN ht2))
       (eql (machash 'DIR 'SYN ht1) 'BS)
       (eql (machash 'DIR 'SYN ht2) 'BS)
       (member (machash 'MODAL 'SYN ht1) '(ALL HARMONIC))
       (member (machash 'MODAL 'SYN ht2) '(ALL HARMONIC))
       (multiple-value-bind (match b1 b2)
	 (cat-match (machash 'RESULT 'SYN ht1) (machash 'ARG 'SYN ht2))
	 (and match (let ((newht (make-cky-entry-hashtable))
			  (newsyn (make-complex-cat-hashtable)))
		      (setf (machash 'SEM newht) (&b (machash 'SEM ht2) (machash 'SEM ht1)))
		      (setf (machash 'INDEX newht) '|<B|) ; ht1 dir and modality projects
		      (setf (machash 'SYN newht) newsyn)
		      (setf (machash 'DIR 'SYN newht) (machash 'DIR 'SYN ht1))
		      (setf (machash 'MODAL 'SYN newht) (machash 'MODAL 'SYN ht1))
		      (setf (machash 'RESULT 'SYN newht)(realize-binds (machash 'RESULT 'SYN ht2) b2))
		      (setf (machash 'ARG 'SYN newht)(realize-binds (machash 'ARG 'SYN ht1) b1))
		      newht)))))

(defun fx-comp (ht1 ht2) 
  "forward crossing composition"
  (and (complexp-hash (machash 'SYN ht1))
       (complexp-hash (machash 'SYN ht2))
       (eql (machash 'DIR 'SYN ht1) 'FS)
       (eql (machash 'DIR 'SYN ht2) 'BS)
       (member (machash 'MODAL 'SYN ht1) '(ALL CROSS))
       (member (machash 'MODAL 'SYN ht2) '(ALL CROSS))
       (multiple-value-bind (match b1 b2)
	 (cat-match (machash 'ARG 'SYN ht1) (machash 'RESULT 'SYN ht2))
	 (and match (let ((newht (make-cky-entry-hashtable))
			  (newsyn (make-complex-cat-hashtable)))
		      (setf (machash 'SEM newht) (&b (machash 'SEM ht1) (machash 'SEM ht2)))
		      (setf (machash 'INDEX newht) '|>Bx|) ; ht2 dir and modality projects
		      (setf (machash 'SYN newht) newsyn)
		      (setf (machash 'DIR 'SYN newht) (machash 'DIR 'SYN ht2))
		      (setf (machash 'MODAL 'SYN newht) (machash 'MODAL 'SYN ht2))
		      (setf (machash 'RESULT 'SYN newht)(realize-binds (machash 'RESULT 'SYN ht1) b1))
		      (setf (machash 'ARG 'SYN newht)(realize-binds (machash 'ARG 'SYN ht2) b2))
		      newht)))))

(defun bx-comp (ht1 ht2) 
  "backward crossing composition"
  (and (complexp-hash (machash 'SYN ht1))
       (complexp-hash (machash 'SYN ht2))
       (eql (machash 'DIR 'SYN ht1) 'FS)
       (eql (machash 'DIR 'SYN ht2) 'BS)
       (member (machash 'MODAL 'SYN ht1) '(ALL CROSS))
       (member (machash 'MODAL 'SYN ht2) '(ALL CROSS))
       (multiple-value-bind (match b1 b2)
	 (cat-match (machash 'RESULT 'SYN ht1) (machash 'ARG 'SYN ht2))
	 (and match (let ((newht (make-cky-entry-hashtable))
			  (newsyn (make-complex-cat-hashtable)))
		      (setf (machash 'SEM newht) (&b (machash 'SEM ht2) (machash 'SEM ht1)))
		      (setf (machash 'INDEX newht) '|<Bx|) ; ht1 dir and modality projects
		      (setf (machash 'SYN newht) newsyn)
		      (setf (machash 'DIR 'SYN newht) (machash 'DIR 'SYN ht1))
		      (setf (machash 'MODAL 'SYN newht) (machash 'MODAL 'SYN ht1))
		      (setf (machash 'RESULT 'SYN newht)(realize-binds (machash 'RESULT 'SYN ht2) b2))
		      (setf (machash 'ARG 'SYN newht)(realize-binds (machash 'ARG 'SYN ht1) b1))
		      newht)))))

(defun f-sub (ht1 ht2) 
  "forward substitution"
  (and (complexp-hash (machash 'SYN ht1))
       (complexp-hash (machash 'SYN ht2))
       (machash 'RESULT 'SYN ht1) 
       (machash 'DIR 'RESULT 'SYN ht1) ; result must be functor too
       (eql (machash 'DIR 'SYN ht1) 'FS)
       (eql (machash 'DIR 'SYN ht2) 'FS)
       (eql (machash 'DIR 'RESULT 'SYN ht1) 'FS)
       (member (machash 'MODAL 'SYN ht1) '(ALL HARMONIC))
       (member (machash 'MODAL 'SYN ht2) '(ALL HARMONIC))
       (member (machash 'MODAL 'RESULT 'SYN ht1) '(ALL HARMONIC))
       (multiple-value-bind (match b1 b2)
	 (cat-match (machash 'ARG 'SYN ht1) (machash 'ARG 'SYN ht2))
	 (and match (multiple-value-bind (match2 b12 b22)
		      (cat-match (machash 'ARG 'RESULT 'SYN ht1)
				 (machash 'RESULT 'SYN ht2))
		      (and match2 
			   (let ((newht (make-cky-entry-hashtable))
				 (newsyn (make-complex-cat-hashtable)))
			     (setf (machash 'SEM newht) (&s (machash 'SEM ht1) (machash 'SEM ht2)))
			     (setf (machash 'INDEX newht) '|>S|) ; ht2 dir and modality projects below
			     (setf (machash 'SYN newht) newsyn)
			     (setf (machash 'DIR 'SYN newht) (machash 'DIR 'SYN ht2))
			     (setf (machash 'MODAL 'SYN newht) (machash 'MODAL 'SYN ht2))
			     (setf (machash 'RESULT 'SYN newht)(realize-binds (machash 'RESULT 'RESULT 'SYN ht1) 
											(append b1 b12)))
			     (setf (machash 'ARG 'SYN newht)(realize-binds (machash 'ARG 'SYN ht2) 
										     (append b2 b22)))
			     newht)))))))

(defun b-sub (ht1 ht2) 
  "backward substitution"
  (and (complexp-hash (machash 'SYN ht2))
       (complexp-hash (machash 'SYN ht1))
       (machash 'RESULT 'SYN ht2) 
       (machash 'DIR 'RESULT 'SYN ht2) ; result must be functor too
       (eql (machash 'DIR 'SYN ht2) 'BS)
       (eql (machash 'DIR 'SYN ht1) 'BS)
       (eql (machash 'DIR 'RESULT 'SYN ht2) 'BS)
       (member (machash 'MODAL 'SYN ht2) '(ALL HARMONIC))
       (member (machash 'MODAL 'SYN ht1) '(ALL HARMONIC))
       (member (machash 'MODAL 'RESULT 'SYN ht2) '(ALL HARMONIC))
       (multiple-value-bind (match b2 b1)
	 (cat-match (machash 'ARG 'SYN ht2) (machash 'ARG 'SYN ht1))
	 (and match (multiple-value-bind (match2 b21 b12)
		      (cat-match (machash 'ARG 'RESULT 'SYN ht2)
				 (machash 'RESULT 'SYN ht1))
		      (and match2 
			   (let ((newht (make-cky-entry-hashtable))
				 (newsyn (make-complex-cat-hashtable)))
			     (setf (machash 'SEM newht) (&s (machash 'SEM ht2) (machash 'SEM ht1)))
			     (setf (machash 'INDEX newht) '|<S|) ; ht1 dir and modality projects below
			     (setf (machash 'SYN newht) newsyn)
			     (setf (machash 'DIR 'SYN newht) (machash 'DIR 'SYN ht1))
			     (setf (machash 'MODAL 'SYN newht) (machash 'MODAL 'SYN ht1))
			     (setf (machash 'RESULT 'SYN newht)(realize-binds (machash 'RESULT 'RESULT 'SYN ht2) 
											(append b2 b21)))
			     (setf (machash 'ARG 'SYN newht)(realize-binds (machash 'ARG 'SYN ht1) 
										     (append b1 b12)))
			     newht)))))))

(defun fx-sub (ht1 ht2) 
  "forward crossed substitution"
  (and (complexp-hash (machash 'SYN ht1))
       (complexp-hash (machash 'SYN ht2))
       (machash 'RESULT 'SYN ht1) 
       (machash 'DIR 'RESULT 'SYN ht1) ; result must be functor too
       (eql (machash 'DIR 'SYN ht1) 'BS)
       (eql (machash 'DIR 'SYN ht2) 'BS)
       (eql (machash 'DIR 'RESULT 'SYN ht1) 'FS)
       (member (machash 'MODAL 'SYN ht1) '(ALL CROSS))
       (member (machash 'MODAL 'SYN ht2) '(ALL CROSS))
       (member (machash 'MODAL 'RESULT 'SYN ht1) '(ALL CROSS))
       (multiple-value-bind (match b1 b2)
	 (cat-match (machash 'ARG 'SYN ht1) (machash 'ARG 'SYN ht2))
	 (and match (multiple-value-bind (match2 b12 b22)
		      (cat-match (machash 'ARG 'RESULT 'SYN ht1)
				 (machash 'RESULT 'SYN ht2))
		      (and match2 
			   (let ((newht (make-cky-entry-hashtable))
				 (newsyn (make-complex-cat-hashtable)))
			     (setf (machash 'SEM newht) (&s (machash 'SEM ht1) (machash 'SEM ht2)))
			     (setf (machash 'INDEX newht) '|>Sx|) ; ht2 dir and modality projects below
			     (setf (machash 'SYN newht) newsyn)
			     (setf (machash 'DIR 'SYN newht) (machash 'DIR 'SYN ht2))
			     (setf (machash 'MODAL 'SYN newht) (machash 'MODAL 'SYN ht2))
			     (setf (machash 'RESULT 'SYN newht)(realize-binds (machash 'RESULT 'RESULT 'SYN ht1) 
											(append b1 b12)))
			     (setf (machash 'ARG 'SYN newht)(realize-binds (machash 'ARG 'SYN ht2) 
										     (append b2 b22)))
			     newht)))))))

(defun bx-sub (ht1 ht2) 
  "backward crossed substitution"
  (and (complexp-hash (machash 'SYN ht2))
       (complexp-hash (machash 'SYN ht1))
       (machash 'RESULT 'SYN ht2) 
       (machash 'DIR 'RESULT 'SYN ht2) ; result must be functor too
       (eql (machash 'DIR 'SYN ht2) 'FS)
       (eql (machash 'DIR 'SYN ht1) 'FS)
       (eql (machash 'DIR 'RESULT 'SYN ht2) 'BS)
       (member (machash 'MODAL 'SYN ht2) '(ALL CROSS))
       (member (machash 'MODAL 'SYN ht1) '(ALL CROSS))
       (member (machash 'MODAL 'RESULT 'SYN ht2) '(ALL CROSS))
       (multiple-value-bind (match b2 b1)
	 (cat-match (machash 'ARG 'SYN ht2) (machash 'ARG 'SYN ht1))
	 (and match (multiple-value-bind (match2 b21 b12)
		      (cat-match (machash 'ARG 'RESULT 'SYN ht2)
				 (machash 'RESULT 'SYN ht1))
		      (and match2 
			   (let ((newht (make-cky-entry-hashtable))
				 (newsyn (make-complex-cat-hashtable)))
			     (setf (machash 'SEM newht) (&s (machash 'SEM ht2) (machash 'SEM ht1)))
			     (setf (machash 'INDEX newht) '|<Sx|) ; ht1 dir and modality projects below
			     (setf (machash 'SYN newht) newsyn)
			     (setf (machash 'DIR 'SYN newht) (machash 'DIR 'SYN ht1))
			     (setf (machash 'MODAL 'SYN newht) (machash 'MODAL 'SYN ht1))
			     (setf (machash 'RESULT 'SYN newht)(realize-binds (machash 'RESULT 'RESULT 'SYN ht2) 
											(append b2 b21)))
			     (setf (machash 'ARG 'SYN newht)(realize-binds (machash 'ARG 'SYN ht1) 
										     (append b1 b12)))
			     newht)))))))

;; this combinator is experimental. In most basic form it is X/Y/Z Y/W -> X/W/Z : \z\w.fz(gw) . It has C in it!
;; by default all its variants are turned off
(defun f-subbar (ht1 ht2) 
  "forward substitution bar, aka the lost combinator"
  (and (complexp-hash (machash 'SYN ht1))
       (complexp-hash (machash 'SYN ht2))
       (machash 'RESULT 'SYN ht1) 
       (machash 'DIR 'RESULT 'SYN ht1) ; result must be functor too
       (eql (machash 'DIR 'SYN ht2) 'FS)
       (eql (machash 'DIR 'RESULT 'SYN ht1) 'FS)
       (member (machash 'MODAL 'SYN ht2) '(ALL HARMONIC))
       (member (machash 'MODAL 'RESULT 'SYN ht1) '(ALL HARMONIC))
       (multiple-value-bind (match2 b12 b22)
		      (cat-match (machash 'ARG 'RESULT 'SYN ht1)
				 (machash 'RESULT 'SYN ht2))
		      (and match2 
			   (let ((newht (make-cky-entry-hashtable))
				 (newsyn (make-complex-cat-hashtable))
				 (newsynw (make-complex-cat-hashtable)))
			     (setf (machash 'SEM newht) (&sbar (machash 'SEM ht1) (machash 'SEM ht2)))
			     (setf (machash 'INDEX newht) '|>L|) 
			     (setf (machash 'SYN newht) newsyn)
			     (setf (machash 'DIR 'SYN newht) (machash 'DIR 'SYN ht1))
			     (setf (machash 'MODAL 'SYN newht) (machash 'MODAL 'SYN ht1))
			     (setf (machash 'DIR newsynw) (machash 'DIR 'SYN ht2))
			     (setf (machash 'RESULT newsynw) (realize-binds 
							       (machash 'RESULT 'RESULT 'SYN ht1) 
											(append nil b12)))
			     (setf (machash 'ARG newsynw) (realize-binds 
							    (machash 'ARG 'SYN ht2) 
							    (append nil b22)))
			     (setf (machash 'RESULT 'SYN newht) newsynw)
			     (setf (machash 'ARG 'SYN newht)(realize-binds (machash 'ARG 'SYN ht1) 
										     (append nil b12)))
			     newht)))))

(defun fx-subbar (ht1 ht2) 
  "forward crossing substitution bar"
  (and (complexp-hash (machash 'SYN ht1))
       (complexp-hash (machash 'SYN ht2))
       (machash 'RESULT 'SYN ht1) 
       (machash 'DIR 'RESULT 'SYN ht1) ; result must be functor too
       (eql (machash 'DIR 'SYN ht2) 'BS)
       (eql (machash 'DIR 'RESULT 'SYN ht1) 'FS)
       (member (machash 'MODAL 'SYN ht2) '(ALL CROSS))
       (member (machash 'MODAL 'RESULT 'SYN ht1) '(ALL CROSS))
       (multiple-value-bind (match2 b12 b22)
		      (cat-match (machash 'ARG 'RESULT 'SYN ht1)
				 (machash 'RESULT 'SYN ht2))
		      (and match2 
			   (let ((newht (make-cky-entry-hashtable))
				 (newsyn (make-complex-cat-hashtable))
				 (newsynw (make-complex-cat-hashtable)))
			     (setf (machash 'SEM newht) (&sbar (machash 'SEM ht1) (machash 'SEM ht2)))
			     (setf (machash 'INDEX newht) '|>Lx|)
			     (setf (machash 'SYN newht) newsyn)
			     (setf (machash 'DIR 'SYN newht) (machash 'DIR 'SYN ht1))
			     (setf (machash 'MODAL 'SYN newht) (machash 'MODAL 'SYN ht1))
			     (setf (machash 'DIR newsynw) (machash 'DIR 'SYN ht2))
			     (setf (machash 'RESULT newsynw) (realize-binds 
							       (machash 'RESULT 'RESULT 'SYN ht1) 
											(append nil b12)))
			     (setf (machash 'ARG newsynw) (realize-binds 
							    (machash 'ARG 'SYN ht2) 
							    (append nil b22)))
			     (setf (machash 'RESULT 'SYN newht) newsynw)
			     (setf (machash 'ARG 'SYN newht)(realize-binds (machash 'ARG 'SYN ht1) 
										     (append nil b12)))
			     newht)))))

(defun b-subbar (ht1 ht2) 
  "backward substitution bar"
  (and (complexp-hash (machash 'SYN ht1))
       (complexp-hash (machash 'SYN ht2))
       (machash 'RESULT 'SYN ht2) 
       (machash 'DIR 'RESULT 'SYN ht2) ; result must be functor too
       (eql (machash 'DIR 'SYN ht1) 'BS)
       (eql (machash 'DIR 'RESULT 'SYN ht2) 'BS)
       (member (machash 'MODAL 'SYN ht1) '(ALL HARMONIC))
       (member (machash 'MODAL 'RESULT 'SYN ht2) '(ALL HARMONIC))
       (multiple-value-bind (match2 b22 b12)
		      (cat-match (machash 'ARG 'RESULT 'SYN ht2)
				 (machash 'RESULT 'SYN ht1))
		      (and match2 
			   (let ((newht (make-cky-entry-hashtable))
				 (newsyn (make-complex-cat-hashtable))
				 (newsynw (make-complex-cat-hashtable)))
			     (setf (machash 'SEM newht) (&sbar (machash 'SEM ht2) (machash 'SEM ht1)))
			     (setf (machash 'INDEX newht) '|<L|) 
			     (setf (machash 'SYN newht) newsyn)
			     (setf (machash 'DIR 'SYN newht) (machash 'DIR 'SYN ht2))
			     (setf (machash 'MODAL 'SYN newht) (machash 'MODAL 'SYN ht2))
			     (setf (machash 'DIR newsynw) (machash 'DIR 'SYN ht1))
			     (setf (machash 'RESULT newsynw) (realize-binds 
							       (machash 'RESULT 'RESULT 'SYN ht2) 
											(append nil b22)))
			     (setf (machash 'ARG newsynw) (realize-binds 
							    (machash 'ARG 'SYN ht1) 
							    (append nil b12)))
			     (setf (machash 'RESULT 'SYN newht) newsynw)
			     (setf (machash 'ARG 'SYN newht)(realize-binds (machash 'ARG 'SYN ht2) 
										     (append nil b22)))
			     newht)))))

(defun bx-subbar (ht1 ht2) 
  "backward crossed substitution bar"
  (and (complexp-hash (machash 'SYN ht1))
       (complexp-hash (machash 'SYN ht2))
       (machash 'RESULT 'SYN ht2) 
       (machash 'DIR 'RESULT  'SYN ht2) ; result must be functor too
       (eql (machash 'DIR 'SYN ht1) 'FS)
       (eql (machash 'DIR 'RESULT 'SYN ht2) 'BS)
       (member (machash 'MODAL 'SYN ht1) '(ALL CROSS))
       (member (machash 'MODAL 'RESULT 'SYN ht2) '(ALL CROSS))
       (multiple-value-bind (match2 b22 b12)
		      (cat-match (machash 'ARG 'RESULT 'SYN ht2)
				 (machash 'RESULT 'SYN ht1))
		      (and match2 
			   (let ((newht (make-cky-entry-hashtable))
				 (newsyn (make-complex-cat-hashtable))
				 (newsynw (make-complex-cat-hashtable)))
			     (setf (machash 'SEM newht) (&sbar (machash 'SEM ht2) (machash 'SEM ht1)))
			     (setf (machash 'INDEX newht) '|<Lx|) 
			     (setf (machash 'SYN newht) newsyn)
			     (setf (machash 'DIR 'SYN newht) (machash 'DIR 'SYN ht2))
			     (setf (machash 'MODAL 'SYN newht) (machash 'MODAL 'SYN ht2))
			     (setf (machash 'DIR newsynw) (machash 'DIR 'SYN ht1))
			     (setf (machash 'RESULT newsynw) (realize-binds 
							       (machash 'RESULT 'RESULT 'SYN ht2) 
											(append nil b22)))
			     (setf (machash 'ARG newsynw) (realize-binds 
							    (machash 'ARG 'SYN ht1) 
							    (append nil b12)))
			     (setf (machash 'RESULT 'SYN newht) newsynw)
			     (setf (machash 'ARG 'SYN newht)(realize-binds (machash 'ARG 'SYN ht2) 
										     (append nil b22)))
			     newht)))))

(defun f-subcomp (ht1 ht2) 
  "forward subcomposition.
   Cf. Bozsahin 2012 and Hoyt and Baldridge 2008 for subcomposition/subcombination.
   This is what is dubbed Orifice (O) in the former, and D in the latter publication.
   Not to be confused with combinator D of Rosenbloom 1950, which is just BB."
  (and (complexp-hash (machash 'SYN ht1))
       (complexp-hash (machash 'SYN ht2))
       (machash 'RESULT 'SYN ht1) 
       (machash 'DIR 'ARG 'SYN ht1) ; arg must be functor too
       (eql (machash 'DIR 'SYN ht2) 'FS)
       (eql (machash 'DIR 'SYN ht1) 'FS)
       (member (machash 'MODAL 'SYN ht2) '(ALL HARMONIC))
       (member (machash 'MODAL 'SYN ht1) '(ALL HARMONIC))
       (multiple-value-bind (match b1 b2)
	 (cat-match (machash 'RESULT 'ARG 'SYN ht1) (machash 'RESULT 'SYN ht2))
	 (and match 
              (let ((newht (make-cky-entry-hashtable))     ;
		    (newsynx (make-complex-cat-hashtable))   ; new result
		    (newsynw (make-complex-cat-hashtable)))  ; new result of new argument
		(setf (machash 'SEM newht) (&o (machash 'SEM ht1) (machash 'SEM ht2)))
		(setf (machash 'INDEX newht) '|>O|) ; things project from ht1 and ht2
		(setf (machash 'SYN newht) newsynx)
		(setf (machash 'DIR 'SYN newht) (machash 'DIR 'SYN ht2))
		(setf (machash 'MODAL 'SYN newht) (machash 'MODAL 'SYN ht2))
                (setf (machash 'RESULT 'SYN newht)
		      (realize-binds (machash 'RESULT 'SYN ht1) b1))
                (setf (machash 'ARG 'SYN newht) newsynw)
                (setf (machash 'DIR 'ARG 'SYN newht) 
			       (machash 'DIR 'ARG 'SYN ht1))
                (setf (machash 'MODAL 'ARG 'SYN newht)
			       (machash 'MODAL 'ARG 'SYN ht1))
                (setf (machash 'RESULT 'ARG 'SYN newht)
		      (realize-binds (machash 'ARG 'SYN ht2) b2))
                (setf (machash 'ARG 'ARG 'SYN newht)
		      (realize-binds (machash 'ARG 'ARG 'SYN ht1) b1))
			     newht)))))

(defun b-subcomp (ht1 ht2) 
  "backward subcomposition."
  (and (complexp-hash (machash 'SYN ht1))
       (complexp-hash (machash 'SYN ht2))
       (machash 'RESULT 'SYN ht2) 
       (machash 'DIR 'ARG 'SYN ht2) ; arg must be functor too
       (eql (machash 'DIR 'SYN ht1) 'BS)
       (eql (machash 'DIR 'SYN ht2) 'BS)
       (member (machash 'MODAL  'SYN ht1) '(ALL HARMONIC))
       (member (machash 'MODAL 'SYN ht2) '(ALL HARMONIC))
       (multiple-value-bind (match b1 b2)
	 (cat-match (machash 'RESULT 'SYN ht1)
		    (machash 'RESULT 'ARG 'SYN ht2)) 
	 (and match 
              (let ((newht (make-cky-entry-hashtable))     ;
		    (newsynx (make-complex-cat-hashtable))   ; new result
		    (newsynw (make-complex-cat-hashtable)))  ; new result of new argument
		(setf (machash 'SEM newht) (&o (machash 'SEM ht2) (machash 'SEM ht1)))
		(setf (machash 'INDEX newht) '|<O|) ; things project from ht1 and ht2
		(setf (machash 'SYN newht) newsynx)
		(setf (machash 'DIR 'SYN newht) (machash 'DIR 'SYN ht1))
		(setf (machash 'MODAL 'SYN newht) (machash 'MODAL 'SYN ht1))
                (setf (machash 'RESULT 'SYN newht)
		      (realize-binds (machash 'RESULT 'SYN ht2) b2))
                (setf (machash 'ARG 'SYN newht) newsynw)
                (setf (machash 'DIR 'ARG 'SYN newht) 
			       (machash 'DIR 'ARG 'SYN ht2))
                (setf (machash 'MODAL 'ARG 'SYN newht)
			       (machash 'MODAL 'ARG 'SYN ht2))
                (setf (machash 'RESULT 'ARG 'SYN newht)
		      (realize-binds (machash 'ARG 'SYN ht1) b1))
                (setf (machash 'ARG 'ARG 'SYN newht)
		      (realize-binds (machash 'ARG 'ARG 'SYN ht2) b2))
			     newht)))))

(defun fx-subcomp (ht1 ht2) 
  "forward crossed subcomposition."
  (and (complexp-hash (machash 'SYN ht1))
       (complexp-hash (machash 'SYN ht2))
       (machash 'RESULT 'SYN ht1) 
       (machash 'DIR 'ARG 'SYN ht1) ; arg must be functor too
       (eql (machash 'DIR 'SYN ht2) 'BS)
       (eql (machash 'DIR 'SYN ht1) 'FS)
       (member (machash 'MODAL 'SYN ht2) '(ALL CROSS))
       (member (machash 'MODAL 'SYN ht1) '(ALL CROSS))
       (multiple-value-bind (match b1 b2)
	 (cat-match (machash 'RESULT 'ARG 'SYN ht1) (machash 'RESULT 'SYN ht2))
	 (and match 
              (let ((newht (make-cky-entry-hashtable))     ;
		    (newsynx (make-complex-cat-hashtable))   ; new result
		    (newsynw (make-complex-cat-hashtable)))  ; new result of new argument
		(setf (machash 'SEM newht) (&o (machash 'SEM ht1) (machash 'SEM ht2)))
		(setf (machash 'INDEX newht) '|>Ox|) ; things project from ht1 and ht2
		(setf (machash 'SYN newht) newsynx)
		(setf (machash 'DIR 'SYN newht) (machash 'DIR 'SYN ht2))
		(setf (machash 'MODAL 'SYN newht) (machash 'MODAL 'SYN ht2))
                (setf (machash 'RESULT 'SYN newht)
		      (realize-binds (machash 'RESULT 'SYN ht1) b1))
                (setf (machash 'ARG  'SYN newht) newsynw)
                (setf (machash 'DIR 'ARG 'SYN newht) 
			       (machash 'DIR 'ARG 'SYN ht1))
                (setf (machash 'MODAL 'ARG 'SYN newht)
			       (machash 'MODAL 'ARG 'SYN ht1))
                (setf (machash 'RESULT 'ARG 'SYN newht)
		      (realize-binds (machash 'ARG 'SYN ht2) b2))
                (setf (machash 'ARG 'ARG 'SYN newht)
		      (realize-binds (machash 'ARG 'ARG 'SYN ht1) b1))
			     newht)))))

(defun bx-subcomp (ht1 ht2) 
  "backward crossed subcomposition."
  (and (complexp-hash (machash 'SYN ht1))
       (complexp-hash (machash 'SYN ht2))
       (machash 'RESULT 'SYN ht2) 
       (machash 'DIR 'ARG 'SYN ht2) ; arg must be functor too
       (eql (machash 'DIR 'SYN ht1) 'FS)
       (eql (machash 'DIR 'SYN ht2) 'BS)
       (member (machash 'MODAL 'SYN ht1) '(ALL CROSS))
       (member (machash 'MODAL 'SYN ht2) '(ALL CROSS))
       (multiple-value-bind (match b1 b2)
	 (cat-match (machash 'RESULT 'SYN ht1)
		    (machash 'RESULT 'ARG 'SYN ht2)) 
	 (and match 
              (let ((newht (make-cky-entry-hashtable))     ;
		    (newsynx (make-complex-cat-hashtable))   ; new result
		    (newsynw (make-complex-cat-hashtable)))  ; new result of new argument
		(setf (machash 'SEM newht) (&o (machash 'SEM ht2) (machash 'SEM ht1)))
		(setf (machash 'INDEX newht) '|<Ox|) ; things project from ht1 and ht2
		(setf (machash 'SYN newht) newsynx)
		(setf (machash 'DIR 'SYN newht) (machash 'DIR 'SYN ht1))
		(setf (machash 'MODAL 'SYN newht) (machash 'MODAL 'SYN ht1))
                (setf (machash 'RESULT 'SYN newht)
		      (realize-binds (machash 'RESULT 'SYN ht2) b2))
                (setf (machash 'ARG 'SYN newht) newsynw)
                (setf (machash 'DIR 'ARG 'SYN newht) 
			       (machash 'DIR 'ARG 'SYN ht2))
                (setf (machash 'MODAL 'ARG 'SYN newht)
			       (machash 'MODAL 'ARG 'SYN ht2))
                (setf (machash 'RESULT 'ARG 'SYN newht)
		      (realize-binds (machash 'ARG 'SYN ht1) b1))
                (setf (machash 'ARG 'ARG 'SYN newht)
		      (realize-binds (machash 'ARG 'ARG 'SYN ht2) b2))
			     newht)))))

(defun f2-comp (ht1 ht2) 
  ">B^2"
  (and (complexp-hash (machash 'SYN ht1))
       (complexp-hash (machash 'SYN ht2))
       (eql (machash 'DIR 'SYN ht1) 'FS)
       (machash 'DIR 'RESULT 'SYN ht2) ; ht2 must have complex result
       (eql (machash 'DIR 'RESULT 'SYN ht2) 'FS)
       (member (machash 'MODAL 'SYN ht1) '(ALL HARMONIC))
       (not (eql (machash 'MODAL 'SYN ht2) 'STAR)) ; main functor must allow composition
       (member (machash 'MODAL 'RESULT 'SYN ht2) '(ALL HARMONIC))
       (multiple-value-bind (match b1 b2)
	 (cat-match (machash 'ARG 'SYN ht1) (machash 'RESULT 'RESULT 'SYN ht2))
	 (and match (let ((newht (make-cky-entry-hashtable))
			  (newsynx (make-complex-cat-hashtable))
			  (newsyn (make-complex-cat-hashtable)))
		      (setf (machash 'SEM newht) (&b2 (machash 'SEM ht1) (machash 'SEM ht2)))
		      (setf (machash 'INDEX newht) '|>B2|) ; ht2 dir and modality projects
		      (setf (machash 'SYN newht) newsyn)
		      (setf (machash 'DIR 'SYN newht) (machash 'DIR 'SYN ht2))
		      (setf (machash 'MODAL 'SYN newht) (machash 'MODAL 'SYN ht2))
		      (setf (machash 'ARG 'SYN newht)
			    (realize-binds (machash 'ARG 'SYN ht2) b2))
		      (setf (machash 'RESULT 'SYN newht) newsynx)
		      (setf (machash 'DIR 'RESULT 'SYN newht) 
			    (machash 'DIR 'RESULT 'SYN ht2))
		      (setf (machash 'MODAL 'RESULT 'SYN newht) 
			    (machash 'MODAL 'RESULT 'SYN ht2))
		      (setf (machash 'RESULT 'RESULT 'SYN newht)
			    (realize-binds (machash 'RESULT 'SYN ht1) b1))
		      (setf (machash 'ARG 'RESULT 'SYN newht)
			    (realize-binds (machash 'ARG 'RESULT 'SYN ht2) b2))
		      newht)))))

(defun b2-comp (ht1 ht2) 
  "<B^2"
  (and (complexp-hash (machash 'SYN ht1))
       (complexp-hash (machash 'SYN ht2))
       (eql (machash 'DIR 'SYN ht2) 'BS)
       (machash 'DIR 'RESULT 'SYN ht1) ; ht1 must have complex result
       (eql (machash 'DIR 'RESULT 'SYN ht1) 'BS)
       (member (machash 'MODAL 'SYN ht2) '(ALL HARMONIC))
       (not (eql (machash 'MODAL 'SYN ht1) 'STAR)) ; main functor must allow composition
       (member (machash 'MODAL 'RESULT 'SYN ht1) '(ALL HARMONIC))
       (multiple-value-bind (match b1 b2)
	 (cat-match (machash 'RESULT 'RESULT 'SYN ht1)
	            (machash 'ARG 'SYN ht2))
	 (and match (let ((newht (make-cky-entry-hashtable))
			  (newsynx (make-complex-cat-hashtable))
			  (newsyn (make-complex-cat-hashtable)))
		      (setf (machash 'SEM newht) (&b2 (machash 'SEM ht2) (machash 'SEM ht1)))
		      (setf (machash 'INDEX newht) '|<B2|) ; ht1 dir and modality projects
		      (setf (machash 'SYN newht) newsyn)
		      (setf (machash 'DIR 'SYN newht) (machash 'DIR 'SYN ht1))
		      (setf (machash 'MODAL 'SYN newht) (machash 'MODAL 'SYN ht1))
		      (setf (machash 'ARG 'SYN newht)
			    (realize-binds (machash 'ARG 'SYN ht1) b1))
		      (setf (machash 'RESULT 'SYN newht) newsynx)
		      (setf (machash 'DIR 'RESULT 'SYN newht) 
			    (machash 'DIR 'RESULT 'SYN ht1))
		      (setf (machash 'MODAL 'RESULT 'SYN newht) 
			    (machash 'MODAL 'RESULT 'SYN ht1))
		      (setf (machash 'RESULT 'RESULT 'SYN newht)
			    (realize-binds (machash 'RESULT 'SYN ht2) b2))
		      (setf (machash 'ARG 'RESULT 'SYN newht)
			    (realize-binds (machash 'ARG 'RESULT 'SYN ht1) b1))
		      newht)))))

(defun fx2-comp (ht1 ht2) 
  ">Bx^2"
  (and (complexp-hash (machash 'SYN ht1))
       (complexp-hash (machash 'SYN ht2))
       (eql (machash 'DIR 'SYN ht1) 'FS)
       (machash 'DIR 'RESULT 'SYN ht2) ; ht2 must have complex result
       (eql (machash 'DIR 'RESULT 'SYN ht2) 'BS)
       (member (machash 'MODAL 'SYN ht1) '(ALL CROSS))
       (not (eql (machash 'MODAL 'SYN ht2) 'STAR)) ; main functor must allow composition
       (member (machash 'MODAL 'RESULT 'SYN ht2) '(ALL CROSS))
       (multiple-value-bind (match b1 b2)
	 (cat-match (machash 'ARG 'SYN ht1) (machash 'RESULT 'RESULT 'SYN ht2))
	 (and match (let ((newht (make-cky-entry-hashtable))
			  (newsynx (make-complex-cat-hashtable))
			  (newsyn (make-complex-cat-hashtable)))
		      (setf (machash 'SEM newht) (&b2 (machash 'SEM ht1) (machash 'SEM ht2)))
		      (setf (machash 'INDEX newht) '|>Bx2|) ; ht2 dir and modality projects
		      (setf (machash 'SYN newht) newsyn)
		      (setf (machash 'DIR 'SYN newht) (machash 'DIR 'SYN ht2))
		      (setf (machash 'MODAL 'SYN newht) (machash 'MODAL 'SYN ht2))
		      (setf (machash 'ARG 'SYN newht)
			    (realize-binds (machash 'ARG 'SYN ht2) b2))
		      (setf (machash 'RESULT 'SYN newht) newsynx)
		      (setf (machash 'DIR 'RESULT 'SYN newht) 
			    (machash 'DIR 'RESULT 'SYN ht2))
		      (setf (machash 'MODAL 'RESULT 'SYN newht) 
			    (machash 'MODAL 'RESULT 'SYN ht2))
		      (setf (machash 'RESULT 'RESULT 'SYN newht)
			    (realize-binds (machash 'RESULT 'SYN ht1) b1))
		      (setf (machash 'ARG 'RESULT 'SYN newht)
			    (realize-binds (machash 'ARG 'RESULT 'SYN ht2) b2))
		      newht)))))

(defun bx2-comp (ht1 ht2) 
  "<Bx^2"
  (and (complexp-hash (machash 'SYN ht1))
       (complexp-hash (machash 'SYN ht2))
       (eql (machash 'DIR 'SYN ht2) 'BS)
       (machash 'DIR 'RESULT 'SYN ht1) ; ht1 must have complex result
       (eql (machash 'DIR 'RESULT 'SYN ht1) 'FS)
       (member (machash 'MODAL 'SYN ht2) '(ALL CROSS))
       (not (eql (machash 'MODAL 'SYN ht1) 'STAR)) ; main functor must allow composition
       (member (machash 'MODAL 'RESULT 'SYN ht1) '(ALL CROSS))
       (multiple-value-bind (match b1 b2)
	 (cat-match (machash 'RESULT 'RESULT 'SYN ht1)
	            (machash 'ARG  'SYN ht2))
	 (and match (let ((newht (make-cky-entry-hashtable))
			  (newsynx (make-complex-cat-hashtable))
			  (newsyn (make-complex-cat-hashtable)))
		      (setf (machash 'SEM newht) (&b2 (machash 'SEM ht2) (machash 'SEM ht1)))
		      (setf (machash 'INDEX newht) '|<Bx2|) ; ht1 dir and modality projects
		      (setf (machash 'SYN newht) newsyn)
		      (setf (machash 'DIR 'SYN newht) (machash 'DIR 'SYN ht1))
		      (setf (machash 'MODAL 'SYN newht) (machash 'MODAL 'SYN ht1))
		      (setf (machash 'ARG 'SYN newht)
			    (realize-binds (machash 'ARG 'SYN ht1) b1))
		      (setf (machash 'RESULT 'SYN newht) newsynx)
		      (setf (machash 'DIR 'RESULT 'SYN newht) 
			    (machash 'DIR 'RESULT 'SYN ht1))
		      (setf (machash 'MODAL  'RESULT  'SYN newht) 
			    (machash 'MODAL 'RESULT 'SYN ht1))
		      (setf (machash 'RESULT 'RESULT 'SYN newht)
			    (realize-binds (machash 'RESULT 'SYN ht2) b2))
		      (setf (machash 'ARG 'RESULT 'SYN newht)
			    (realize-binds (machash 'ARG 'RESULT 'SYN ht1) b1))
		      newht)))))

(defun f2-sub (ht1 ht2) 
  ">S'', which is not S2, which is useless. See Bozsahin CL book ch.5"
  (and (complexp-hash (machash 'SYN ht1))
       (complexp-hash (machash 'SYN ht2))
       (machash 'RESULT 'SYN ht1) 
       (machash 'DIR 'RESULT 'SYN ht1) ; result must be functor too
       (machash 'DIR 'RESULT 'SYN ht2) ; result must be functor too
       (eql (machash 'DIR 'RESULT 'SYN ht1) 'FS)
       (eql (machash 'DIR 'RESULT 'SYN ht2) 'FS)
       (not (eql (machash 'MODAL 'SYN ht2) 'STAR)) ; main functor must allow composition
       (member (machash 'MODAL 'RESULT 'SYN ht1) '(ALL HARMONIC))
       (member (machash 'MODAL 'RESULT 'SYN ht2) '(ALL HARMONIC))
       (multiple-value-bind (match b1 b2)
	 (cat-match (machash 'ARG 'SYN ht1) (machash 'ARG 'SYN ht2))
	 (and match (multiple-value-bind (match2 b12 b22)
		      (cat-match (machash 'ARG 'RESULT 'SYN ht1)
				 (machash 'RESULT 'RESULT 'SYN ht2))
		      (and match2 
			   (let ((newht (make-cky-entry-hashtable))
				 (newsyn2 (make-complex-cat-hashtable))
				 (newsyn (make-complex-cat-hashtable)))
			     (setf (machash 'SEM newht) (&s2 (machash 'SEM ht1) (machash 'SEM ht2)))
			     (setf (machash 'INDEX newht) '|>S2|) ; ht2 dir and modality projects below
			     (setf (machash 'SYN newht) newsyn)
			     (setf (machash 'DIR 'SYN newht) (machash 'DIR 'SYN ht2))
			     (setf (machash 'MODAL 'SYN newht) (machash 'MODAL 'SYN ht2))
			     (setf (machash 'ARG 'SYN newht)
				   (realize-binds (machash 'ARG 'SYN ht2)
			                          (append b2 b22)))
			     (setf (machash 'RESULT 'SYN newht) newsyn2)
			     (setf (machash 'RESULT 'RESULT 'SYN newht)
				   (realize-binds (machash 'RESULT 'RESULT 'SYN ht1) 
						  (append b1 b12)))
			     (setf (machash 'ARG 'RESULT 'SYN newht)
				   (realize-binds (machash 'ARG 'RESULT 'SYN ht2) 
			                          (append b2 b22)))
			     (setf (machash 'DIR 'RESULT 'SYN newht)
				   (machash 'DIR 'RESULT 'SYN ht2))
			     (setf (machash 'MODAL 'RESULT 'SYN newht)
				   (machash 'MODAL 'RESULT 'SYN ht2))
			     newht)))))))

(defun b2-sub (ht1 ht2) 
  "<S'', which is not S2, which is useless. See Bozsahin CL book ch.5"
  (and (complexp-hash (machash 'SYN ht2))
       (complexp-hash (machash 'SYN ht1))
       (machash 'RESULT 'SYN ht2) 
       (machash 'DIR 'RESULT 'SYN ht2) ; result must be functor too
       (machash 'DIR 'RESULT 'SYN ht1) ; result must be functor too
       (eql (machash 'DIR 'RESULT 'SYN ht2) 'BS)
       (eql (machash 'DIR 'RESULT 'SYN ht1) 'BS)
       (not (eql (machash 'MODAL 'SYN ht1) 'STAR)) ; main functor must allow composition
       (member (machash 'MODAL 'RESULT 'SYN ht2) '(ALL HARMONIC))
       (member (machash 'MODAL 'RESULT 'SYN ht1) '(ALL HARMONIC))
       (multiple-value-bind (match b1 b2)
	 (cat-match (machash 'ARG 'SYN ht1) 
		    (machash 'ARG 'SYN ht2))
	 (and match (multiple-value-bind (match2 b12 b22)
		      (cat-match (machash 'RESULT 'RESULT 'SYN ht1)
				 (machash 'ARG 'RESULT 'SYN ht2))
		      (and match2 
			   (let ((newht (make-cky-entry-hashtable))
				 (newsyn2 (make-complex-cat-hashtable))
				 (newsyn (make-complex-cat-hashtable)))
			     (setf (machash 'SEM newht) (&s2 (machash 'SEM ht2) (machash 'SEM ht1)))
			     (setf (machash 'INDEX newht) '|<S2|) ; ht1 dir and modality projects below
			     (setf (machash 'SYN newht) newsyn)
			     (setf (machash 'DIR 'SYN newht) (machash 'DIR 'SYN ht1))
			     (setf (machash 'MODAL 'SYN newht) (machash 'MODAL 'SYN ht1))
			     (setf (machash 'ARG 'SYN newht)
				   (realize-binds (machash 'ARG 'SYN ht1)
			                          (append b1 b12)))
			     (setf (machash 'RESULT 'SYN newht) newsyn2)
			     (setf (machash 'RESULT 'RESULT 'SYN newht)
				   (realize-binds (machash 'RESULT 'RESULT 'SYN ht2) 
						  (append b2 b22)))
			     (setf (machash 'ARG 'RESULT 'SYN newht)
				   (realize-binds (machash 'ARG 'RESULT  'SYN ht1) 
			                          (append b1 b12)))
			     (setf (machash 'DIR 'RESULT 'SYN newht)
				   (machash 'DIR 'RESULT 'SYN ht1))
			     (setf (machash 'MODAL 'RESULT 'SYN newht)
				   (machash 'MODAL 'RESULT 'SYN ht1))
			     newht)))))))

(defun fx2-sub (ht1 ht2) 
  ">Sx'', which is not S2, which is useless. See Bozsahin CL book ch.5"
  (and (complexp-hash (machash 'SYN ht1))
       (complexp-hash (machash 'SYN ht2))
       (machash 'RESULT 'SYN ht1) 
       (machash 'DIR 'RESULT 'SYN ht1) ; result must be functor too
       (machash 'DIR 'RESULT 'SYN ht2) ; result must be functor too
       (eql (machash 'DIR 'RESULT 'SYN ht1) 'FS)
       (eql (machash 'DIR 'RESULT 'SYN ht2) 'BS)
       (not (eql (machash 'MODAL 'SYN ht2) 'STAR)) ; main functor must allow composition
       (member (machash 'MODAL 'RESULT 'SYN ht1) '(ALL CROSS))
       (member (machash 'MODAL 'RESULT 'SYN ht2) '(ALL CROSS))
       (multiple-value-bind (match b1 b2)
	 (cat-match (machash 'ARG 'SYN ht1) (machash 'ARG 'SYN ht2))
	 (and match (multiple-value-bind (match2 b12 b22)
		      (cat-match (machash 'ARG 'RESULT 'SYN ht1)
				 (machash 'RESULT 'RESULT 'SYN ht2))
		      (and match2 
			   (let ((newht (make-cky-entry-hashtable))
				 (newsyn2 (make-complex-cat-hashtable))
				 (newsyn (make-complex-cat-hashtable)))
			     (setf (machash 'SEM newht) (&s2 (machash 'SEM ht1) (machash 'SEM ht2)))
			     (setf (machash 'INDEX newht) '|>Sx2|) ; ht2 dir and modality projects below
			     (setf (machash 'SYN newht) newsyn)
			     (setf (machash 'DIR 'SYN newht) (machash 'DIR 'SYN ht2))
			     (setf (machash 'MODAL 'SYN newht) (machash 'MODAL 'SYN ht2))
			     (setf (machash 'ARG 'SYN newht)
				   (realize-binds (machash 'ARG 'SYN ht2)
			                          (append b2 b22)))
			     (setf (machash 'RESULT 'SYN newht) newsyn2)
			     (setf (machash 'RESULT 'RESULT 'SYN newht)
				   (realize-binds (machash 'RESULT 'RESULT 'SYN ht1) 
						  (append b1 b12)))
			     (setf (machash 'ARG 'RESULT 'SYN newht)
				   (realize-binds (machash 'ARG 'RESULT 'SYN ht2) 
			                          (append b2 b22)))
			     (setf (machash 'DIR 'RESULT 'SYN newht)
				   (machash 'DIR 'RESULT 'SYN ht2))
			     (setf (machash 'MODAL 'RESULT 'SYN newht)
				   (machash 'MODAL 'RESULT  'SYN ht2))
			     newht)))))))

(defun bx2-sub (ht1 ht2) 
  "<Sx'', which is not S2, which is useless. See Bozsahin CL book ch.5"
  (and (complexp-hash (machash 'SYN ht2))
       (complexp-hash (machash 'SYN ht1))
       (machash 'RESULT 'SYN ht2) 
       (machash 'DIR 'RESULT 'SYN ht2) ; result must be functor too
       (machash 'DIR 'RESULT 'SYN ht1) ; result must be functor too
       (eql (machash 'DIR 'RESULT 'SYN ht2) 'BS)
       (eql (machash 'DIR 'RESULT 'SYN ht1) 'FS)
       (not (eql (machash 'MODAL 'SYN ht1) 'STAR)) ; main functor must allow composition
       (member (machash 'MODAL 'RESULT 'SYN ht2) '(ALL CROSS))
       (member (machash 'MODAL 'RESULT 'SYN ht1) '(ALL CROSS))
       (multiple-value-bind (match b1 b2)
	 (cat-match (machash 'ARG 'SYN ht1) 
		    (machash 'ARG 'SYN ht2))
	 (and match (multiple-value-bind (match2 b12 b22)
		      (cat-match (machash 'RESULT 'RESULT 'SYN ht1)
				 (machash 'ARG 'RESULT 'SYN ht2))
		      (and match2 
			   (let ((newht (make-cky-entry-hashtable))
				 (newsyn2 (make-complex-cat-hashtable))
				 (newsyn (make-complex-cat-hashtable)))
			     (setf (machash 'SEM newht) (&s2 (machash 'SEM ht2) (machash 'SEM ht1)))
			     (setf (machash 'INDEX newht) '|<Sx2|) ; ht1 dir and modality projects below
			     (setf (machash 'SYN newht) newsyn)
			     (setf (machash 'DIR 'SYN newht) (machash 'DIR 'SYN ht1))
			     (setf (machash 'MODAL 'SYN newht) (machash 'MODAL 'SYN ht1))
			     (setf (machash 'ARG 'SYN newht)
				   (realize-binds (machash 'ARG 'SYN ht1)
			                          (append b1 b12)))
			     (setf (machash 'RESULT 'SYN newht) newsyn2)
			     (setf (machash 'RESULT 'RESULT 'SYN newht)
				   (realize-binds (machash 'RESULT 'RESULT 'SYN ht2) 
						  (append b2 b22)))
			     (setf (machash 'ARG 'RESULT 'SYN newht)
				   (realize-binds (machash 'ARG 'RESULT 'SYN ht1) 
			                          (append b1 b12)))
			     (setf (machash 'DIR 'RESULT 'SYN newht)
				   (machash 'DIR 'RESULT 'SYN ht1))
			     (setf (machash 'MODAL 'RESULT 'SYN newht)
				   (machash 'MODAL 'RESULT  'SYN ht1))
			     newht)))))))

(defun f3-comp (ht1 ht2) 
  ">B^3"
  (and (complexp-hash (machash 'SYN ht1))
       (complexp-hash (machash 'SYN ht2))
       (eql (machash 'DIR 'SYN ht1) 'FS)
       (member (machash 'MODAL 'SYN ht1) '(ALL HARMONIC))
       (machash 'DIR 'RESULT 'SYN ht2) ; ht2 must have a really complex result
       (machash 'DIR 'RESULT 'RESULT 'SYN ht2)
       (eql (machash 'DIR 'RESULT 'RESULT 'SYN ht2) 'FS)
       (not (eql (machash 'MODAL 'SYN ht2) 'STAR)) ; main functor must allow composition
       (member (machash 'MODAL 'RESULT 'RESULT 'SYN ht2) '(ALL HARMONIC))
       (multiple-value-bind (match b1 b2)
	 (cat-match (machash 'ARG 'SYN ht1) 
		    (machash 'RESULT 'RESULT 'RESULT 'SYN ht2))
	 (and match (let ((newht (make-cky-entry-hashtable))
			  (newsyn1 (make-complex-cat-hashtable))
			  (newsyn2 (make-complex-cat-hashtable))
			  (newsyn3 (make-complex-cat-hashtable)))
		      (setf (machash 'SEM newht) (&b3 (machash 'SEM ht1) (machash 'SEM ht2)))
		      (setf (machash 'INDEX newht) '|>B3|) ; ht2 dir and modality projects
		      (setf (machash 'SYN newht) newsyn1)
		      (setf (machash 'DIR 'SYN newht) (machash 'DIR 'SYN ht2))
		      (setf (machash 'MODAL 'SYN newht) (machash 'MODAL 'SYN ht2))
		      (setf (machash 'ARG 'SYN newht)
			    (realize-binds (machash 'ARG 'SYN ht2) b2))
		      (setf (machash 'RESULT 'SYN newht) newsyn2)
		      (setf (machash 'DIR 'RESULT 'SYN newht) 
			    (machash 'DIR 'RESULT 'SYN ht2))
		      (setf (machash 'MODAL 'RESULT 'SYN newht) 
			    (machash 'MODAL 'RESULT 'SYN ht2))
		      (setf (machash 'ARG 'RESULT 'SYN newht)
			    (realize-binds (machash 'ARG 'RESULT 'SYN ht2) b2))
		      (setf (machash 'RESULT 'RESULT 'SYN newht) newsyn3)
		      (setf (machash 'RESULT 'RESULT 'RESULT 'SYN newht)
			    (realize-binds (machash 'RESULT 'SYN ht1) b1))
		      (setf (machash 'ARG 'RESULT 'RESULT 'SYN newht)
			    (realize-binds (machash 'ARG 'RESULT 'RESULT 'SYN ht2) b2))
		      (setf (machash 'DIR 'RESULT 'RESULT 'SYN newht)
			    (machash 'DIR 'RESULT 'RESULT 'SYN ht2))
		      (setf (machash 'MODAL 'RESULT 'RESULT 'SYN newht)
			    (machash 'MODAL 'RESULT 'RESULT 'SYN ht2))
		      newht)))))

(defun fx3-comp (ht1 ht2) 
  ">Bx^3"
  (and (complexp-hash (machash 'SYN ht1))
       (complexp-hash (machash 'SYN ht2))
       (eql (machash 'DIR 'SYN ht1) 'FS)
       (member (machash 'MODAL 'SYN ht1) '(ALL CROSS))
       (machash 'DIR 'RESULT 'SYN ht2) ; ht2 must have a really complex result
       (machash 'DIR 'RESULT 'RESULT 'SYN ht2)
       (eql (machash 'DIR 'RESULT 'RESULT 'SYN ht2) 'BS)
       (not (eql (machash 'MODAL 'SYN ht2) 'STAR)) ; main functor must allow composition
       (member (machash 'MODAL 'RESULT 'RESULT 'SYN ht2) '(ALL CROSS))
       (multiple-value-bind (match b1 b2)
	 (cat-match (machash 'ARG 'SYN ht1) 
		    (machash 'RESULT 'RESULT 'RESULT 'SYN ht2))
	 (and match (let ((newht (make-cky-entry-hashtable))
			  (newsyn1 (make-complex-cat-hashtable))
			  (newsyn2 (make-complex-cat-hashtable))
			  (newsyn3 (make-complex-cat-hashtable)))
		      (setf (machash 'SEM newht) (&b3 (machash 'SEM ht1) (machash 'SEM ht2)))
		      (setf (machash 'INDEX newht) '|>Bx3|) ; ht2 dir and modality projects
		      (setf (machash 'SYN newht) newsyn1)
		      (setf (machash 'DIR 'SYN newht) (machash 'DIR 'SYN ht2))
		      (setf (machash 'MODAL 'SYN newht) (machash 'MODAL 'SYN ht2))
		      (setf (machash 'ARG 'SYN newht)
			    (realize-binds (machash 'ARG 'SYN ht2) b2))
		      (setf (machash 'RESULT 'SYN newht) newsyn2)
		      (setf (machash 'DIR 'RESULT 'SYN newht) 
			    (machash 'DIR 'RESULT 'SYN ht2))
		      (setf (machash 'MODAL 'RESULT 'SYN newht) 
			    (machash 'MODAL 'RESULT 'SYN ht2))
		      (setf (machash 'ARG 'RESULT 'SYN newht)
			    (realize-binds (machash 'ARG 'RESULT 'SYN ht2) b2))
		      (setf (machash 'RESULT 'RESULT 'SYN newht) newsyn3)
		      (setf (machash 'RESULT 'RESULT 'RESULT 'SYN newht)
			    (realize-binds (machash 'RESULT 'SYN ht1) b1))
		      (setf (machash 'ARG 'RESULT 'RESULT 'SYN newht)
			    (realize-binds (machash 'ARG 'RESULT 'RESULT 'SYN ht2) b2))
		      (setf (machash 'DIR 'RESULT 'RESULT 'SYN newht)
			    (machash 'DIR 'RESULT 'RESULT 'SYN ht2))
		      (setf (machash 'MODAL 'RESULT 'RESULT 'SYN newht)
			    (machash 'MODAL 'RESULT 'RESULT 'SYN ht2))
		      newht)))))

(defun b3-comp (ht1 ht2) 
  "<B^3"
  (and (complexp-hash (machash 'SYN ht1))
       (complexp-hash (machash 'SYN ht2))
       (eql (machash 'DIR 'SYN ht2) 'BS)
       (member (machash 'MODAL 'SYN ht2) '(ALL HARMONIC))
       (machash 'DIR 'RESULT 'SYN ht1) ; ht1 must have a really complex result
       (machash 'DIR 'RESULT 'RESULT 'SYN ht1)
       (eql (machash 'DIR 'RESULT 'RESULT 'SYN ht1) 'BS)
       (not (eql (machash 'MODAL 'SYN ht1) 'STAR)) ; main functor must allow composition
       (member (machash 'MODAL 'RESULT 'RESULT 'SYN ht1) '(ALL HARMONIC))
       (multiple-value-bind (match b1 b2)
	 (cat-match (machash 'RESULT 'RESULT 'RESULT 'SYN ht1)
		    (machash 'ARG 'SYN ht2)) 
	 (and match (let ((newht (make-cky-entry-hashtable))
			  (newsyn1 (make-complex-cat-hashtable))
			  (newsyn2 (make-complex-cat-hashtable))
			  (newsyn3 (make-complex-cat-hashtable)))
		      (setf (machash 'SEM newht) (&b3 (machash 'SEM ht2) (machash 'SEM ht1)))
		      (setf (machash 'INDEX newht) '|<B3|) ; ht1 dir and modality projects
		      (setf (machash 'SYN newht) newsyn1)
		      (setf (machash 'DIR 'SYN newht) (machash 'DIR 'SYN ht1))
		      (setf (machash 'MODAL 'SYN newht) (machash 'MODAL 'SYN ht1))
		      (setf (machash 'ARG 'SYN newht)
			    (realize-binds (machash 'ARG 'SYN ht1) b1))
		      (setf (machash 'RESULT 'SYN newht) newsyn2)
		      (setf (machash 'DIR 'RESULT 'SYN newht) 
			    (machash 'DIR 'RESULT 'SYN ht1))
		      (setf (machash 'MODAL 'RESULT 'SYN newht) 
			    (machash 'MODAL 'RESULT 'SYN ht1))
		      (setf (machash 'ARG 'RESULT 'SYN newht)
			    (realize-binds (machash 'ARG 'RESULT 'SYN ht1) b1))
		      (setf (machash 'RESULT 'RESULT 'SYN newht) newsyn3)
		      (setf (machash 'RESULT 'RESULT 'RESULT 'SYN newht)
			    (realize-binds (machash 'RESULT 'SYN ht2) b2))
		      (setf (machash 'ARG 'RESULT 'RESULT 'SYN newht)
			    (realize-binds (machash 'ARG 'RESULT 'RESULT 'SYN ht1) b1))
		      (setf (machash 'DIR 'RESULT 'RESULT 'SYN newht)
			    (machash 'DIR 'RESULT 'RESULT 'SYN ht1))
		      (setf (machash 'MODAL 'RESULT 'RESULT 'SYN newht)
			    (machash 'MODAL 'RESULT 'RESULT 'SYN ht1))
		      newht)))))

(defun bx3-comp (ht1 ht2) 
  "<Bx^3"
  (and (complexp-hash (machash 'SYN ht1))
       (complexp-hash (machash 'SYN ht2))
       (eql (machash 'DIR 'SYN ht2) 'BS)
       (member (machash 'MODAL 'SYN ht2) '(ALL CROSS))
       (machash 'DIR 'RESULT 'SYN ht1) ; ht1 must have a really complex result
       (machash 'DIR 'RESULT 'RESULT 'SYN ht1)
       (eql (machash 'DIR 'RESULT 'RESULT 'SYN ht1) 'FS)
       (not (eql (machash 'MODAL 'SYN ht1) 'STAR)) ; main functor must allow composition
       (member (machash 'MODAL 'RESULT 'RESULT 'SYN ht1) '(ALL CROSS))
       (multiple-value-bind (match b1 b2)
	 (cat-match (machash 'RESULT 'RESULT 'RESULT 'SYN ht1)
		    (machash 'ARG 'SYN ht2)) 
	 (and match (let ((newht (make-cky-entry-hashtable))
			  (newsyn1 (make-complex-cat-hashtable))
			  (newsyn2 (make-complex-cat-hashtable))
			  (newsyn3 (make-complex-cat-hashtable)))
		      (setf (machash 'SEM newht) (&b3 (machash 'SEM ht2) (machash 'SEM ht1)))
		      (setf (machash 'INDEX newht) '|<Bx3|) ; ht1 dir and modality projects
		      (setf (machash 'SYN newht) newsyn1)
		      (setf (machash 'DIR 'SYN newht) (machash 'DIR 'SYN ht1))
		      (setf (machash 'MODAL 'SYN newht) (machash 'MODAL 'SYN ht1))
		      (setf (machash 'ARG 'SYN newht)
			    (realize-binds (machash 'ARG 'SYN ht1) b1))
		      (setf (machash 'RESULT 'SYN newht) newsyn2)
		      (setf (machash 'DIR 'RESULT 'SYN newht) 
			    (machash 'DIR 'RESULT 'SYN ht1))
		      (setf (machash 'MODAL 'RESULT 'SYN newht) 
			    (machash 'MODAL 'RESULT 'SYN ht1))
		      (setf (machash 'ARG 'RESULT 'SYN newht)
			    (realize-binds (machash 'ARG 'RESULT 'SYN ht1) b1))
		      (setf (machash 'RESULT 'RESULT 'SYN newht) newsyn3)
		      (setf (machash 'RESULT 'RESULT 'RESULT 'SYN newht)
			    (realize-binds (machash 'RESULT 'SYN ht2) b2))
		      (setf (machash 'ARG 'RESULT 'RESULT 'SYN newht)
			    (realize-binds (machash 'ARG 'RESULT 'RESULT 'SYN ht1) b1))
		      (setf (machash 'DIR 'RESULT 'RESULT 'SYN newht)
			    (machash 'DIR 'RESULT 'RESULT 'SYN ht1))
		      (setf (machash 'MODAL 'RESULT 'RESULT 'SYN newht)
			    (machash 'MODAL 'RESULT 'RESULT 'SYN ht1))
		      newht)))))

(defun f-special (ht1 ht2)
  "@.. cats can only apply. We assume there is one unknown in such cats, and that all such cats are functors."
  (and (specialp-hash (machash 'SYN ht1))
       (eql (machash 'DIR 'SYN ht1) 'FS)
       (not (specialp-hash (machash 'SYN ht2)))
       (let ((newht (make-cky-entry-hashtable)))
	 (setf (machash 'SEM newht) (&a (machash 'SEM ht1) (machash 'SEM ht2)))
	 (setf (machash 'INDEX newht) '|>|)
	 (setf (machash 'SYN newht)(substitute-special-cat   ; pass on a fresh copy for substtn
				     (machash 'RESULT 'SYN ht1)
				     (copy-hashtable (machash 'SYN ht2))))
         newht)))

(defun b-special (ht1 ht2)
  "@.. cats can only apply. We assume there is one unknown in such cats, and that all such cats are functors."
  (and (specialp-hash (machash 'SYN ht2))
       (eql (machash 'DIR 'SYN ht2) 'BS)
       (not (specialp-hash (machash 'SYN ht1)))
       (let ((newht (make-cky-entry-hashtable)))
	 (setf (machash 'SEM newht) (&a (machash 'SEM ht2) (machash 'SEM ht1)))
	 (setf (machash 'INDEX newht) '|<|)
	 (setf (machash 'SYN newht)(substitute-special-cat   ; pass on a fresh copy for substtn
				     (machash 'RESULT 'SYN ht2)
				     (copy-hashtable (machash 'SYN ht1))))
         newht)))

(defun ccg-combine (ht1 ht2 lex1 lex2)
  "Short-circuit evaluates ccg rules one by one, to left term (ht1) and right term (ht2), which are hashtables.
  Returns the result as a hashtable.
  Note: CCG is procedurally neutral, i.e. given two cats, the other is uniquely determined
  if combinable (see Pareschi & steedman 1987). Therefore only one rule can succeed if
  lexical cats never use category variables (we don't do that). Eat your heart out, unifiers!!
  So we return immediately once a rule succeeds, because of this paradeterminism.
  The universal list of rules is from Bozsahin (2012) CL book, p117.
  NB: No type-raising or unary rule! They do not combine.
  Global switches give the model developer complete control over rule application.
  Set its switch to nil if you dont want that rule.  By default all rules are on.
  x-special are for application only. So they use their switches.
  Reminder to code developers: every combination creates a new CKY hashtable entry, and as many
  complex result hashtables as there are slashes in the result."
  (cond ((and (basicp-hash (machash 'SYN ht1))
	      (basicp-hash (machash 'SYN ht2)))  ; both are basic cats, the only non-combinable case
	 (return-from ccg-combine nil))
	((and (complexp-hash ht1)
	      (complexp-hash ht2)
	      (eql (machash 'DIR 'SYN ht1) 'BS)
	      (eql (machash 'DIR 'SYN ht2) 'FS)) ; the only case which no rule can combine 
	 (return-from ccg-combine nil)))
  (or (and *f-apply* (f-apply ht1 ht2 lex2))    ; application -- the only relevant case for lex slash
      (and *b-apply* (b-apply ht1 ht2 lex1))
      (and *f-comp* (f-comp ht1 ht2))           ; composition
      (and *b-comp* (b-comp ht1 ht2))
      (and *fx-comp* (fx-comp ht1 ht2))
      (and *bx-comp* (bx-comp ht1 ht2))
      (and *f-sub* (f-sub ht1 ht2))             ; substitution
      (and *b-sub* (b-sub ht1 ht2))
      (and *fx-sub* (fx-sub ht1 ht2))
      (and *bx-sub* (bx-sub ht1 ht2))
      (and *f-subbar* (f-subbar ht1 ht2))       ; substitution bar (aka lost combinator)
      (and *b-subbar* (b-subbar ht1 ht2))
      (and *fx-subbar* (fx-subbar ht1 ht2))
      (and *bx-subbar* (bx-subbar ht1 ht2))
      (and *f-subcomp* (f-subcomp ht1 ht2))     ; subcomposition (i.e. D/O)
      (and *b-subcomp* (b-subcomp ht1 ht2))
      (and *fx-subcomp* (fx-subcomp ht1 ht2))
      (and *bx-subcomp* (bx-subcomp ht1 ht2))
      (and *f2-comp* (f2-comp ht1 ht2))         ; B^2
      (and *b2-comp* (b2-comp ht1 ht2))
      (and *fx2-comp* (fx2-comp ht1 ht2))
      (and *bx2-comp* (bx2-comp ht1 ht2))
      (and *f2-sub* (f2-sub ht1 ht2))           ; S'' (not S^2 of Curry; see Bozsahin CL book)
      (and *b2-sub* (b2-sub ht1 ht2))
      (and *fx2-sub* (fx2-sub ht1 ht2))
      (and *bx2-sub* (bx2-sub ht1 ht2))
      (and *f3-comp* (f3-comp ht1 ht2))         ; B^3
      (and *b3-comp* (b3-comp ht1 ht2))
      (and *fx3-comp* (fx3-comp ht1 ht2))
      (and *bx3-comp* (bx3-comp ht1 ht2))
      (and *f-apply* (f-special ht1 ht2))       ; application only special cats @X, @Y ...
      (and *b-apply* (b-special ht1 ht2))))

(defun apply-unary-rules (i j m lexp)
  "applies all the unary rules to the result in CKY cell i j k, where k=1,...m.
  Creates more types of same length in the cell i j starting with m+1.
  NB. A later rule can see results of earlier rules; the loop goes up to r, not m.
  The semantics of lexical rule is application of its 'outsem to lf of current cell.
  Hence lf 'insem is syntactic sugar, a recipe to write lfs of lexical rules compositionally."
  (cond ((or (null (machash (list i j 1) *cky-hashtable*)) (null *lex-rules-table*))
	 (return-from apply-unary-rules nil))
	(t (let ((r m))
	     (dolist (lr *lex-rules-table*) ; i use lexical rules as synonymous with unary rules
	       (loop for k from 1 to r do
		     (multiple-value-bind (match b1 b2)
;		       (declare (ignore b1))
		       (cat-match (machash 'SYN (nv-list-val 'SOLUTION (machash (list i j k) *cky-hashtable*)))
				  (machash 'INSYN lr))
		       (and match	   
			    (setf r (+ r 1))
			    (let ((newht (make-cky-entry-hashtable))
				  (nlr (copy-hashtable (machash 'OUTSYN lr))))
			      (setf (machash 'SEM newht)      
				    (&a (machash 'OUTSEM lr)
					(machash 'SEM (nv-list-val 'SOLUTION 
								   (machash (list i j k) *cky-hashtable*)))))
			      (setf (machash 'PARAM newht) (f-param-inner-prod 
							     (machash 'PARAM lr)
							     (machash 'PARAM (nv-list-val 'SOLUTION
							       (machash (list i j k) *cky-hashtable*)))))
			      (setf (machash 'INDEX newht) (machash 'INDEX lr))
			      (setf (machash 'KEY newht) (machash 'KEY lr))
			      (setf (machash 'SYN newht) (realize-binds nlr b2))
			      (if lexp   ; slightly less consing this way -- lexical rules on lex item is also lexical, otherwise not
                                  (setf (machash (list i j r) *cky-hashtable*)
					(list 
					  (list 'LEFT (list i j k))
					  (list 'RIGHT (list i j k))
					  (list 'SOLUTION newht)
					  (list 'LEX t)))
			          (setf (machash (list i j r) *cky-hashtable*)
					(list 
					  (list 'LEFT (list i j k))
					  (list 'RIGHT (list i j k))
					  (list 'SOLUTION newht))))))))))))
  t)

(defun ccg-deduce (itemslist)
  "CKY-parses the items in the input list.
  The lower-triangular matrix of CKY is built as a hashtable
  where keys are triplets (i j k), meaning combinations of length i,
  starting with position j, yielding reading k."
  (cond ((listp itemslist)
	 (clrhash *cky-hashtable*)
	 (clrhash *cky-lf-hashtable*)
	 (setf *cky-lf* nil)(setf *cky-argmax-lf* nil)
	 (setf *cky-argmax-lf-max* nil)(setf *cky-max* nil)
	 (let ((n (length itemslist))
	       (a 0))  ; number of readings per CKY cell
	   (loop for i from 1 to n do  ; lex loop
		 (let* ((matches (get-gram-items (nth (- i 1) itemslist)))
			(n2 (length matches)))
		   (cond  ((eql n2 0)
			   (format t "No lex entry for ~A! Exiting without parse.~%"
					  (nth (- i 1) itemslist))
			   (return-from ccg-deduce nil)))
		   (loop for i2 from 1 to n2 do
			 (setf (machash (list 1 i i2) *cky-hashtable*) 
			       (list (list 'LEFT (list 1 i i2))
				     (list 'RIGHT (list 1 i i2))
				     (list 'SOLUTION (hash-lex (nth (- i2 1) matches)))
				     (list 'LEX t))))
                   (apply-unary-rules 1 i n2 t))) 
	   (setf *cky-input* itemslist)
	   (loop for i from 2 to n do ; i j k are CKY loops
             (loop for j from 1 to (+ (- n i) 1) do
	       (setf a 0) 
	       (loop for k from 1 to (- i 1) do
	         (do ((p 1 (+ p 1)))  ; p q loop over multiple readings in cky slots
		     ((not (machash (list k j p) *cky-hashtable*)))
		     (do ((q 1 (+ q 1)))
		         ((not (machash (list (- i k) (+ j k) q) *cky-hashtable*)))
                         (let ((result (ccg-combine 
                                 (nv-list-val 'SOLUTION (machash (list k j p) *cky-hashtable*))
				 (nv-list-val 'SOLUTION (machash (list (- i k) (+ j k) q) *cky-hashtable*))
				 (nv-list-val 'LEX (machash (list k j p) *cky-hashtable*))
				 (nv-list-val 'LEX (machash (list (- i k) (+ j k) q) *cky-hashtable*))
				 )))
			   (and result 
				(setf (machash 'PARAM result)  ; calculate inner product on the fly
				      (f-param-inner-prod 
					(machash 'PARAM 
						 (nv-list-val 'SOLUTION 
								(machash (list k j p) *cky-hashtable*)))
					(machash 'PARAM 
						 (nv-list-val 'SOLUTION (machash (list (- i k) (+ j k) q)
				                                   *cky-hashtable*)))))
                                (setf a (+ a 1))
				(setf (machash (list i j a) *cky-hashtable*)
				      (if (machash 'LEX result)  ; if result is lexical, this is marked in its hashtable, pass it on to cky
					(list (list 'LEFT (list k j p))
					      (list 'RIGHT (list (- i k) (+ j k) q))
					      (list 'LEX t)
					      (list 'SOLUTION result))
					(list (list 'LEFT (list k j p))
					      (list 'RIGHT (list (- i k) (+ j k) q))
					      (list 'SOLUTION result)))))))))
	       (apply-unary-rules i j a nil)))
	   (and (machash (list n 1 1) *cky-hashtable*) t)))  ; if a rule applied, result would be in n 1 1 
	(t (format t "Error: expected a list of items.~%"))))

;;;; =============================================================================
;;;; == Part 3: The CKY parse ranker for CCG -- the inductive component         ==
;;;; =============================================================================


(defun cky-find-argmax-lf ()
  "finds the most likely LF for the currently parsed input, and its most probable derivation.
   NB. LF equivalence is checked by Lisp's #'equal predicate for the hashtable.
   We don't use exp function because the denominator in formula (2) of the manual is same,
   we are maximizing, and e^x > e^y iff x > y."
   (setf *cky-lf* nil)
   (setf *cky-argmax-lf* nil)
   (setf *cky-argmax-lf-max* nil)
   (setf *cky-lf-hashtable-sum* 0.0)
   (let ((lfmax most-negative-single-float))
     (maphash #'(lambda (lf info)
	      (progn
	        (setf *cky-lf-hashtable-sum* (+ *cky-lf-hashtable-sum* (first info)))
		(cond ((>= (first info) lfmax)
		       (setf lfmax (first info))
		       (setf *cky-lf* (list (first info) lf))
		       (setf *cky-argmax-lf* (second info)))))) ; keep first as list, then find max. prob in it
	      *cky-lf-hashtable*))
   (let ((lfmax most-negative-single-float)
         (maxcell nil))
     (dolist (cell *cky-argmax-lf*)
       (cond ((> (machash 'PARAM (nv-list-val 'SOLUTION (machash cell *cky-hashtable*))) lfmax)
              (setf lfmax (machash 'PARAM (nv-list-val 'SOLUTION (machash cell *cky-hashtable*))))
	      (setf maxcell cell))))
     (setf *cky-argmax-lf-max* maxcell)))

(defun add-to-cky-lf-sum (cell)
  "adds the inner product for LF in cell to the lf hashtable."
  (let ((lf (beta-normalize-outer (cky-sem cell))) 
	(flag t)) ; to avoid double counts because of non-equalp but beta-equalp terms 
    (maphash #'(lambda (savedlf val)  ; savedlf s are beta-normalized
		 (declare (ignore val))
		 (cond ((alpha-equivalent lf savedlf)
			(setf flag nil)
			(setf (machash savedlf *cky-lf-hashtable*)
			      (list (+ (first (machash savedlf *cky-lf-hashtable*))
				       (machash 'PARAM (nv-list-val 'SOLUTION (machash cell *cky-hashtable*))))
				    (cons cell (second (machash savedlf *cky-lf-hashtable*))))))))
	     *cky-lf-hashtable*)
    (and flag (setf (machash lf *cky-lf-hashtable*)
		    (list (machash 'PARAM (nv-list-val 'SOLUTION (machash cell *cky-hashtable*)))
			  (list cell))))))

(defun cky-show-probs (cell)
  "to show a derivation with its counts"
  (cond ((null (machash cell *cky-hashtable*)) 
	 (format t "~%No such parse! (cky-show-probs)")
	 (return-from cky-show-probs ""))
	(t (let* ((solution (nv-list-val 'SOLUTION (machash cell *cky-hashtable*)))
		  (l (nv-list-val 'LEFT (machash cell *cky-hashtable*)))
		  (r (nv-list-val 'RIGHT (machash cell *cky-hashtable*)))
		  (lf (machash 'SEM solution))
		  (pr (machash 'PARAM solution))
		  (ix (machash 'INDEX solution))
	          (inputs (concatenate 'string
			      (write-to-string (input-range (cell-len l)(cell-pos l)))
			      (write-to-string (input-range (cell-len r)(cell-pos r)))))
	          (syn (linearize-syn (machash 'SYN solution))))
	     (cond ((equal l r)   ; we've reached a lexical cell 
		    (cond ((> (cell-len l) 1)
			   (format t (cky-show-probs l)))) ; it may be a lex rule applying to a phrase
		    (if *lfflag* 
		      (format nil "~%~5,,,a~7,,,F~14T~A := ~A~%        : ~A" ix pr (input-range (cell-len l)(cell-pos l)) syn lf)
		      (format nil "~%~5,,,a~7,,,F~14T~A := ~A" ix pr (input-range (cell-len l)(cell-pos l)) syn)))
		   (t (concatenate 'string 
				   (cky-show-probs l)
				   (cky-show-probs r)
				   (if *lfflag* 
				     (format nil "~%~5,,,a~7,,,F~14T~A := ~A~%        : ~A" ix pr inputs syn lf)
				     (format nil "~%~5,,,a~7,,,F~14T~A := ~A" ix pr inputs syn)))))))))

(defun lex-rule-param (key)
  "return the parameter of the lex rule with <key>"
  (dolist (lr *lex-rules-table*)
    (cond ((equal key (machash 'KEY lr))
	   (return-from lex-rule-param (machash 'PARAM lr)))))
  (format t "~%Error! no such lexical rule: ~A" key))

(defun lex-rule-p (key)
  "returns true if key is the key of a lex rule, nil otherwise."
  (and key (dolist (lr *lex-rules-table*)
	     (cond ((eql key (machash 'KEY lr))
		    (return-from lex-rule-p t)))))
  nil)

(defun approximate-lr-use (cell in-cell subtotal lr-param)
  "since we don't have access to lex items fed into lr rule in dynamic programming, we approximate
  relative to their weighted sum by looking at finite history of cell."
  (cond ((eql (cell-len cell) 1)(+ subtotal lr-param))
	;; if cell is larger than lex cell, check the child cells only but not grandchildren
	(t (let ((lchild-par 
		   (machash 'PARAM (nv-list-val 'SOLUTION (machash (nv-list-val 'LEFT (machash in-cell *cky-hashtable*))
				                           *cky-hashtable*))))
                 (rchild-par 
		   (machash 'PARAM (nv-list-val 'SOLUTION (machash (nv-list-val 'RIGHT (machash in-cell *cky-hashtable*))
				                           *cky-hashtable*)))))
	     (+ subtotal lr-param (* (cell-len cell)(/ (+ (max lchild-par rchild-par) 
							  (/ subtotal (cell-len cell))) 
						       subtotal)))))))

(defun sum-inner-product (cell &optional (sum 0.0))
  "local counts are in constituents cells leading to the derivation in <cell>"
  (cond ((null (machash cell *cky-hashtable*)) 
	 (format t "~%No such parse! (sum-inner-product)")
	 (return-from sum-inner-product sum))
	(t (let  ((l (nv-list-val 'LEFT (machash cell *cky-hashtable*)))
		  (r (nv-list-val 'RIGHT (machash cell *cky-hashtable*)))
		  (cell-key (machash 'KEY (nv-list-val 'SOLUTION (machash cell *cky-hashtable*)))))
	     (cond ((equal l r) 
	            (cond ((lex-rule-p cell-key)  
			   (approximate-lr-use cell l (machash 'PARAM (nv-list-val 'SOLUTION (machash l *cky-hashtable*)))
					       (lex-rule-param cell-key)))
			  (t (+ sum (machash 'PARAM (nv-list-val 'SOLUTION 
		                        (machash l *cky-hashtable*)))))))   ; we've reached a lexical cell 
		   (t (+ sum (sum-inner-product l (machash 'PARAM 
				        (nv-list-val 'SOLUTION (machash l *cky-hashtable*))))
                             (sum-inner-product r (machash 'PARAM 
				        (nv-list-val 'SOLUTION (machash r *cky-hashtable*)))))))))))

(defun cky-pprint-probs (cell)
  (format t (cky-show-probs cell)))

(defun cky-show-induction ()
  (format t "~%Most likely LF for the input: ~A~2%  ~A =~%  ~A~2%Cumulative weight:  ~A" *cky-input* 
	  (second *cky-lf*)(display-lf (beta-normalize-outer (second *cky-lf*)))
	  (first *cky-lf*))
  (format t "~2%Most probable derivation for it: ~A~%--------------------------------" *cky-argmax-lf-max*)
  (format t (cky-show-probs *cky-argmax-lf-max*))
  (format t "~2%Final LF, normal-order evaluated: ~2%    ~A =~%    ~A~%" (beta-normalize-outer (cky-sem *cky-argmax-lf-max*))
	  (display-lf (beta-normalize-outer (cky-sem *cky-argmax-lf-max*))))
  (format t "~2%Most weighted derivation : ~A" *cky-max*)
  (format t  "~%--------------------------")
  (format t (cky-show-probs *cky-max*))
  (format t "~2&Final LF, normal-order evaluated: ~2%    ~A =~%    ~A" 
	  (beta-normalize-outer (cky-sem *cky-max*))
	  (display-lf (beta-normalize-outer (cky-sem *cky-max*))))
  (format t "~2%Try (cky-pprint) to see all the parses, including the features,")
  (format t  "~%    (cky-pprint-probs <cell>) to pretty-print the parse in <cell>."))

;;;; =============================================================================
;;;; == Part 4: the modeling component                                          ==
;;;; =============================================================================

;; Please read the opening comments in the beginning of this file and the manual about this component.
;; CCGlab's standard workflow is that of section 2 of Z&C'05.
;; We recommend you write modeling code as add-on, rather than plugging it in here.
;; NB the manual for a suggested workflow.

(defparameter *bign* 0) ; N in Z&C05 -- number of iterations over training data
(defparameter *supervision-pairs-list* nil) ; set of (Si Li) pairs
(defparameter *smalln* 0) ; size of (Si,Li).  n in Z&C05 -- number of supervision data
(defparameter *n-paramaters* 0) ; size of training grammar (which is the number of parameters)
(defparameter *alpha0* 1.0)       ; alpha_0 of Z&C05 - learning rate parameter
(defparameter *c* 1.0)            ; c of Z&C05       - learning rate parameter
(defparameter *training-hashtable* nil); parameter vector x partial derivative hash table, for training
(defparameter *training-non0-hashtable* nil); parameter vector and current nonzero counts

(defun load-supervision (pname)
  (let ((supname (concatenate 'string pname ".sup")))
    (with-open-file (s supname  :direction :input :if-does-not-exist :error) 
      (setf *supervision-pairs-list* (read s)))
    (format t "~%Supervision file loaded: ~A" supname))
  (dolist (s-lf *supervision-pairs-list*)
    (cond ((not (beta-normalize-outer (sup-lf s-lf))) 
	   (format t "~%Warning! This S-LF pair has unnormalizable LF, and may give unexpected stats :~% ~a"
		   s-lf)))))

(defun count-local-structure (resultcell)
  "using the lexical counts, it does the (counts x parameters) scalar multiplication dynamic programming style.
  If you override this definition too, make sure you return non-nil."
  (setf (machash 'PARAM (nv-list-val 'SOLUTION (machash resultcell *cky-hashtable*)))
	 (sum-inner-product resultcell))
  t)

(defun plugin-count-more-substructure (resultcell)
  "Override this definition if you want to count more substructure in a derivational
  history recorded in the result CKY cell <resultcell>. It must return non-nil.
  Currently it does nothing.
  Suggestion: do the override by defining function of same name in your project p's p.lisp code.
  Suggestion 2: make it additive so that you dont lose lexical weighted counts in resultcell."
  resultcell t)

(defun count-feature (key cell &optional (sum 0.0) (flag nil) (lc 0))
  "if the feature/lex item with key is used, return the total count in the derivation, dynamic programming style.
  We cannot use string identity of lex items here because of ambiguity--we need the key of lex item, which is unique.
  The flag is to count multiple occurences of lex rules."
  (cond ((null (machash cell *cky-hashtable*)) 
	 (format t "~%No such parse! (count-feature)")
	 (return-from count-feature 0.0))
	(t (let  ((l (nv-list-val 'LEFT (machash cell *cky-hashtable*)))
		  (r (nv-list-val 'RIGHT (machash cell *cky-hashtable*))))
	     (cond ((equal l r)   ; we've reached a lexical cell. NB: lex rules' keys are saved in hashtable
		    (cond ((lex-rule-p (machash 'KEY (nv-list-val 'SOLUTION (machash cell *cky-hashtable*))))
			   (if (equal key (machash 'KEY (nv-list-val 'SOLUTION (machash cell *cky-hashtable*))))
			     (count-feature key l sum t (+ lc 1)) 
			     (count-feature key l (+ 1 sum) flag lc)))
			  (t (cond ((equal key (machash 'KEY (nv-list-val 'SOLUTION (machash l *cky-hashtable*))))
				    (+ 1 sum))
				   (flag (/ lc 2.0))  ; counted twice because l and r are same
				   (t 0.0)))))
		   (t (+ (count-feature key l (+ 1 sum) flag lc)
                         (count-feature key r (+ 1 sum) flag lc))))))))

(defun ccg-induce (itemslist)
  "Computes formulas (1) and argmax_L of Zettlemoyer & Collins (2005).
  We don't exponentiate (1) to avoid overflows, since sum is the same for argmax_L.
  ccg-deduce calculates local sums using CKY. This function simply sums them."
  (and (not (listp itemslist))(format t "Expected a list!")(return-from ccg-induce nil))
  (let ((n (length itemslist)))
    (and (ccg-deduce itemslist) ; this creates the CKY table with its local counts
	 (do ((maxprob most-negative-single-float)
	      (minprob most-positive-single-float)
	      (cmax 0)
	      (k 1 (+ k 1)))
	   ((null (machash (list n 1 k) *cky-hashtable*))
	    (setf *cky-max* (list n 1 cmax)) ; we will use next 4 information to set the beam later
	    (setf *cky-nparses* (- k 1))
	    t)
	   (count-local-structure (list n 1 k)) ;update sum for results only
	   (plugin-count-more-substructure (list n 1 k))      ; this is a plug-in to count more substructure
	   (add-to-cky-lf-sum (list n 1 k))
	   (let ((param (machash 'PARAM (nv-list-val 'SOLUTION (machash (list n 1 k) *cky-hashtable*)))))
	     (if (> param maxprob)
	       (progn 
		 (setf maxprob param)
		 (setf cmax k)))
	     (if (< param minprob)
	       (setf minprob param))))
	 (cky-find-argmax-lf)
	 t)))

(defun set-training-parameters (bign smalln nparams alpha0 c) 
  "The parameters of the workflow of Z&C'05 for model parameter estimation. 
  Also initializes the paramaters from .ind, and the derivative."
  (setf *bign* bign)
  (setf *smalln* smalln)
  (setf *n-paramaters* nparams)
  (setf *alpha0* alpha0)     
  (setf *c* c)
  (setf *training-hashtable* (make-training-hashtable nparams))
  (setf *training-non0-hashtable* (make-training-hashtable smalln)) ; for inside-outside
  (dolist (l *ccg-grammar*)(mk-train-entry (nv-list-val 'KEY l) (nv-list-val 'PARAM l) 0.0))
  t)

(defun estimate-parameters (k i)
  "the inner loop of Z&C's gradient ascent after the derivative is calculated."
  (maphash #'(lambda (key val)
	       (declare (ignore key))
	       (put-param val (+ (get-param val)
				 (/ (* *alpha0* (get-derivative val))
				       (+ 1 (* *c* (+ i (* k *smalln*))))))))
	   *training-hashtable*))


(defun pprint-hashtable (ht)
  (format t "~%=========~%Hash Table: key val")
  (maphash #'(lambda (k v)(format t "~%~a  ~a" k v)) ht))

(defun update-derivative (key in-sum all-sum li-sum all-li-sum verbose debug)
  (and debug (format t "~%Update derivative: ~A~%" (list key in-sum all-sum li-sum all-li-sum)))
  (cond ((eql in-sum 0.0) (setf in-sum 1.0))) ; penalize badly if no corr soln but avoid DBZ.(li-sum==0 anyway)
  (cond ((eql all-sum 0.0) (setf all-sum 1.0))) ; penalize badly if no corr soln but avoid DBZ.(all-li-sum==0 anyway)
  (put-derivative key (- (/ li-sum in-sum)  ; li-sums are f_je^p+... , in-sums are e^p+... 
			                    ; we get probabilities by dividing, formula (2) style
					    ; and gradient by difference, as in formula (5) in the manual.
			 (/ all-li-sum all-sum)))
  (and verbose (pprint-hashtable *training-hashtable*)))

(defun make-sorted-solutions (r1 r2)
  "Creates a list of lists whose first el is analysis no  (3rd item of result cell r1 r2 r3) and second el is cell parameter; returns sorted list"
  (let ((solutions nil))
    (do* ((r3 1 (+ r3 1)))
      ((null (machash (list r1 r2 r3) *cky-hashtable*))) ; loop for every solution 
      (push (list  r3 (get-cell-param (list r1 r2 r3))) solutions))
    (sort solutions #'> :key #'second)))

(defun inside-outside ()
  "inside-outside algorithm to find non zero counts--all others considered 0. Go as much as beam"
  (clrhash *training-non0-hashtable*) ; clear counts
  (let ((pairindex 0))
    (dolist (s-lf *supervision-pairs-list*)
      (incf pairindex)
      (let* ((s (ccg-induce (sup-sentence s-lf)))
	     (b (and s *beamp* (beamer))) ;sets  beam parameter -- reduce more for more parses
	     (r1 (cell-len *cky-max*))
	     (r2 (cell-pos *cky-max*))
	     (solutions (make-sorted-solutions r1 r2)) 
	     (keylist nil))
	(declare (ignore b))
	(maphash #'(lambda (key val) ; the table was prepared by set-training-parameters
		     (declare (ignore val))
		     (block analyses
			    (let ((cnt 1))
			      (dolist 
				(solution solutions)
				(and *beamp* (> cnt *beam*) (return-from analyses)) ; stop
				(incf cnt)
				(if (> (count-feature key (list r1 r2 (first solution))) 0.0) 
				  (progn 
				    (push key keylist)
				    (return-from analyses)))))))  ; finding the item in one result is enough; derivative will calculate sums
		 *training-hashtable*)
	(setf (machash pairindex *training-non0-hashtable*) keylist)))))

(defun prepare-solutions (debug)
  "after parses for current training pair are found, this function finds the nonzero counts in them,
  and places only those in the non0 training table. If beam is on, it creates a sorted list of solutions"
  (and *beamp* (beamer)) ;sets  beam parameter -- reduce more for more parses
  (let ((r1 (cell-len *cky-max*))
	(r2 (cell-pos *cky-max*)))
    (setf *training-sorted-solutions-list* (make-sorted-solutions r1 r2)) ;do before in-out for beam effect on both find-derivative and in-out
    (and debug (format t "~%Number of sorted solutions = ~A" (length *training-sorted-solutions-list*)))))

(defun find-derivative-of-log-likelihood (s-lf pairindex verbose debug)
  "given (Si Li) pair find the partial derivative of log likelihood.
  This is the PCCG variant of the inside-outside algorithm, where training-hashtable keeps all weights.
  What we get is f_je^param1+f_j^param2...-f_je^param+f_je^param counts first.
  Then update-derivative turns them into probabilities by dividing into sums."
  (let* ((result (ccg-induce (sup-sentence s-lf)))   ; get all analyses. we will filter later (ie No Normal form parsing)
	 (lf (and result (beta-normalize-outer (sup-lf s-lf))))
	 (s (and result (prepare-solutions debug))) ; sets beam, and produces *training-sorted-solutions-list*
	 (nonzerokeys (machash pairindex *training-non0-hashtable*)) ; table was set by inside-outside
	 (r1 (cell-len *cky-max*))
	 (r2 (cell-pos *cky-max*)))
    (declare (ignore s))
    (cond (result
	    (dolist (key nonzerokeys)
	      (let ((in-sum 0.0)
		    (all-sum 0.0)
		    (li-sum 0.0)
		    (all-li-sum 0.0)
		    (cnt 1))
		(block analyses
		       (dolist 
			 (analysis-param *training-sorted-solutions-list*)
			 (and *beamp* (> cnt *beam*) (return-from analyses)) ; stop
			 (incf cnt)
			 (let* ((term-cell (second analysis-param)) ; already fetched by make-sorted-solutions
				(term-c (count-feature key (list r1 r2 (first analysis-param)))) ; this one needs CKY access
				(term-e (exp term-cell)) ; get e^param but not divide by sum until found-- see update-derivative
				(term (* term-c term-e))
				(cell-lf (beta-normalize-outer (cky-sem (list r1 r2 (first analysis-param)))))) ; this needs CKY access too
			   (and debug (format t "~&Find derivative: ~A~%" 
					      (list key term-c term-e term r1 r2 (first analysis-param) *cky-nparses*)))
			   (cond ((alpha-equivalent lf cell-lf)
				  (setf in-sum (+ in-sum term-e))
				  (setf all-sum (+ all-sum term-e))
				  (setf li-sum (+ li-sum term))
				  (setf all-li-sum (+ all-li-sum term)))
				 (t 
				   (setf all-sum (+ all-sum term-e))
				   (setf all-li-sum (+ all-li-sum term)))))))
		(update-derivative key in-sum all-sum li-sum all-li-sum verbose debug))))
	  (t (format t "~%*** Unparsable training data! ~A~%Either fix or eliminate the pair from training set~%" s-lf)))))

(defun stochastic-gradient-ascent (verbose debug) ; this is done per Li, Si, hence it is stochastic
  (loop for k from 0 to (- *bign* 1) do 
    (loop for i from 1 to *smalln* do
      (and debug (format t "~%---------------------------------~%Iteration k i= ~A  ~A~%" k i))
      (find-derivative-of-log-likelihood (elt *supervision-pairs-list* (- i 1)) i verbose debug)
      (estimate-parameters k i)))
  (format t "~%Done. use (show-training/save-training) to see/save the results")t)

(defun update-model (pname iterations alpha0 c &key (verbose nil)(load nil) (debug nil))
  "general workflow for updating model parameters of a project. Compare and save are separate."
  (beam-value) ;; in case you want to abort a misguided looong training asap
  (and load (load-model pname)) ; loads the .ind file into *ccg-grammar*
  (and load (load-supervision pname)) ; (Si Li) pairs loaded into *supervision-pairs-list*
  (set-training-parameters iterations (length *supervision-pairs-list*)(length *ccg-grammar*) alpha0 c)
  (inside-outside) ; redundantly parse all sup pairs once to create hash table of nonzero counts for every pair
                   ; we're trying to avoid recalculating counts since they dont change over iterations
  (stochastic-gradient-ascent verbose debug))

(defun show-training ()
  "show the values of parameters per key before and after training"
  (format t "The rule set used in the experiment:~%")
  (switches)
  (format t "~%Training parameters: N = ~a alpha0 = ~a c = ~a n = ~a  " 
	  *bign*  *alpha0* *c* *smalln*)
  (beam-value)
  (format t "~%Model parameters before and after training~%================================================")
  (format t "~%key   lex             initial  final    diff ~%------------------------------------------------")
  (dolist (l *ccg-grammar*)
    (let ((feat (if (lex-rule-p (nv-list-val 'KEY l)) 'INDEX 'PHON)))
      (format t "~%~5,,,A ~12,,,A ~8,,,F ~8,,,F  (~8,,,F)"
	      (nv-list-val 'KEY l) (nv-list-val feat l) (nv-list-val 'PARAM l) (get-key-param (nv-list-val 'KEY l))
	      (- (get-key-param (nv-list-val 'KEY l)) (nv-list-val 'PARAM l)))))
  (format t "~%================================================"))

(defun save-grammar (out)
  "this save is baroque to make it lisp reload-able"
  (with-open-file (s out :direction :output :if-exists :supersede) 
    (format s "(defparameter *ccg-grammar*~%")
    (format s "'")
    (prin1 *ccg-grammar* s)
    (format s ")~%")))

(defun save-training (out)
  (or out (format t "please specify an output file to avoid unintentional overrides") 
      (return-from save-training))
  (dolist (l *ccg-grammar*)
    (setf (nv-list-val 'PARAM l) (get-key-param (nv-list-val 'KEY l))))
  (save-grammar out))

(defun z-score-grammar ()
  "turns current parameter values to z-scores with normal distribution N(0,1).
  Now all parameters are factors apart from population standard deviation with same variance as original sample."
  (if (< (length *ccg-grammar*) 2)
    (format t "Nothing to z-score!")
    (let ((sumsq 0.0) ; find standard deviation and mean in one pass, from Guttman/Wilks/Hunter 
	  (sum  0.0)
	  (std  0.0)
	  (mean 0.0)
	  (n (length *ccg-grammar*)))
      (dolist (item *ccg-grammar*)
	(setf sumsq (+ sumsq (expt (nv-list-val 'PARAM item) 2)))
	(setf sum (+ sum (nv-list-val 'PARAM item))))
      (setf std (sqrt (/ (- sumsq (/ (expt sum 2) n)) (- n 1))))
      (if (< std least-positive-short-float) 
	(format t "No variation, no change")
	(let ((minw most-positive-single-float)
	      (maxw most-negative-single-float))
	  (setf mean (/ sum n))
	  (dolist (item *ccg-grammar*)
	    (setf (nv-list-val 'PARAM item) (/ (- (nv-list-val 'PARAM item) mean) std))
	    (if (> (nv-list-val 'PARAM item) maxw) (setf maxw (nv-list-val 'PARAM item)))
	    (if (< (nv-list-val 'PARAM item) minw) (setf minw (nv-list-val 'PARAM item))))
	  (format t "Max z-score = ~A, Min z-score = ~A~%" maxw minw)
	  (format t "Done. Use save-grammar to save the changes in a file"))))))

(defun show-lf ()
  (setf *lfflag* t)(format t "All LFs will be shown~%"))

(defun hide-lf ()
  (setf *lfflag* nil)(format t "Only final LF will be shown~%"))

(defun mklist (obj)
  (if (listp obj) obj (list obj)))

(defun reset-globals()
  (setf *print-readably* nil)
  (setf *print-pretty* t) 
  (setf *lex-rules-table* nil)
  (clrhash *cky-hashtable*)
  (clrhash *cky-lf-hashtable*)
  (setf *cky-lf-hashtable-sum* 0.0)
  (setf *cky-input* nil) 
  (setf *cky-max* nil)
  (show-lf)
  (beam-off)
  (setf *cky-argmax-lf-max* nil) 
  (setf *cky-argmax-lf* nil)
  (setf *cky-lf* nil) 
  (setf *loaded-grammar* "")
  (setf *ccg-grammar*  nil)
  (setf *ccg-grammar-keys*  0)
  t)

(defun read1 (fn)
  "reads one lisp object from file fn in one fell swoop"
  (with-open-file (s fn :direction :input :if-does-not-exist :error) (read s)))

(defun write1 (fn obj)
  "writes one lisp object from file fn in one fell swoop"
  (with-open-file (s fn :direction :output :if-exists :error) (format  s "~A~%" obj)))

;; ======================================
;; some shortcuts for top-level functions
;; ======================================

;; macros from Graham 94 OL

(defun group (source n)
  (if (endp source)
    nil
    (let ((rest (nthcdr n source)))
      (cons (if (consp rest) (subseq source 0 n) source)
	    (group rest n)))))

(defmacro abbrev (short long)
  `(defmacro ,short (&rest args)
     `(,',long ,@args)))

(defmacro abbrevs (&rest names)
  "let here is not really necessary; i use it to show destructive
  effects of sort. without copy-seq the last reference to np gives error."
  (let ((np (group names 2)))
    (setf *abv* (sort (copy-seq np) #'string< :key #'car)) ; beware: sort is destructive
    `(progn 
       ,@(mapcar #'(lambda (pair) `(abbrev ,@pair))
	       np))))

;; shortcuts for common functions. they become macros.

(abbrevs lg load-grammar 
         lm load-model
	 cd ccg-deduce
	 ci ccg-induce
	 p  ccg-deduce
	 pp ccg-induce
	 rank ccg-induce
	 ders cky-show-deduction
	 csd cky-show-deduction
	 csi cky-show-induction
	 probs cky-show-induction
	 csle cky-show-lf-eqv 
	 um update-model
	 st show-training
	 csnf cky-show-normal-forms
	 crs cky-reveal-cell
	 cpp cky-pprint-probs
	 sg  save-grammar
	 savet save-training
	 z z-score-grammar
	 beta beta-normalize-outer
	 ms make-supervision
	 )

(defun ab ()
  (dolist (a *abv*) (format t "~5A ~A~%" (first a) (second a))))
