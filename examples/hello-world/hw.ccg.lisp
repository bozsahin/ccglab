(DEFPARAMETER *CCG-GRAMMAR*
  '(((KEY 1) (PHON EVERY) (MORPH DET)
     (SYN
      ((((BCAT S) (FEATS NIL)) (DIR FS) (MODAL ALL)
        (((BCAT S) (FEATS NIL)) (DIR BS) (MODAL ALL) ((BCAT NP) (FEATS NIL))))
       (DIR FS) (MODAL STAR) ((BCAT N) (FEATS NIL))))
     (SEM (LAM P (LAM Q (LAM X (("EVERY" (P X)) (Q X)))))) (PARAM 1.0))
    ((KEY 2) (PHON THE) (MORPH DET)
     (SYN
      (((BCAT NP) (FEATS NIL)) (DIR FS) (MODAL STAR) ((BCAT N) (FEATS NIL))))
     (SEM (LAM X ("DEF" X))) (PARAM 1.0))
    ((KEY 3) (PHON CAT) (MORPH N) (SYN ((BCAT N) (FEATS NIL)))
     (SEM (LAM Y ("CAT" Y))) (PARAM 1.0))
    ((KEY 4) (PHON SAT) (MORPH V)
     (SYN
      (((BCAT S) (FEATS NIL)) (DIR BS) (MODAL ALL) ((BCAT NP) (FEATS NIL))))
     (SEM (LAM Z ("SAT" Z))) (PARAM 1.0))
    ((KEY 5) (PHON ON) (MORPH P)
     (SYN
      (((((BCAT S) (FEATS NIL)) (DIR BS) (MODAL ALL) ((BCAT NP) (FEATS NIL)))
        (DIR BS) (MODAL ALL)
        (((BCAT S) (FEATS NIL)) (DIR BS) (MODAL ALL) ((BCAT NP) (FEATS NIL))))
       (DIR FS) (MODAL ALL) ((BCAT NP) (FEATS NIL))))
     (SEM (LAM X (LAM P (LAM Y (("AND" (P Y)) (("ON" X) Y)))))) (PARAM 1.0))
    ((KEY 6) (PHON MAT) (MORPH N) (SYN ((BCAT N) (FEATS NIL)))
     (SEM (LAM Y ("MAT" Y))) (PARAM 1.0))))