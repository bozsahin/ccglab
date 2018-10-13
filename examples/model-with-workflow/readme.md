There are two ways to replicate the experiment.

I. Doing it using the test suite provided:
  After getting into ccglab, do
  1. (load "testsuite.lisp") 
  2. (test-noqnoc)

II. Doing it manually, which is better for understanding the modeling workflow.

1. Created the text file g1.ccg. It is the grammar we wish to train.
2. Created the text file g1.supervision. It is the data we wish to train on.
3. In ccglab, did (load-grammar "g1" :maker 'sbcl). 
    It created the g1.ded file from g1.ccg. 
4. In ccglab, did (make-supervision "g1" :maker 'sbcl).
    It created the g1.sup file from g1.supervision.
5. Copied g1.ded to g1.ind to prepare for training.
6. Initialized the parameters in g1.ind. I kept them as 1.0.
7. In ccglab, did (update-model "g1" 10 1.0 1.0 :load t).
    It iterates over g1.sup 10 times, to update the parameters in g1.ind.
    1.0 and 1.0 are learning parameters alpha0 and c. NB. the manual.
    Did (show-training) to see the difference.
8. In ccglab, did (save-training "new-g1.ind").
    It saves the trained grammar as new-g1.ind. 
9. In ccglab, do (load-model "new-g1") to start using the trained grammar.
10. One way is (rank '(john knows mary loves John))
    It will show the most likely LF for the example, among other things.
11. The '.out' file shows the details above in Lispese. It was started
    in ccglab as (dribble "g1.trained...out") before i ran the experiment.
    I stopped dribbling after step 9. I zscored the new grammar for comparison.

(dribble "fn") is Lisp's way of saving all the top commands and their output in a file called fn.
    
(dribble) turns it off.

enjoy.
-cem
