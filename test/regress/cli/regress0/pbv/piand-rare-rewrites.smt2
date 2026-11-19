; COMMAND-LINE: --piand-rare-rewrites
; EXPECT: unsat
; piand is 0 at k <= 0. The RARE rule piand-idem (pbv/rewrites-piand) rewrites
; piand(k,x,x) to ite(k > 0, x mod 2^k, 0); the hand-written rule in the arith
; rewriter drops the guard and makes this sat.
(set-logic ALL)
(declare-const k Int)
(declare-const x Int)
(declare-const y Int)
(assert (< k 0))
(assert (= x 5))
(assert (or (= (piand k x x) 5)
            (not (= (piand k x (piand k x y)) (piand k x y)))))
(check-sat)
