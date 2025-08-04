; EXPECT: unsat
;; unsupported operator int.pow2
; DISABLE-TESTER: alethe
(set-logic QF_NIA)
(set-info :status unsat)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (<= 1 x))
(assert (distinct 0 (mod (int.pow2 x) 2)))

(check-sat)
