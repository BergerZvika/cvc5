; EXPECT: unsat
; Rule pbv-neg-sub: (pbvneg (pbvsub x y)) => (pbvsub y x)
(set-logic PBV)
(declare-fun x () PBitVec)
(declare-fun y () PBitVec)
(assert (= (pbvsize x) (pbvsize y)))
(assert (not (= (pbvneg (pbvsub x y)) (pbvsub y x))))
(check-sat)
