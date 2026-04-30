; EXPECT: unsat
; Rule pbv-neg-idemp: (pbvneg (pbvneg x)) => x
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (not (= (pbvneg (pbvneg x)) x)))
(check-sat)
