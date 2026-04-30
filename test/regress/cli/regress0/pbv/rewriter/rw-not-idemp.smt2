; EXPECT: unsat
; Rule pbv-not-idemp: (pbvnot (pbvnot x)) => x
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (not (= (pbvnot (pbvnot x)) x)))
(check-sat)
