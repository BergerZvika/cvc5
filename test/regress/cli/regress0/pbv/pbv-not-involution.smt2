; EXPECT: unsat
; Double negation is identity: ~~x = x
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (not (= (pbvnot (pbvnot x)) x)))
(check-sat)
