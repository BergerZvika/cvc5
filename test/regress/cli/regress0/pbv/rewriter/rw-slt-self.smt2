; EXPECT: unsat
; Rule pbv-slt-self: (pbvslt x x) => false
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (pbvslt x x))
(check-sat)
