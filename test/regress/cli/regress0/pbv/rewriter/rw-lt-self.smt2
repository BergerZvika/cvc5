; EXPECT: unsat
; Rule pbv-lt-self: (pbvult x x) => false
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (pbvult x x))
(check-sat)
