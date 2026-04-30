; EXPECT: unsat
; Rule pbv-ule-self: (pbvule x x) => true
; Asserting its negation must be unsat
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (not (pbvule x x)))
(check-sat)
