; EXPECT: unsat
; Rule pbv-zero-ule: (pbvule (int_to_pbv k 0) x) => true
; Asserting its negation must be unsat
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (not (pbvule (int_to_pbv (pbvsize x) 0) x)))
(check-sat)
