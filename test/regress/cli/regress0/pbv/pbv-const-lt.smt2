; EXPECT: unsat
; Constant comparison: 3 < 3 is false at any width >= 2
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (pbvult (int_to_pbv (pbvsize x) 3) (int_to_pbv (pbvsize x) 3)))
(check-sat)
