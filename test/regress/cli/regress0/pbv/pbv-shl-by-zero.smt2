; EXPECT: unsat
; Shifting by 0 is identity: x << 0 = x
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (not (= (pbvshl x (int_to_pbv (pbvsize x) 0)) x)))
(check-sat)
