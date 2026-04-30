; EXPECT: unsat
; Logical right shift by 0 is identity: x >> 0 = x
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (not (= (pbvlshr x (int_to_pbv (pbvsize x) 0)) x)))
(check-sat)
