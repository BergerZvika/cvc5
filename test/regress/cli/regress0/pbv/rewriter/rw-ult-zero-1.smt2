; EXPECT: unsat
; Rule pbv-ult-zero-1: (pbvult (int_to_pbv k 0) x) => (not (= x (int_to_pbv k 0)))
; So 0 < x iff x != 0; asserting 0 < x and x = 0 must be unsat
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (pbvult (int_to_pbv (pbvsize x) 0) x))
(assert (= x (int_to_pbv (pbvsize x) 0)))
(check-sat)
