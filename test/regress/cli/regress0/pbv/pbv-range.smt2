; EXPECT: unsat
; PBV values are non-negative; x < 0 is impossible
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (pbvult x (int_to_pbv (pbvsize x) 0)))
(check-sat)
