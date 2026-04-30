; EXPECT: unsat
; x + 0 = x  (additive identity)
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (not (= (pbvadd x (int_to_pbv (pbvsize x) 0)) x)))
(check-sat)
