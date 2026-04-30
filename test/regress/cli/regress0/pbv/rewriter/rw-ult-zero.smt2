; EXPECT: unsat
; Rule pbv-ult-zero-2: (pbvult x (int_to_pbv k 0)) => false
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (pbvult x (int_to_pbv (pbvsize x) 0)))
(check-sat)
