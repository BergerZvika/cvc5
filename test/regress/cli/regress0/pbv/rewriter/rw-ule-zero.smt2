; EXPECT: unsat
; Rule pbv-ule-zero: (pbvule x (int_to_pbv k 0)) => (= x (int_to_pbv k 0))
; So x <= 0 iff x = 0; asserting x <= 0 and x != 0 must be unsat
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (pbvule x (int_to_pbv (pbvsize x) 0)))
(assert (not (= x (int_to_pbv (pbvsize x) 0))))
(check-sat)
