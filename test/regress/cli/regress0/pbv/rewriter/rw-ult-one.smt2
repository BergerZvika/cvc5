; EXPECT: unsat
; Rule pbv-ult-one: (pbvult x (int_to_pbv k 1)) => (= x (int_to_pbv k 0))
; So x < 1 iff x = 0; asserting x < 1 and x != 0 should be unsat
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (pbvult x (int_to_pbv (pbvsize x) 1)))
(assert (not (= x (int_to_pbv (pbvsize x) 0))))
(check-sat)
