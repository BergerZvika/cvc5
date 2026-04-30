; EXPECT: unsat
; Rule pbv-udiv-one: (pbvudiv x (int_to_pbv k 1)) => x
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (not (= (pbvudiv x (int_to_pbv (pbvsize x) 1)) x)))
(check-sat)
