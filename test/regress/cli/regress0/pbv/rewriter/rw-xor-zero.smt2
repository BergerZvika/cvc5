; EXPECT: unsat
; Rule pbv-xor-zero: (pbvxor x (int_to_pbv k 0)) => x
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (not (= (pbvxor x (int_to_pbv (pbvsize x) 0)) x)))
(check-sat)
