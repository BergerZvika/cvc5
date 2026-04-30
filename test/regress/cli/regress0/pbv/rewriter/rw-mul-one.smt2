; EXPECT: unsat
; Rule pbv-mul-one: (pbvmul x (int_to_pbv k 1)) => x
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (not (= (pbvmul x (int_to_pbv (pbvsize x) 1)) x)))
(check-sat)
