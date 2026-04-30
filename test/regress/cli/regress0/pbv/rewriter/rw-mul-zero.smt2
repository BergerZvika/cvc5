; EXPECT: unsat
; Rule pbv-mul-zero: (pbvmul x (int_to_pbv k 0)) => (int_to_pbv k 0)
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (not (= (pbvmul x (int_to_pbv (pbvsize x) 0))
               (int_to_pbv (pbvsize x) 0))))
(check-sat)
