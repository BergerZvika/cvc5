; EXPECT: unsat
; Rule pbv-lshr-by-const-0: (pbvlshr x (int_to_pbv k 0)) => x
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (not (= (pbvlshr x (int_to_pbv (pbvsize x) 0)) x)))
(check-sat)
