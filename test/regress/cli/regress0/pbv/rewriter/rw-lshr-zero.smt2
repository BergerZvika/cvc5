; EXPECT: unsat
; Rule pbv-lshr-zero: (pbvlshr (int_to_pbv k 0) x) => (int_to_pbv k 0)
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (not (= (pbvlshr (int_to_pbv (pbvsize x) 0) x)
               (int_to_pbv (pbvsize x) 0))))
(check-sat)
