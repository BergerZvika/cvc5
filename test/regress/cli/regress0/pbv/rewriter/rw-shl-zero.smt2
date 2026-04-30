; EXPECT: unsat
; Rule pbv-shl-zero: (pbvshl (int_to_pbv k 0) x) => (int_to_pbv k 0)
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (not (= (pbvshl (int_to_pbv (pbvsize x) 0) x)
               (int_to_pbv (pbvsize x) 0))))
(check-sat)
