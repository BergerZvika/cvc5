; EXPECT: unsat
; Rule pbv-urem-one: (pbvurem x (int_to_pbv k 1)) => (int_to_pbv k 0)
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (not (= (pbvurem x (int_to_pbv (pbvsize x) 1))
               (int_to_pbv (pbvsize x) 0))))
(check-sat)
