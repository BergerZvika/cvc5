; EXPECT: unsat
; Rule pbv-add-zero: (pbvadd x (int_to_pbv k 0)) => x
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (not (= (pbvadd x (int_to_pbv (pbvsize x) 0)) x)))
(check-sat)
