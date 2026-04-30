; EXPECT: unsat
; Rule pbv-shl-by-const-0: (pbvshl x (int_to_pbv k 0)) => x
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (not (= (pbvshl x (int_to_pbv (pbvsize x) 0)) x)))
(check-sat)
