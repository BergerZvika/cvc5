; EXPECT: unsat
; Rule pbv-or-zero: (pbvor x (int_to_pbv k 0)) => x
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (not (= (pbvor x (int_to_pbv (pbvsize x) 0)) x)))
(check-sat)
