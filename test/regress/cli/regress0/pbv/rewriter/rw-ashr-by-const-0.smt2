; EXPECT: unsat
; Rule pbv-ashr-by-const-0: (pbvashr x (int_to_pbv k 0)) => x
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (not (= (pbvashr x (int_to_pbv (pbvsize x) 0)) x)))
(check-sat)
