; EXPECT: unsat
; Arithmetic right shift by 0 is identity: x >>_a 0 = x.
; Both MSB branches give t1 div pow2(0) = t1 div 1 = t1.
; Symbolic width test.
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (not (= (pbvashr x (int_to_pbv (pbvsize x) 0)) x)))
(check-sat)
