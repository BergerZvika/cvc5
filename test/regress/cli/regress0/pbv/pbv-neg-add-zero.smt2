; EXPECT: unsat
; x + (-x) = 0  (mod 2^k)
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (not (= (pbvadd x (pbvneg x)) (int_to_pbv (pbvsize x) 0))))
(check-sat)
