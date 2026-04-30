; EXPECT: unsat
; -^B 0 = 0 for any width: (pow2(k) - 0) mod pow2(k) = 0.
; Symbolic width test of NEG encoding.
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (not (= (pbvneg (int_to_pbv (pbvsize x) 0))
               (int_to_pbv (pbvsize x) 0))))
(check-sat)
