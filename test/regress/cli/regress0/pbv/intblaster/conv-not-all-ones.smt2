; EXPECT: unsat
; ~^B 0 = all-ones: pow2(k) - (0 + 1) = pow2(k) - 1.
; Symbolic width: pbvnot (int_to_pbv k 0) gives all-ones at any width.
; Then (all-ones + 1) should = 0 mod 2^k, so pbvadd(~0, 1) = 0.
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (not (= (pbvadd (pbvnot (int_to_pbv (pbvsize x) 0))
                        (int_to_pbv (pbvsize x) 1))
               (int_to_pbv (pbvsize x) 0))))
(check-sat)
