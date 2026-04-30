; EXPECT: sat
; The RANGE upper bound is tight: chi(x) = pow2(k)-1 (all-ones) is allowed.
; x = all-ones is satisfiable.
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (= x (pbvnot (int_to_pbv (pbvsize x) 0))))
(check-sat)
