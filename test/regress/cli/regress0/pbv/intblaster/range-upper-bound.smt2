; EXPECT: unsat
; RANGE upper bound: chi(x) < pow2(kappa(x)).
; Consequence: (chi(x) - 0) mod pow2(kappa(x)) = chi(x)  [since chi(x) is already in range].
; So x - 0 = x must always hold.
; Without RANGE upper bound: chi(x) could be >= pow2(k), making
;   (chi(x) - 0) mod pow2(k)  !=  chi(x).
; CONV(pbvsub x (int_to_pbv k 0)) = (chi(x) - 0) mod pow2(kappa(x)) = chi(x).
; CONV(x) = chi(x).  Equality holds. NOT of this is unsat.
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (not (= (pbvsub x (int_to_pbv (pbvsize x) 0)) x)))
(check-sat)
