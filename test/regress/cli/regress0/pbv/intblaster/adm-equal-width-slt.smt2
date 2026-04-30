; EXPECT: unsat
; ADM for pbvslt(x, y): emits kappa(x) = kappa(y).
; utsSym uses pow2(kappa-1). With kappa(x) = kappa(y), the signed conversion
; uses the same threshold for both, making the comparison well-defined.
; Consequence: x <_s x is always false (irreflexivity of signed less-than).
; CONV: uts(k, chi(x)) < uts(k, chi(x)) is always false.
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (pbvslt x x))
(check-sat)
