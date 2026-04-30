; EXPECT: unsat
; ADM for pbvsub(x, y): emits kappa(x) = kappa(y).
; CONV(x - y) = (chi(x) - chi(y)) mod pow2(kappa(x)).
; Consequence: x - x = 0 for any x (since (chi - chi) mod pow2(k) = 0).
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (not (= (pbvsub x x) (int_to_pbv (pbvsize x) 0))))
(check-sat)
