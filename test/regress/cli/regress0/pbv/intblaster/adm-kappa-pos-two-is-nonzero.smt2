; EXPECT: unsat
; ADM ensures kappa(x) > 0. CONV and RANGE produce:
;   0 <= chi(x) < pow2(kappa(x))   [RANGE]
;   kappa(x) > 0                    [ADM]
; Consequence: pbvneg(x) + x = 0 (additive inverse).
; CONV(pbvadd(pbvneg x, x)):
;   pbvneg(x) = (pow2(k) - chi(x)) mod pow2(k)
;   pbvadd(pbvneg x, x) = ((pow2(k) - chi(x)) mod pow2(k) + chi(x)) mod pow2(k)
;                       = pow2(k) mod pow2(k) = 0.
; NOT of this is unsat. Tests that CONV of NEG + ADD gives correct cancellation
; with RANGE ensuring chi(x) is in [0, pow2(k)).
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (not (= (pbvadd (pbvneg x) x) (int_to_pbv (pbvsize x) 0))))
(check-sat)
