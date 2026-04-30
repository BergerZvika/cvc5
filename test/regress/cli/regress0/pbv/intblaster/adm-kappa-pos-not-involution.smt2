; EXPECT: unsat
; ADM ensures kappa(x) > 0 for every free PBV variable x.
; Consequence: ~~x = x (NOT is an involution) holds at any positive width.
; CONV(~(~x)) = pow2(k) - (pow2(k) - (chi(x)+1) + 1)
;             = pow2(k) - pow2(k) + chi(x) + 1 - 1
;             = chi(x)
; So double negation returns the original value. The negation is unsat.
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (not (= (pbvnot (pbvnot x)) x)))
(check-sat)
