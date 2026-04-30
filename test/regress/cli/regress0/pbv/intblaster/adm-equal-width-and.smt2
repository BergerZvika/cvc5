; EXPECT: unsat
; ADM for pbvand(x, y): emits kappa(x) = kappa(y).
; Direct consequence via computeKappa: pbvsize(pbvand x y) = pbvsize(x).
; Also: pbvand is commutative — this is a semantic property.
; CONV(pbvand x y) = PIAND(kappa(x), chi(x), chi(y)).
; CONV(pbvand y x) = PIAND(kappa(y), chi(y), chi(x)).
; With ADM kappa(x) = kappa(y) and PIAND commutativity: equal.
; Test: pbvsize of the AND result equals pbvsize of first operand.
(set-logic PBV)
(declare-fun x () PBitVec)
(declare-fun y () PBitVec)
(assert (not (= (pbvsize (pbvand x y)) (pbvsize x))))
(check-sat)
