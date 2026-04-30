; EXPECT: unsat
; ADM for pbvadd(x, y): emits kappa(x) = kappa(y) (equal-width constraint).
; A direct testable consequence: computeKappa(pbvadd x y) = computeKappa(x).
; In other words: pbvsize(pbvadd x y) = pbvsize(x).
; CONV(pbvsize(pbvadd x y)) = computeKappa(pbvadd x y) = kappa(x).
; CONV(pbvsize(x)) = kappa(x). Equal -> NOT is unsat.
; This exercises the computeKappa rule for binary ops: kappa = kappa(first child).
(set-logic PBV)
(declare-fun x () PBitVec)
(declare-fun y () PBitVec)
(assert (not (= (pbvsize (pbvadd x y)) (pbvsize x))))
(check-sat)
