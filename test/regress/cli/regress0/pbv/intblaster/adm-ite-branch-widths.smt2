; EXPECT: unsat
; ADM for ite(cond, t2, t3) over PBV: emits kappa(t2) = kappa(t3).
; computeKappa(ite(c, x, y)) = computeKappa(x) = kappa(x).
; So pbvsize(ite(c, x, y)) = pbvsize(x) always.
; NOT of this is unsat.
; Tests that the ITE kappa computation follows the then-branch width,
; and that ADM's equal-branch constraint is respected.
(set-logic PBV)
(declare-fun x () PBitVec)
(declare-fun y () PBitVec)
(declare-fun c () Bool)
(assert (not (= (pbvsize (ite c x y)) (pbvsize x))))
(check-sat)
