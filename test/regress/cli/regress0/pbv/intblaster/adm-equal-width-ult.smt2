; EXPECT: unsat
; ADM for pbvult(x, y): emits kappa(x) = kappa(y).
; Direct consequence: pbvsize(pbvult x y) gives Bool, but the pbvult translation
; uses kappa(x) as the width. Since kappa(pbvult) is based on kappa(x) = kappa(y),
; the resulting comparison is well-typed.
; Testable: pbvult is irreflexive — x <_u x is always false.
; CONV(pbvult x x) = chi(x) < chi(x) = false. NOT(false) = true -> NOT is UNSAT.
; Also tests that ADM's equal-width constraint makes comparisons work correctly.
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (pbvult x x))
(check-sat)
