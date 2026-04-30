; EXPECT: unsat
; pbvult is irreflexive: x < x is false
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (pbvult x x))
(check-sat)
