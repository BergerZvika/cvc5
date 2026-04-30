; EXPECT: unsat
; Rule pbv-uge-eliminate: (pbvuge x y) => (pbvule y x)
; pbvuge x x -> pbvule x x -> true; negation must be unsat
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (not (pbvuge x x)))
(check-sat)
