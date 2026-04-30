; EXPECT: unsat
; Rule pbv-ugt-eliminate: (pbvugt x y) => (pbvult y x)
; pbvugt x x reduces to pbvult x x => false, so asserting (pbvugt x x) is unsat
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (pbvugt x x))
(check-sat)
