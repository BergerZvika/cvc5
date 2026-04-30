; EXPECT: unsat
; pbvult is transitive: x < y /\ y < z => x < z
(set-logic PBV)
(declare-fun x () PBitVec)
(declare-fun y () PBitVec)
(declare-fun z () PBitVec)
(assert (= (pbvsize x) (pbvsize y)))
(assert (= (pbvsize y) (pbvsize z)))
(assert (pbvult x y))
(assert (pbvult y z))
(assert (not (pbvult x z)))
(check-sat)
