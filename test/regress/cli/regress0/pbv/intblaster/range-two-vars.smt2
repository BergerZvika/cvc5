; EXPECT: unsat
; Two independent free PBV variables each get their own RANGE constraint.
; Consequence: ULT is transitive over them.
; If x <_u y and y <_u z then x <_u z.
; CONV: chi(x) < chi(y) AND chi(y) < chi(z) -> chi(x) < chi(z). LIA transitivity.
; NOT of the conclusion together with the premises is unsat.
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
