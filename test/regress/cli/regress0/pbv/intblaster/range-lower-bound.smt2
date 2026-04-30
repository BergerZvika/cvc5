; EXPECT: unsat
; RANGE constraint: 0 <= chi(x).
; Without it the solver could assign chi(x) = -1 and satisfy x <_u 0.
; Because RANGE emits "0 <= chi(x)", x <_u 0 (i.e. chi(x) < 0) is unsat.
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (pbvult x (int_to_pbv (pbvsize x) 0)))
(check-sat)
