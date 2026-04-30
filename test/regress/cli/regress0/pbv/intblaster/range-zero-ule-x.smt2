; EXPECT: unsat
; Direct consequence of RANGE lower bound: 0 <= chi(x) for every free var x.
; In PBV: int_to_pbv(pbvsize x, 0) <=_u x  must always hold.
; Negation: NOT (0 <=_u x) is unsat.
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (not (pbvule (int_to_pbv (pbvsize x) 0) x)))
(check-sat)
