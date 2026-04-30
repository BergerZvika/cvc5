; EXPECT: unsat
; CONV(t1 <=^B_u t2) = CONV(t1) <= CONV(t2)
; 5 <=_u 5 = true (reflexive). Negation is unsat.
(set-logic PBV)
(declare-fun k () Int)
(assert (>= k 3))
(assert (not (pbvule (int_to_pbv k 5) (int_to_pbv k 5))))
(check-sat)
