; EXPECT: unsat
; CONV(t1 <^B_u t2) = CONV(t1) < CONV(t2)  (direct integer LT)
; 3 <_u 7 = true. Negation is unsat.
(set-logic PBV)
(declare-fun k () Int)
(assert (>= k 3))
(assert (not (pbvult (int_to_pbv k 3) (int_to_pbv k 7))))
(check-sat)
