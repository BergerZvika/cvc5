; EXPECT: unsat
; CONV(~^B t) = pow2(k) - (CONV(t) + 1)
; At k=4: ~3 = 16 - 4 = 12. Assert negation is unsat.
(set-logic PBV)
(declare-fun k () Int)
(assert (= k 4))
(assert (not (= (pbvnot (int_to_pbv k 3))
               (int_to_pbv k 12))))
(check-sat)
