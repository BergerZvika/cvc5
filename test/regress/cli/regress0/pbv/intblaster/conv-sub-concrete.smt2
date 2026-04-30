; EXPECT: unsat
; CONV(t1 -^B t2) = (CONV(t1) - CONV(t2)) mod pow2(kappa(t1))
; 10 - 3 = 7 at any width >= 4. Assert negation must be unsat.
(set-logic PBV)
(declare-fun k () Int)
(assert (>= k 4))
(assert (not (= (pbvsub (int_to_pbv k 10) (int_to_pbv k 3))
               (int_to_pbv k 7))))
(check-sat)
