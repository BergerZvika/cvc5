; EXPECT: unsat
; CONV(t1 *^B t2) = (CONV(t1) * CONV(t2)) mod pow2(kappa(t1))
; 3 * 5 = 15 at any width >= 4. Assert negation is unsat.
(set-logic PBV)
(declare-fun k () Int)
(assert (>= k 4))
(assert (not (= (pbvmul (int_to_pbv k 3) (int_to_pbv k 5))
               (int_to_pbv k 15))))
(check-sat)
