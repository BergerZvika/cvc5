; EXPECT: unsat
; CONV(t1 <<^B t2) = (CONV(t1) * pow2(CONV(t2))) mod pow2(kappa(t1))
; At k=4: 3 << 2 = 12.  3 * 4 = 12.  12 mod 16 = 12.
(set-logic PBV)
(declare-fun k () Int)
(assert (= k 4))
(assert (not (= (pbvshl (int_to_pbv k 3) (int_to_pbv k 2))
               (int_to_pbv k 12))))
(check-sat)
