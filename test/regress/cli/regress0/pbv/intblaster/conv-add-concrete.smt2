; EXPECT: unsat
; CONV(t1 +^B t2) = (CONV(t1) + CONV(t2)) mod pow2(kappa(t1))
; Concrete check: 3 + 5 = 8 at any width (mod 2^k means this holds for k >= 4)
; We assert 3+5 != 8 which must be unsat.
(set-logic PBV)
(declare-fun k () Int)
(assert (>= k 4))
(assert (not (= (pbvadd (int_to_pbv k 3) (int_to_pbv k 5))
               (int_to_pbv k 8))))
(check-sat)
