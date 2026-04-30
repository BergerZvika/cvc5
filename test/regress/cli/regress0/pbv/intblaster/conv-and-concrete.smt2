; EXPECT: unsat
; CONV(t1 &^B t2) = piand(kappa(t1), CONV(t1), CONV(t2))
; 0b1010 & 0b1100 = 0b1000 = 8 at k=4.
; 10 & 12 = 8.
(set-logic PBV)
(declare-fun k () Int)
(assert (= k 4))
(assert (not (= (pbvand (int_to_pbv k 10) (int_to_pbv k 12))
               (int_to_pbv k 8))))
(check-sat)
