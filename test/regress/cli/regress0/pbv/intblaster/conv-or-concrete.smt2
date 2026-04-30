; EXPECT: unsat
; CONV(t1 |^B t2) = CONV(t1) + CONV(t2) - piand(k, CONV(t1), CONV(t2))
; 0b1010 | 0b1100 = 0b1110 = 14.  10 | 12 = 14.
; Equivalently: 10 + 12 - 8 = 14 (since 10 & 12 = 8).
(set-logic PBV)
(declare-fun k () Int)
(assert (= k 4))
(assert (not (= (pbvor (int_to_pbv k 10) (int_to_pbv k 12))
               (int_to_pbv k 14))))
(check-sat)
