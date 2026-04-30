; EXPECT: unsat
; CONV(-^B t) = (pow2(k) - CONV(t)) mod pow2(k)
; -3 at k=4: (16 - 3) mod 16 = 13.
; At k=4: pbvneg (int_to_pbv 4 3) = int_to_pbv 4 13.
(set-logic PBV)
(declare-fun k () Int)
(assert (= k 4))
(assert (not (= (pbvneg (int_to_pbv k 3))
               (int_to_pbv k 13))))
(check-sat)
