; EXPECT: unsat
; CONV(t1 >>_l t2) = CONV(t1) div pow2(CONV(t2))
; At k=4: 12 lshr 2 = 3.  12 div 4 = 3.
(set-logic PBV)
(declare-fun k () Int)
(assert (= k 4))
(assert (not (= (pbvlshr (int_to_pbv k 12) (int_to_pbv k 2))
               (int_to_pbv k 3))))
(check-sat)
