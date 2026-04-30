; EXPECT: unsat
; CONV(t1 ○ t2) = CONV(t1) * pow2(kappa(t2)) + CONV(t2)
; Concatenating 0b1010 (k1=4) with 0b0011 (k2=4):
; result = 0b10100011 = 163.
; CONV: 10 * pow2(4) + 3 = 10*16 + 3 = 163.
(set-logic PBV)
(declare-fun k1 () Int)
(declare-fun k2 () Int)
(assert (= k1 4))
(assert (= k2 4))
(assert (not (= (pconcat (int_to_pbv k1 10) (int_to_pbv k2 3))
               (int_to_pbv (+ k1 k2) 163))))
(check-sat)
