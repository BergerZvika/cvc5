; EXPECT: unsat
; CONV(t1 xor t2) = CONV(t1) + CONV(t2) - 2*piand(k, CONV(t1), CONV(t2))
; 0b1010 xor 0b1100 = 0b0110 = 6.  10 xor 12 = 6.
; Equivalently: 10 + 12 - 2*8 = 6.
(set-logic PBV)
(declare-fun k () Int)
(assert (= k 4))
(assert (not (= (pbvxor (int_to_pbv k 10) (int_to_pbv k 12))
               (int_to_pbv k 6))))
(check-sat)
