; EXPECT: unsat
; CONV(sign_extend(n, t)) for MSB=0 case: value unchanged.
; 0b0101 (= 5, k=4, MSB=0) sign-extended by 4 bits = 0b00000101 (= 5, k=8).
; Since 5 < pow2(3) = 8, MSB=0 branch: result = CONV(t) = 5.
(set-logic PBV)
(declare-fun k () Int)
(assert (= k 4))
(assert (not (= (psign_extend 4 (int_to_pbv k 5))
               (int_to_pbv (+ k 4) 5))))
(check-sat)
