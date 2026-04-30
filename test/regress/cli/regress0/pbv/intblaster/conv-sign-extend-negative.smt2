; EXPECT: unsat
; CONV(sign_extend(n, t)) for MSB=1 case:
;   result = (pow2(n) - 1) * pow2(k) + CONV(t)
; 0b1101 (= 13, k=4, MSB=1, represents -3) sign-extended by 4 bits:
;   = (pow2(4) - 1) * pow2(4) + 13 = 15 * 16 + 13 = 240 + 13 = 253.
; 253 = 0b11111101, which is -3 in 8-bit signed. Correct.
(set-logic PBV)
(declare-fun k () Int)
(assert (= k 4))
(assert (not (= (psign_extend 4 (int_to_pbv k 13))
               (int_to_pbv (+ k 4) 253))))
(check-sat)
