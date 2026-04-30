; EXPECT: unsat
; CONV arithmetic right shift for MSB=1 case (sign-extension):
; Algorithm 3: if CONV(t1) >= pow2(k-1): result = pow2(k)-1 - ((pow2(k)-1-t1) div pow2(t2))
; At k=4: 12 = 0b1100 (MSB=1, represents -4 in signed 4-bit).
; 12 ashr 1: allOnes=15, complement=15-12=3, 3 div 2=1, result=15-1=14.
; 14 = 0b1110, which is -2 in 4-bit signed. Correct: -4 >> 1 = -2.
(set-logic PBV)
(declare-fun k () Int)
(assert (= k 4))
(assert (not (= (pbvashr (int_to_pbv k 12) (int_to_pbv k 1))
               (int_to_pbv k 14))))
(check-sat)
