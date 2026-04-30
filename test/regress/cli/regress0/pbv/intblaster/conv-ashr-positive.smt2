; EXPECT: unsat
; CONV(t1 >>_a t2) for MSB=0 case: same as LSHR.
; At k=4: 12 ashr 1 = 6.
; 12 = 0b1100 has MSB=1, so this exercises the MSB=1 (signed) branch:
; ~(~12 >> 1) = ~(3 >> 1) = ~1 = 14.  So 12 ashr 1 = 14? No:
; Let's recalculate: complement = (16-1) - 12 = 3.  3 div 2 = 1.
; signed result = 14 - 1 = 13.  But 12 = -4 in 4-bit signed, -4 >> 1 = -2 = 14.
; Let's use a positive-MSB example: 6 ashr 1 = 3 (MSB=0 branch, same as lshr).
; 6 = 0b0110: MSB=0, so unsignedResult = 6 div 2 = 3. Correct.
(set-logic PBV)
(declare-fun k () Int)
(assert (= k 4))
(assert (not (= (pbvashr (int_to_pbv k 6) (int_to_pbv k 1))
               (int_to_pbv k 3))))
(check-sat)
