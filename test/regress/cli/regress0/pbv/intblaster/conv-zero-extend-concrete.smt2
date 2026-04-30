; EXPECT: unsat
; CONV(zero_extend(n, t)) = CONV(t)  (integer value unchanged, just wider sort)
; Extending 0b0101 (= 5, k=4) by 4 bits gives 0b00000101 (= 5, k=8).
; The integer value is identical, so both sides = int_to_pbv 8 5.
(set-logic PBV)
(declare-fun k () Int)
(assert (= k 4))
(assert (not (= (pzero_extend 4 (int_to_pbv k 5))
               (int_to_pbv (+ k 4) 5))))
(check-sat)
