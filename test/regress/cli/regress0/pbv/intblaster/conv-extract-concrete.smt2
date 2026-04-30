; EXPECT: unsat
; CONV(t[i:j]) = (CONV(t) div pow2(j)) mod pow2(i-j+1)
; Extract bits [3:1] of int_to_pbv 8 0b10110110 (= 182).
; bits [3:1] = 0b011 = 3.
; CONV: (182 div pow2(1)) mod pow2(3) = 91 mod 8 = 3.
(set-logic PBV)
(declare-fun k () Int)
(assert (= k 8))
(assert (not (= (pextract (int_to_pbv k 182) 3 1)
               (int_to_pbv 3 3))))
(check-sat)
