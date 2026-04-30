; EXPECT: unsat
; Shift-left overflow: at k=4, 1 << 4 = 0 (shift by full width).
; CONV: (1 * pow2(4)) mod pow2(4) = 16 mod 16 = 0.
; This test exercises the case where shift amount equals the bit-width.
; Without Range constraints, the solver cannot bound the shift amount
; and hence cannot resolve the mod correctly.
(set-logic PBV)
(declare-fun k () Int)
(assert (= k 4))
(assert (not (= (pbvshl (int_to_pbv k 1) (int_to_pbv k 4))
               (int_to_pbv k 0))))
(check-sat)
