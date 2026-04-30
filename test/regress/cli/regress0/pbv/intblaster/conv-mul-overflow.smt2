; EXPECT: unsat
; Multiplication overflow: at k=4, 6 * 4 = 24, and 24 mod 16 = 8.
; CONV(6 *^4 4) = 8.
; Tests mod-pow2 wrapping in MUL translation.
(set-logic PBV)
(declare-fun k () Int)
(assert (= k 4))
(assert (not (= (pbvmul (int_to_pbv k 6) (int_to_pbv k 4))
               (int_to_pbv k 8))))
(check-sat)
