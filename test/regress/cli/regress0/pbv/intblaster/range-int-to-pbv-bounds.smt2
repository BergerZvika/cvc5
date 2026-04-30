; EXPECT: unsat
; CONV(int_to_pbv(k, v)) = v mod pow2(k).
; For v = pow2(k), this gives 0.
; So int_to_pbv(k, pow2(k)) = int_to_pbv(k, 0) for all k >= 1.
; Asserting they are not equal is unsat.
; This exercises that CONV wraps via mod, keeping results in [0, 2^k).
(set-logic PBV)
(declare-fun k () Int)
(assert (>= k 1))
; int_to_pbv(k, 0) = int_to_pbv(k, 0) trivially, but:
; int_to_pbv(k, 256) at k=8 gives 256 mod 256 = 0 = int_to_pbv(8, 0).
; More generally: int_to_pbv(k, 0) = int_to_pbv(k, 0): tautology.
; Test: 255 mod 256 = 255, 256 mod 256 = 0. So at k=8 they differ.
; We test: int_to_pbv(k, 0) is always the zero element (ult everything except itself).
(assert (pbvult (int_to_pbv k 1) (int_to_pbv k 0)))
(check-sat)
