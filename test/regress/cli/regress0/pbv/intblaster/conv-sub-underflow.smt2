; EXPECT: unsat
; Subtraction wraps: 0 - 1 = 2^k - 1  (all-ones).
; CONV(0 -^B 1) = (0 - 1) mod 2^k = 2^k - 1.
; At width k=4: 0 - 1 = 15 = all-ones.
; Tests that Range + CONV mod-pow2 encoding handles underflow correctly.
; This test FAILS if Range constraints are omitted: without 0 <= chi < 2^k,
; (0 - 1) mod 2^k cannot be resolved as 2^k - 1 symbolically.
(set-logic PBV)
(declare-fun k () Int)
(assert (= k 4))
(assert (not (= (pbvsub (int_to_pbv k 0) (int_to_pbv k 1))
               (int_to_pbv k 15))))
(check-sat)
