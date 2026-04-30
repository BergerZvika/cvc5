; EXPECT: sat
; RANGE allows chi(x) and chi(y) to take any values in [0, 2^k).
; Overflow is possible: x + y <_u x when y > 0 and x + y >= 2^k.
; E.g. at k=4: x=15 (all-ones), y=1 -> x+y = 16 mod 16 = 0 < 15 = x.
; This test confirms the RANGE-bounded domain allows wrap-around semantics.
(set-logic PBV)
(declare-fun x () PBitVec)
(declare-fun y () PBitVec)
(assert (= (pbvsize x) (pbvsize y)))
; y > 0
(assert (pbvugt y (int_to_pbv (pbvsize y) 0)))
; x + y wraps below x (overflow)
(assert (pbvult (pbvadd x y) x))
(check-sat)
