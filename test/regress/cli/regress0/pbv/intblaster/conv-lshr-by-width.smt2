; EXPECT: unsat
; Logical right shift by the full width gives 0.
; CONV: CONV(t1) div pow2(k) = chi(x) div pow2(k).
; Since 0 <= chi(x) < pow2(k), we have chi(x) div pow2(k) = 0.
; This test FAILS without Range constraints: without 0 <= chi(x) < pow2(k),
; the division chi(x)/pow2(k) cannot be bounded to 0.
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (not (= (pbvlshr x (int_to_pbv (pbvsize x) (pbvsize x)))
               (int_to_pbv (pbvsize x) 0))))
(check-sat)
