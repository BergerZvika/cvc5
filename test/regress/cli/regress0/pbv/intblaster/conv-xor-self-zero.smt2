; EXPECT: unsat
; x xor x = 0: CONV(t) + CONV(t) - 2*piand(k,CONV(t),CONV(t))
;            = 2*CONV(t) - 2*CONV(t) = 0.
; Tests XOR encoding with symbolic width.
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (not (= (pbvxor x x) (int_to_pbv (pbvsize x) 0))))
(check-sat)
