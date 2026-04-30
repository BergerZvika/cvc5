; EXPECT: unsat
; CONV(t1 <^B_s t2) = utsSym(k, CONV(t1)) < utsSym(k, CONV(t2))
; utsSym(k, x) = x - ite(x < pow2(k-1), 0, pow2(k))
; For MSB=0 values (positive in signed): utsSym = CONV(t).
; 3 <_s 7 (both positive at k=4): 3 < 7. Negation is unsat.
(set-logic PBV)
(declare-fun k () Int)
(assert (= k 4))
(assert (not (pbvslt (int_to_pbv k 3) (int_to_pbv k 7))))
(check-sat)
