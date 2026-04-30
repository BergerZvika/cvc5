; EXPECT: unsat
; CONV(t1 /^B t2) = ite(CONV(t2)=0, pow2(k)-1, CONV(t1) div CONV(t2))
; 10 udiv 3 = 3 (integer division). Assert negation is unsat.
(set-logic PBV)
(declare-fun k () Int)
(assert (>= k 4))
(assert (not (= (pbvudiv (int_to_pbv k 10) (int_to_pbv k 3))
               (int_to_pbv k 3))))
(check-sat)
