; EXPECT: unsat
; CONV(t1 %^B t2) = ite(CONV(t2)=0, CONV(t1), CONV(t1) mod CONV(t2))
; 10 urem 3 = 1. Assert negation is unsat.
(set-logic PBV)
(declare-fun k () Int)
(assert (>= k 4))
(assert (not (= (pbvurem (int_to_pbv k 10) (int_to_pbv k 3))
               (int_to_pbv k 1))))
(check-sat)
