; EXPECT: unsat
; CONV(t1 %^B 0) = CONV(t1)  (SMT-LIB BV urem-by-zero semantics)
; Algorithm 3: ite(CONV(t2)=0, CONV(t1), CONV(t1) mod CONV(t2))
; t1 urem 0 = t1 for any t1. Both sides go through int_to_pbv so they agree.
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (not (= (pbvurem x (int_to_pbv (pbvsize x) 0)) x)))
(check-sat)
