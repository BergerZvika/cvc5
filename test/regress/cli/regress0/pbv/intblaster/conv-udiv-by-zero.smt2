; EXPECT: unsat
; CONV(t1 /^B 0) = pow2(k) - 1  (all-ones, SMT-LIB semantics for BV division by zero)
; Algorithm 3: ite(CONV(t2)=0, pow2(k)-1, t1 div t2)
; At k=4: udiv(7, 0) = 15 = all-ones.
; This verifies the zero-divisor branch of the ITE encoding.
(set-logic PBV)
(declare-fun k () Int)
(assert (= k 4))
(assert (not (= (pbvudiv (int_to_pbv k 7) (int_to_pbv k 0))
               (int_to_pbv k 15))))
(check-sat)
