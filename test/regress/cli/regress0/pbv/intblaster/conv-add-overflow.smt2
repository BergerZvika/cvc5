; EXPECT: unsat
; CONV(t1 +^B t2) wraps modulo 2^kappa(t1).
; For a 4-bit-wide value: (int_to_pbv k 15) + (int_to_pbv k 1) = int_to_pbv k 0
; because (15 + 1) mod 16 = 0.
; This test FAILS if Range constraints are omitted (the solver would not know
; that CONV(x) < 2^k and hence couldn't establish overflow semantics).
(set-logic PBV)
(declare-fun k () Int)
(assert (= k 4))
(assert (not (= (pbvadd (int_to_pbv k 15) (int_to_pbv k 1))
               (int_to_pbv k 0))))
(check-sat)
