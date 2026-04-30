; EXPECT: unsat
; t &^B t = t  (idempotence of AND, using piand)
; CONV(t & t) = piand(k, CONV(t), CONV(t)) = CONV(t).
; Symbolic width test.
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (not (= (pbvand x x) x)))
(check-sat)
