; EXPECT: unsat
; pbvadd is commutative: x + y = y + x  (mod 2^k)
(set-logic PBV)
(declare-fun x () PBitVec)
(declare-fun y () PBitVec)
(assert (= (pbvsize x) (pbvsize y)))
(assert (not (= (pbvadd x y) (pbvadd y x))))
(check-sat)
