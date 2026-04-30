; EXPECT: unsat
; RANGE ensures chi(x) is a valid integer, making ULE total.
; For any x and y with the same width: x <=_u y OR y <=_u x (totality of <=_u).
; CONV: chi(x) <= chi(y) OR chi(y) <= chi(x).
; From LIA: for any two integers, one is <= the other. -> always true.
; NOT of this is unsat.
; This exercises that ULE's CONV (<=) is total over the range-constrained integers.
(set-logic PBV)
(declare-fun x () PBitVec)
(declare-fun y () PBitVec)
(assert (= (pbvsize x) (pbvsize y)))
(assert (not (or (pbvule x y) (pbvule y x))))
(check-sat)
