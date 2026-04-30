; EXPECT: sat
; There exist x,y of same width with x < y
(set-logic PBV)
(declare-fun x () PBitVec)
(declare-fun y () PBitVec)
(assert (= (pbvsize x) (pbvsize y)))
(assert (pbvult x y))
(check-sat)
