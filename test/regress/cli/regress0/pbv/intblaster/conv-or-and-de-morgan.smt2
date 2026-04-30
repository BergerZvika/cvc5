; EXPECT: unsat
; De Morgan's law: ~(x | y) = ~x & ~y
; Tests interaction of OR and AND CONV encodings with NOT.
; Symbolic width: works for any k > 0.
(set-logic PBV)
(declare-fun x () PBitVec)
(declare-fun y () PBitVec)
(assert (= (pbvsize x) (pbvsize y)))
(assert (not (= (pbvnot (pbvor x y))
               (pbvand (pbvnot x) (pbvnot y)))))
(check-sat)
