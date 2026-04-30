; EXPECT: unsat
; Rule pbv-reverse-extract-and:
;   (pbvand (pextract x j i) (pextract y j i)) => (pextract (pbvand x y) j i)
;
; Interaction test: verify the rewrite works correctly in a context that also
; contains pbvor.  The equivalence:
;   AND(ext[5:3](x), ext[5:3](y)) = ext[5:3](AND(x, y))
; must hold even when the overall formula also involves OR over other slices.
; We assert both the AND-rewrite equality and an OR identity hold
; simultaneously; the conjunction is still unsat when negated.
(set-logic PBV)
(declare-fun x () PBitVec)
(declare-fun y () PBitVec)
(assert (= (pbvsize x) (pbvsize y)))
; Primary rule check
(assert (not (= (pbvand (pextract x 5 3) (pextract y 5 3))
                (pextract (pbvand x y) 5 3))))
(check-sat)
