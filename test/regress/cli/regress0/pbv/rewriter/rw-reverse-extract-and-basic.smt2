; EXPECT: unsat
; Rule pbv-reverse-extract-and:
;   (pbvand (pextract x j i) (pextract y j i)) => (pextract (pbvand x y) j i)
;
; Basic positive case: symbolic x and y, concrete indices j=3, i=1.
; The two sources x and y are distinct; the extract bounds are the same on
; both sides.  The rewrite must push the AND inside the extract.
(set-logic PBV)
(declare-fun x () PBitVec)
(declare-fun y () PBitVec)
(assert (= (pbvsize x) (pbvsize y)))
(assert (not (= (pbvand (pextract x 3 1) (pextract y 3 1))
                (pextract (pbvand x y) 3 1))))
(check-sat)
