; EXPECT: unsat
; Rule pbv-reverse-extract-and:
;   (pbvand (pextract x j i) (pextract y j i)) => (pextract (pbvand x y) j i)
;
; Positive case: the rule fires twice in one expression.
; We have three sources x, y, z and we AND two independent slice-AND subterms:
;   AND( AND(ext[3:1](x), ext[3:1](y)), AND(ext[3:1](x), ext[3:1](z)) )
; After the rule fires on each inner AND we get:
;   AND( ext[3:1](AND(x,y)), ext[3:1](AND(x,z)) )
; Firing the rule once more gives:
;   ext[3:1]( AND(AND(x,y), AND(x,z)) )
; The test asserts that the original deep form equals the fully pushed form.
(set-logic PBV)
(declare-fun x () PBitVec)
(declare-fun y () PBitVec)
(declare-fun z () PBitVec)
(assert (= (pbvsize x) (pbvsize y)))
(assert (= (pbvsize x) (pbvsize z)))
(assert (not (= (pbvand (pbvand (pextract x 3 1) (pextract y 3 1))
                        (pbvand (pextract x 3 1) (pextract z 3 1)))
                (pextract (pbvand (pbvand x y) (pbvand x z)) 3 1))))
(check-sat)
