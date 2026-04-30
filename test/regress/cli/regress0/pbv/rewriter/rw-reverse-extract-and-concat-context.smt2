; EXPECT: unsat
; Rule pbv-reverse-extract-and:
;   (pbvand (pextract x j i) (pextract y j i)) => (pextract (pbvand x y) j i)
;
; Context test: the rewritten term appears as an argument to pconcat.
; We verify:
;   pconcat( AND(ext[5:3](x), ext[5:3](y)),  AND(ext[2:0](x), ext[2:0](y)) )
;   = pconcat( ext[5:3](AND(x,y)),  ext[2:0](AND(x,y)) )
;
; The rule fires independently on each conjunct.  The outer pconcat then
; groups them.  This tests that no context-sensitivity breaks the rule.
(set-logic PBV)
(declare-fun x () PBitVec)
(declare-fun y () PBitVec)
(assert (= (pbvsize x) (pbvsize y)))
(assert (not (= (pconcat (pbvand (pextract x 5 3) (pextract y 5 3))
                         (pbvand (pextract x 2 0) (pextract y 2 0)))
                (pconcat (pextract (pbvand x y) 5 3)
                         (pextract (pbvand x y) 2 0)))))
(check-sat)
