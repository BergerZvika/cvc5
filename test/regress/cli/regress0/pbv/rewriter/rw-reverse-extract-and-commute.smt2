; EXPECT: unsat
; Rule pbv-reverse-extract-and:
;   (pbvand (pextract x j i) (pextract y j i)) => (pextract (pbvand x y) j i)
;
; Argument-order test: the rule must fire regardless of which operand of
; pbvand appears first.  We check that:
;   (a) AND(ext[4:2](x), ext[4:2](y)) = ext[4:2](AND(x, y))    [x first]
;   (b) AND(ext[4:2](y), ext[4:2](x)) = ext[4:2](AND(y, x))    [y first]
; Both equalities must hold simultaneously (we negate the conjunction).
; Note: this does NOT assert commutativity of pbvand itself; it only asserts
; that the rule fires in both syntactic orderings and that the results are
; consistent with their respective push-through forms.
(set-logic PBV)
(declare-fun x () PBitVec)
(declare-fun y () PBitVec)
(assert (= (pbvsize x) (pbvsize y)))
(assert (not (and
  (= (pbvand (pextract x 4 2) (pextract y 4 2))
     (pextract (pbvand x y) 4 2))
  (= (pbvand (pextract y 4 2) (pextract x 4 2))
     (pextract (pbvand y x) 4 2)))))
(check-sat)
