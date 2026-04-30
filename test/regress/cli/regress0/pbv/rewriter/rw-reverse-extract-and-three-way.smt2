; EXPECT: unsat
; Rule pbv-reverse-extract-and:
;   (pbvand (pextract x j i) (pextract y j i)) => (pextract (pbvand x y) j i)
;
; Three-operand AND test.  pbvand is n-ary (children = "2:" in kinds.toml).
; We check whether the rule composes correctly when AND has three operands by
; reducing it to a chain of binary applications:
;   AND(ext[4:1](x), AND(ext[4:1](y), ext[4:1](z)))
;   = ext[4:1](AND(x, AND(y, z)))
;
; The inner AND(ext(y), ext(z)) fires first, yielding ext(AND(y,z)).
; The outer AND(ext(x), ext(AND(y,z))) then fires because the second operand
; is now a pextract of the same bounds.
(set-logic PBV)
(declare-fun x () PBitVec)
(declare-fun y () PBitVec)
(declare-fun z () PBitVec)
(assert (= (pbvsize x) (pbvsize y)))
(assert (= (pbvsize x) (pbvsize z)))
(assert (not (= (pbvand (pextract x 4 1) (pbvand (pextract y 4 1) (pextract z 4 1)))
                (pextract (pbvand x (pbvand y z)) 4 1))))
(check-sat)
