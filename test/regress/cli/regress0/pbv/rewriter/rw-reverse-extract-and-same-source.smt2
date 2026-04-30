; EXPECT: unsat
; Rule pbv-reverse-extract-and:
;   (pbvand (pextract x j i) (pextract y j i)) => (pextract (pbvand x y) j i)
;
; Positive case: x and y are the same term (x AND x = x).
; The rule fires because both extracts share the same i and j; the resulting
; equality reduces further by idempotency of AND (pbvand x x = x) together
; with the rewrite, but the test only asks that the two sides of the equation
; before that extra step are equal.  Even without idempotency this identity
; holds: AND(extract[j:i](x), extract[j:i](x)) = extract[j:i](AND(x,x)).
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (not (= (pbvand (pextract x 5 2) (pextract x 5 2))
                (pextract (pbvand x x) 5 2))))
(check-sat)
