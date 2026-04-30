; EXPECT: unsat
; Rule pbv-reverse-extract-and:
;   (pbvand (pextract x j i) (pextract y j i)) => (pextract (pbvand x y) j i)
;
; Parametric-width test: both the source width and the slice bounds are
; symbolic.  We declare i and j as unconstrained integer-sorted variables
; (subject to the implicit well-formedness constraints of pextract: 0 <= i
; <= j < pbvsize(x)).  The rule must hold for all valid (i, j).
;
; We constrain 0 <= i, i <= j, and j < pbvsize(x) to stay within bounds,
; then assert the negation of the rewrite equality.  The result must be unsat
; because the rewrite is universally sound for all valid extractions.
(set-logic PBV)
(declare-fun x () PBitVec)
(declare-fun y () PBitVec)
(declare-fun i () Int)
(declare-fun j () Int)
(assert (= (pbvsize x) (pbvsize y)))
(assert (<= 0 i))
(assert (<= i j))
(assert (< j (pbvsize x)))
(assert (not (= (pbvand (pextract x j i) (pextract y j i))
                (pextract (pbvand x y) j i))))
(check-sat)
