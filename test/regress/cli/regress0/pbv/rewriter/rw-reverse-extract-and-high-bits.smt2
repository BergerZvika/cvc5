; EXPECT: unsat
; Rule pbv-reverse-extract-and:
;   (pbvand (pextract x j i) (pextract y j i)) => (pextract (pbvand x y) j i)
;
; Positive case: extract the high half (bits [n:n/2]) of both operands.
; Uses symbolic bound n = pbvsize(x) - 1 and m = n / 2 to exercise a
; parametric slice that is not anchored at bit 0.
(set-logic PBV)
(declare-fun x () PBitVec)
(declare-fun y () PBitVec)
(declare-fun n () Int)
(declare-fun m () Int)
(assert (= (pbvsize x) (pbvsize y)))
(assert (= n (- (pbvsize x) 1)))
(assert (= m (div n 2)))
(assert (not (= (pbvand (pextract x n m) (pextract y n m))
                (pextract (pbvand x y) n m))))
(check-sat)
