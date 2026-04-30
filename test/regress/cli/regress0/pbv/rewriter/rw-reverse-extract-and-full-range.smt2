; EXPECT: unsat
; Rule pbv-reverse-extract-and:
;   (pbvand (pextract x j i) (pextract y j i)) => (pextract (pbvand x y) j i)
;
; Edge case: extract covers the full width of the source.
; Here n = pbvsize(x) - 1 so pextract x n 0 is the identity extraction.
; This exercises the boundary where j reaches the top bit index.
; The rule must still fire: the AND distributes through a full-width extract.
(set-logic PBV)
(declare-fun x () PBitVec)
(declare-fun y () PBitVec)
(declare-fun n () Int)
(assert (= (pbvsize x) (pbvsize y)))
(assert (= n (- (pbvsize x) 1)))
(assert (not (= (pbvand (pextract x n 0) (pextract y n 0))
                (pextract (pbvand x y) n 0))))
(check-sat)
