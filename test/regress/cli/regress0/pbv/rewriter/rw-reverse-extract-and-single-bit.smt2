; EXPECT: unsat
; Rule pbv-reverse-extract-and:
;   (pbvand (pextract x j i) (pextract y j i)) => (pextract (pbvand x y) j i)
;
; Edge case: single-bit extraction (j = i = 0).
; The extracted slice has width 1.  The AND of two 1-bit values is still a
; 1-bit value and the rule must push AND inside the single-bit extract.
(set-logic PBV)
(declare-fun x () PBitVec)
(declare-fun y () PBitVec)
(assert (= (pbvsize x) (pbvsize y)))
(assert (not (= (pbvand (pextract x 0 0) (pextract y 0 0))
                (pextract (pbvand x y) 0 0))))
(check-sat)
