; EXPECT: unsat
; Rule pbv-concat-extract-merge:
;   (pconcat (pextract s k j1) (pextract s j i)) => (pextract s k i)
;   when j1 = j + 1 (adjacent slices from the same source)
; Here: concat bits [3:2] and [1:0] of s gives back bits [3:0] of s
(set-logic PBV)
(declare-fun s () PBitVec)
(assert (not (= (pconcat (pextract s 3 2) (pextract s 1 0))
               (pextract s 3 0))))
(check-sat)
