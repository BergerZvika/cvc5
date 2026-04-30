; EXPECT: unsat
; Rule pbv-reverse-extract-and:
;   (pbvand (pextract x j i) (pextract y j i)) => (pextract (pbvand x y) j i)
;
; Concrete small-width regression: use width-4 constants to ground the rule.
; x = int_to_pbv 4 v_x, y = int_to_pbv 4 v_y where v_x, v_y are symbolic
; integers in [0,15].  Extract bits [2:1] (a 2-bit slice) from both, AND
; them, and verify the result equals the same slice of AND(x,y).
;
; This also exercises the interaction of int_to_pbv with pextract and pbvand.
(set-logic PBV)
(declare-fun vx () Int)
(declare-fun vy () Int)
(assert (<= 0 vx)) (assert (< vx 16))
(assert (<= 0 vy)) (assert (< vy 16))
(define-fun x () PBitVec (int_to_pbv 4 vx))
(define-fun y () PBitVec (int_to_pbv 4 vy))
(assert (not (= (pbvand (pextract x 2 1) (pextract y 2 1))
                (pextract (pbvand x y) 2 1))))
(check-sat)
