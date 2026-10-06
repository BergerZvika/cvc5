; REQUIRES: poly
; COMMAND-LINE: --nl-icp --nl-icp-fix --simplification=none
; EXPECT: sat
; The bound (f y) <= 1 is used when contracting x, so it must be part of the
; origins of the ICP conflict; otherwise the conflict clause also excludes the
; branch (f y) >= 3, which has the model x=25/4, (f y)=3, w=v=1/2.
(set-logic QF_UFNRA)
(declare-fun f (Real) Real)
(declare-const x Real)
(declare-const y Real)
(declare-const w Real)
(declare-const v Real)
(assert (= x (+ (* 2.0 (f y)) (* w v))))
(assert (>= x 5.0))
(assert (>= w 0.0)) (assert (<= w 1.0))
(assert (>= v 0.0)) (assert (<= v 1.0))
(assert (or (>= (f y) 3.0) (<= (f y) 1.0)))
(check-sat)
