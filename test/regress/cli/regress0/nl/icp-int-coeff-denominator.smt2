; REQUIRES: poly
; COMMAND-LINE: --nl-icp --nl-icp-fix
; EXPECT: sat
; The ICP candidate for x must divide by both the coefficient of x and the
; denominator of the remaining sum. Using only the coefficient turned the
; bound x <= -3/2 into x <= -15/2, ruling out the model x=-2, y=z=0.
(set-logic QF_NIRA)
(declare-const x Int)
(declare-const y Real)
(declare-const z Real)
(declare-const w Real)
(declare-const v Real)
(assert (<= (+ (* 2 (to_real x)) (/ y 3.0) (/ z 5.0)) (- 3.0)))
(assert (>= y 0.0)) (assert (<= y 3.0))
(assert (>= z 0.0)) (assert (<= z 5.0))
(assert (>= x (- 2)))
(assert (>= w 1.0)) (assert (<= w 2.0))
(assert (>= v 1.0)) (assert (<= v 2.0))
(assert (= (* w v) 2.0))
(check-sat)
