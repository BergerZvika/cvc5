; REQUIRES: poly
; COMMAND-LINE: --nl-icp --nl-icp-fix --simplification=none
; EXPECT: sat
; Pure QF_NIA, no division by zero in the model (x0=x1=-2, x2=1), yet plain
; --nl-icp --simplification=none answers unsat: a non-constant divisor is
; enough for OperatorElim to introduce the (int_div_by_zero x) / (mod_by_zero
; x) applications, whose bounds ICP uses without recording them as origins.
; Found by the planted-model fuzzer (seed 1368).
(set-logic QF_NIA)
(declare-const x0 Int)
(declare-const x1 Int)
(declare-const x2 Int)
(assert (<= (- 3) x0))
(assert (<= x0 1))
(assert (not (> (div x2 x0) (mod x1 x0))))
(assert (= 1 x2))
(assert (not (distinct x0 x1)))
(assert (not (>= (+ x0 x0) (* x1 x0 x2))))
(assert (not (= (* x1 x2 x1) x2)))
(assert (or (distinct (mod x0 x1) (- 1)) (= (+ x1 x1) x0) (< (mod x1 x2) 4)))
(assert (or (distinct x1 4) (= (* x2 x0) 1)))
(check-sat)
