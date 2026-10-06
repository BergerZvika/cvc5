; REQUIRES: poly
; COMMAND-LINE: --nl-icp --nl-icp-fix
; COMMAND-LINE: --nl-icp --nl-icp-fix --simplification=none
; EXPECT: sat
; Pure QF_NIA instance on which plain --nl-icp answers unsat. Division by zero
; is eliminated to the uninterpreted applications (int_div_by_zero x2) and
; (mod_by_zero x1); ICP uses their bounds when contracting but the original
; collectVariables only records the variables inside them as origins, so the
; resulting lemma is missing a premise and prunes the satisfying branch.
; Found by the planted-model fuzzer (seed 1227); z3 and default cvc5 say sat.
(set-logic QF_NIA)
(declare-const x0 Int)
(declare-const x1 Int)
(declare-const x2 Int)
(assert (<= x2 (- 1)))
(assert (= (mod x2 x2) (div x2 0)))
(assert (not (distinct (mod x1 0) (mod x2 x2))))
(assert (or (not (> (mod x2 x0) x1)) (>= (mod x2 x1) (- 3)) (= (mod x2 0) 1)))
(assert (or (<= (mod x2 0) (mod x1 x2)) (not (= x1 4)) (= 4 (mod x0 x0))))
(check-sat)
