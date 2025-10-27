; EXPECT: unsat
(set-logic QF_NIA)
(declare-const k Int)
(declare-const x Int)
(declare-const y Int)
(assert (> k 0))
(assert (= y 1))
(assert (distinct (piand k x y) (mod x 2)))
(check-sat)
