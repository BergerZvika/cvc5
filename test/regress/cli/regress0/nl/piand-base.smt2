; EXPECT: unsat
(set-logic QF_NIA)
(declare-const k Int)
(declare-const x Int)
(declare-const y Int)
(assert (distinct (piand k 1 1) 1))
(check-sat)
