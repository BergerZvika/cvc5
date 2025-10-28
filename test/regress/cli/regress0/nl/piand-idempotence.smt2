; EXPECT: unsat
; DISABLE-TESTER: proof
(set-logic QF_NIA)
(declare-const k Int)
(declare-const x Int)
(declare-const y Int)
(assert (= x y))
(assert (distinct (piand k x y) x))
(check-sat)
