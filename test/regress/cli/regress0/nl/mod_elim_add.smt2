; COMMAND-LINE: --learned-rewrite
; EXPECT: unsat
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
(set-logic QF_NIA)
(declare-const A Int)
(declare-const B Int)
(declare-const C Int)
(declare-const D Int)
(define-fun lemma () Bool (= (mod (+ (mod A (+ C D)) B) (+ C D)) (mod (+ A B) (+ C D))))

(assert (> C 0))
(assert (> D 0))

(assert (not lemma))
(check-sat)
