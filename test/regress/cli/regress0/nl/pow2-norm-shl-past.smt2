; DISABLE-TESTER: proof
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: lfsc
; DISABLE-TESTER: alethe
; DISABLE-TESTER: cpc
; COMMAND-LINE: --arith-pow2-norm --nl-ext-tplanes
; EXPECT: unsat
; (s << t) << (2^k - (t+1)) is a shift by 2^k - 1 >= k, i.e. 0.
(set-logic ALL)
(declare-const k Int)
(declare-const s Int)
(declare-const t Int)
(assert (and (distinct (mod (* (* s (** 2 t)) (** 2 (- (** 2 k) (+ t 1)))) (** 2 k)) 0)
             (>= s 0) (< s (** 2 k)) (>= t 0) (< t (** 2 k)) (> k 0)))
(check-sat)
