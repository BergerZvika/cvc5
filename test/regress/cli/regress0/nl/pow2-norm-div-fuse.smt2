; DISABLE-TESTER: proof
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: lfsc
; DISABLE-TESTER: alethe
; DISABLE-TESTER: cpc
; COMMAND-LINE: --arith-pow2-norm
; EXPECT: unsat
; (s >> a) >> t = (s >> t) >> a
(set-logic ALL)
(declare-const k Int)
(declare-const s Int)
(declare-const t Int)
(assert (and (distinct (div (div s (** 2 (mod (* s s) (** 2 k)))) (** 2 t))
                       (div (div s (** 2 t)) (** 2 (mod (* s s) (** 2 k)))))
             (>= s 0) (< s (** 2 k)) (>= t 0) (< t (** 2 k)) (> k 0)))
(check-sat)
