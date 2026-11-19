; COMMAND-LINE: --arith-exp-rare-rewrites
; EXPECT: unsat
; exp-const-base-zero (pbv/rewrites-exp): (** 0 t) -> ite(t = 0, 1, 0), which holds
; for negative t too. Without it this times out.
(set-logic ALL)
(declare-const t Int)
(declare-const s Int)
(assert (< t 0))
(assert (or (= (** 0 t) 1) (not (= (** s 1) s))))
(check-sat)
