; COMMAND-LINE: --arith-exp-rare-rewrites
; EXPECT: unsat
; exp-unroll and exp-normalize (pbv/rewrites-exp): s^c -> s * s^(c-1) for a
; numeral 2 <= c <= 8, so both powers become polynomials. Without the rules
; this times out.
(set-logic ALL)
(declare-const x Int)
(assert (or (not (= (** x 3) (* x x x)))
            (not (= (** (** x 2) 2) (* x x x x)))))
(check-sat)
