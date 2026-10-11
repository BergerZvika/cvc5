; COMMAND-LINE: --learned-rewrite-rules=int
; EXPECT: sat
; The mod-2^k reducer must not strip the inner mod when k < 0: 2^k is 0, so
; the outer mod does not truncate and (mod (mod x 32) 0) is not (mod x 0).
(set-logic ALL)
(declare-const x Int)
(declare-const k Int)
(declare-const m Int)
(assert (< k 0))
(assert (= m 5))
(assert (distinct (mod (mod x (** 2 m)) (** 2 k)) (mod x (** 2 k))))
(check-sat)
