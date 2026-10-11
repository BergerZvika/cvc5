; COMMAND-LINE: --learned-rewrite-rules=reduce-mods
; EXPECT: unsat
; Case 1 of the mod-2^k reducer, run by learned-rewrite: under 0 <= k <= m,
; (mod (mod x 2^m) 2^k) is (mod x 2^k).
(set-logic ALL)
(declare-const x Int)
(declare-const k Int)
(declare-const m Int)
(assert (>= k 0))
(assert (<= k m))
(assert (distinct (mod (mod x (** 2 m)) (** 2 k)) (mod x (** 2 k))))
(check-sat)
