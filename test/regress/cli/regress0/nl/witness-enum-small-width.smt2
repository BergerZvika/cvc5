; COMMAND-LINE: --arith-witness-enum=20000
; EXPECT: sat
; not a valid rewrite: fails at k = 3, t = 1, s = 2
(set-logic ALL)
(declare-const k Int)
(declare-const s Int)
(declare-const t Int)
(assert (and (distinct (div (div (mod (* s (** 2 s)) (** 2 k)) (** 2 s)) (** 2 t))
                       (div (mod (* s (** 2 (div s (** 2 t)))) (** 2 k)) (** 2 s)))
             (>= s 0) (< s (** 2 k)) (>= t 0) (< t (** 2 k)) (> k 0)))
(check-sat)
