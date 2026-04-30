; EXPECT: sat
; Negative case: the pbv-reverse-extract-and rule requires both extracts to
; use IDENTICAL bounds.  When the upper index j differs, the two operands of
; pbvand would have different widths and the expression is ill-typed.  We
; cannot directly write ill-typed SMT2.
;
; Instead we demonstrate the satisfiability of a goal that would be false if
; the solver incorrectly over-generalised the rule to mismatched bounds.
;
; We use the fact that extract[2:1](x) and extract[2:1](y) can differ: there
; exist x, y of the same width such that the slice [2:1] of x ANDed with the
; slice [2:1] of y is NOT equal to x itself (trivially satisfiable).
; If the rewriter spuriously fired on an expression that does not match the
; pattern it would collapse the formula incorrectly and return unsat.
; The expected answer is sat, confirming no spurious rewrite occurred.
(set-logic PBV)
(declare-fun x () PBitVec)
(declare-fun y () PBitVec)
(assert (= (pbvsize x) (pbvsize y)))
; A satisfiable formula that is NOT a rewrite-rule instance.
; AND of two independent slices need not equal the full value.
(assert (pbvult (pbvand (pextract x 2 1) (pextract y 2 1))
                (pextract x 2 1)))
(check-sat)
