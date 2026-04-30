; EXPECT: sat
; Negative case: the pbv-reverse-extract-and rule is specific to pbvand.
; Replacing AND with subtraction (pbvsub) produces an expression that does
; NOT match the rule pattern.  The equation:
;   SUB(ext[3:1](x), ext[3:1](y)) = ext[3:1](SUB(x, y))
; is NOT a tautology in T_PBV (subtraction does not distribute through
; extraction in general because carry bits may propagate across boundaries).
;
; We assert the alleged equality and expect sat, confirming that cvc5 does
; NOT erroneously rewrite it to true.
(set-logic PBV)
(declare-fun x () PBitVec)
(declare-fun y () PBitVec)
(assert (= (pbvsize x) (pbvsize y)))
; Pick a concrete model: x = 0b...0100 (bit 2 set), y = 0b...0110 (bits 2,1
; set in the slice [3:1]).  ext[3:1](x) = 0b010, ext[3:1](y) = 0b011.
; SUB(0b010, 0b011) = 0b111 (mod 8) whereas ext[3:1](SUB(x,y)) may differ
; due to borrow propagation from lower bits.
; The assertion below is satisfiable because the equality fails in general.
(assert (not (= (pbvsub (pextract x 3 1) (pextract y 3 1))
                (pextract (pbvsub x y) 3 1))))
(check-sat)
