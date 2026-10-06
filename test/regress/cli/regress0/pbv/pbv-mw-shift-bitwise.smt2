; COMMAND-LINE: --pbv-mw-shift-bitwise
; EXPECT: unsat
; InstCombineShift440: (Y ^ ((X >> C) & C2)) << C = (X & (C2 << C)) ^ (Y << C).
; W1 distributes the shift, W2 turns (X >> C) << C into X & (ones << C), W3
; absorbs the mask next to C2 << C, and W5 sorts both sides into one term.
(set-logic PBV)
(declare-fun C () PBitVec)
(declare-fun Y () PBitVec)
(declare-fun C2 () PBitVec)
(declare-fun X () PBitVec)
(assert (and (pbvult C (int_to_pbv (pbvsize C) (pbvsize C))) (not (= (pbvshl (pbvxor Y (pbvand (pbvlshr X C) C2)) C) (pbvxor (pbvand X (pbvshl C2 C)) (pbvshl Y C))))))
(check-sat)
