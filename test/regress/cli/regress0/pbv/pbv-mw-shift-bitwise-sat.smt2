; COMMAND-LINE: --pbv-mw-shift-bitwise --pbv-mw-sign-idioms --pbv-mw-mask-facts
; EXPECT: sat
; (x >> c) << c drops the low bits of x: satisfiable, and the rules must keep
; it so (W2 gives x & (ones << c), which differs from x).
(set-logic PBV)
(declare-fun c () PBitVec)
(declare-fun x () PBitVec)
(assert (pbvult c (int_to_pbv (pbvsize c) (pbvsize c))))
(assert (not (= (pbvshl (pbvlshr x c) c) x)))
(check-sat)
