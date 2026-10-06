; COMMAND-LINE: --pbv-mw-mask-facts
; EXPECT: unsat
; AndOrXor_537: C+1 is a power of two (C a low mask), so X >u C exactly when X
; has a bit above C (K1).
(set-logic PBV)
(declare-fun C () PBitVec)
(declare-fun X () PBitVec)
(assert (let ((c1 (pbvadd C (int_to_pbv (pbvsize C) 1)))) (and (= (pbvand c1 (pbvsub c1 (int_to_pbv (pbvsize C) 1))) (int_to_pbv (pbvsize C) 0)) (not (= (pbvugt X C) (not (= (pbvand X (pbvnot C)) (int_to_pbv (pbvsize C) 0))))) (not (= c1 (int_to_pbv (pbvsize C) 0))))))
(check-sat)
