; COMMAND-LINE: --pbv-div-lemmas
; EXPECT: unsat
; muldivrem_735b: without overflow in C1*C2, (X / C1) / C2 = X / (C1 * C2).
(set-logic PBV)
(declare-fun C1 () PBitVec)
(declare-fun C2 () PBitVec)
(declare-fun X () PBitVec)
(assert (and (= (pextract (pbvmul (pzero_extend (pbvsize C1) C1) (pzero_extend (pbvsize C1) C2)) (- (* 2 (pbvsize C1)) 1) (pbvsize C1)) (int_to_pbv (pbvsize C1) 0)) (not (= C1 (int_to_pbv (pbvsize C1) 0))) (not (= C2 (int_to_pbv (pbvsize C1) 0))) (not (= (pbvudiv (pbvudiv X C1) C2) (pbvudiv X (pbvmul C1 C2))))))
(check-sat)
