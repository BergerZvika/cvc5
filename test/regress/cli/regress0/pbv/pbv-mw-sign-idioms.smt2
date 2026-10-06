; COMMAND-LINE: --pbv-mw-sign-idioms
; EXPECT: unsat
; Select_575a: ite(X >s -1, C1, C2) = ((X >>s (w-1)) & (C2 - C1)) + C1.
; G3 reads the sign broadcast as ite(X <s 0, ones, 0), G4/G5 push the and and
; the addition into it and cancel, G2/G6 put the left side in the same shape.
(set-logic PBV)
(declare-fun C1 () PBitVec)
(declare-fun C2 () PBitVec)
(declare-fun X () PBitVec)
(assert (not (= (ite (pbvsgt X (pbvnot (int_to_pbv (pbvsize C1) 0))) C1 C2) (pbvadd (pbvand (pbvashr X (pbvsub (int_to_pbv (pbvsize C1) (pbvsize C1)) (int_to_pbv (pbvsize C1) 1))) (pbvsub C2 C1)) C1))))
(check-sat)
