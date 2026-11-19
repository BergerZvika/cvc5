; COMMAND-LINE: --learned-rewrite-rules=shift-add-distrib
; EXPECT: sat
; s >= p + 2^u - 1 does not keep the addition from wrapping (s=2, x=z=1, y=2:
; 0 vs 2). The old side condition let rule F fire here and gave unsat.
(set-logic PBV)
(declare-const p Int)
(declare-const u Int)
(declare-const s Int)
(declare-fun x () PBitVec)
(declare-fun z () PBitVec)
(declare-fun y () PBitVec)
(assert (= (pbvsize x) p))
(assert (= (pbvsize z) u))
(assert (= (pbvsize y) s))
(assert (>= p 1))
(assert (>= u 1))
(assert (>= s (+ p (- (int.pow2 u) 1))))
(assert (not (= (pbvlshr (pbvadd (pbvshl (pzero_extend (- s p) x) (pzero_extend (- s u) z)) y)
                         (pzero_extend (- s u) z))
                (pbvadd (pzero_extend (- s p) x) (pbvlshr y (pzero_extend (- s u) z))))))
(check-sat)
