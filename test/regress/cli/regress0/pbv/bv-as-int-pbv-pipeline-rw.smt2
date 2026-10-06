; COMMAND-LINE: --solve-bv-as-int=pbv-pipeline
; EXPECT: unsat
; bv-term-small-rw_427: in mode pbv-pipeline the lifted assertion reaches the
; PBV rewriter, which closes it; in mode pbv it is int-blasted first and the
; piand chain has to be solved by the arithmetic solver instead.
(set-logic QF_BV)
(declare-fun s () (_ BitVec 32))
(declare-fun t () (_ BitVec 32))
(assert (not (= (bvand t s) (bvand s (bvsub (bvadd t (bvand t s)) (bvand t (bvand t s)))))))
(check-sat)
