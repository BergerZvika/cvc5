; COMMAND-LINE: --solve-bv-as-int=pbv-pipeline
; COMMAND-LINE: --solve-bv-as-int=pbv
; EXPECT: sat
; A UF application inside an ite against a lifted term: only type-checks
; because both PBV modes lift the function symbol too (--pbv-lift-uf).
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(assert (= (ite (bvult x y) (f x) (bvadd x #x01)) y))
(assert (= (f x) (f y)))
(assert (not (= x y)))
(check-sat)
