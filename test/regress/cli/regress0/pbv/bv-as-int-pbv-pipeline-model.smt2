; COMMAND-LINE: --solve-bv-as-int=pbv-pipeline --produce-models
; EXPECT: sat
; EXPECT: ((x #b00000101) (y #b0000000000000110))
; Model recovery: pbv-to-int defines x := ((_ nat2bv 8) chi(pbv_x)) from the
; lifted-variable pairs bv-to-int handed it.
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 16))
(assert (= x #x05))
(assert (= y (bvadd ((_ zero_extend 8) x) #x0001)))
(check-sat)
(get-value (x y))
