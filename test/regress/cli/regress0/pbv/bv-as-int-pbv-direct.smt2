; COMMAND-LINE: --solve-bv-as-int=pbv-direct --produce-models
; EXPECT: sat
; EXPECT: ((x #b1010) (y #b00000011))
; Direct mode: the PBV int-blaster over the BV terms themselves, no lifting.
; Covers the parameterized kinds (extract / extend), concat, shifts and a
; signed compare, and the model recovery x := ((_ int_to_bv k) chi(x)).
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(declare-fun y () (_ BitVec 8))
(assert (= ((_ extract 3 1) x) #b101))
(assert (= ((_ extract 0 0) x) #b0))
(assert (= ((_ sign_extend 4) x) (bvsub #x00 #x06)))
(assert (bvslt (concat x x) (bvshl ((_ zero_extend 4) x) #x02)))
(assert (= (bvlshr y #x01) #x01))
(assert (= (bvurem y #x02) #x01))
(check-sat)
(get-value (x y))
