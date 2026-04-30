; EXPECT: unsat
; Extracting bit 0 of x gives the low bit.
; CONV(x[0:0]) = (CONV(x) div 1) mod 2 = CONV(x) mod 2.
; Low bit of x XOR'd with x gives all low-bits XOR'd:
; Simpler: x[0:0] & ~x[0:0] = 0 at single bit width.
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (not (= (pbvand (pextract x 0 0) (pbvnot (pextract x 0 0)))
               (int_to_pbv 1 0))))
(check-sat)
