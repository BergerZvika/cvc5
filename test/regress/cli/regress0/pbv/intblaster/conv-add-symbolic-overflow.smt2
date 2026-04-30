; EXPECT: unsat
; CONV wraps addition: (2^k - 1) + 1 = 0  for any k >= 1.
; With symbolic width: int_to_pbv k (pow2(k)-1) + int_to_pbv k 1 = int_to_pbv k 0.
; We express all-ones as int_to_pbv k (2^k - 1) by using x = ~0.
; Simpler form: pbvadd x (pbvnot x) = all-ones, and then +1 wraps to 0.
; So: (pbvadd (pbvnot (int_to_pbv (pbvsize x) 0)) (int_to_pbv (pbvsize x) 1))
;     = int_to_pbv (pbvsize x) 0   [all-ones + 1 = 0 mod 2^k]
; This test exercises Range constraints: without 0 <= chi(x) < 2^k the
; mod-pow2 encoding of addition is not pinned correctly.
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (not (= (pbvadd (pbvnot (int_to_pbv (pbvsize x) 0))
                        (int_to_pbv (pbvsize x) 1))
               (int_to_pbv (pbvsize x) 0))))
(check-sat)
