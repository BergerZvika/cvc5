; REQUIRES: poly
; COMMAND-LINE: --nl-icp --nl-icp-fix
; COMMAND-LINE: --arith-tune-for-logic=icp-fix
; EXPECT: sat
; Model: width 2, s = t = 1: (s << (t * (t | 0))) = 2 != 1 = s.
; Plain --nl-icp answers unsat: the int-blasted problem is full of opaque
; leaves ((** 2 _k), piand, purification skolems) whose bounds ICP uses but,
; without --nl-icp-fix, never records as origins of its lemmas.
; From sat25/mut/cade19_mutant/terms_size3-sat-bvand-to-bvor/test-pbv534.
(set-logic PBV)
(declare-const s PBitVec)
(declare-const t PBitVec)
(assert (distinct (pbvshl s (pbvmul t (pbvor t (int_to_pbv (pbvsize s) 0)))) s))
(check-sat)
