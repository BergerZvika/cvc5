; EXPECT: sat
; ADM ensures kappa(x) > 0 for every free PBV variable x.
; With kappa >= 1 there exist at least TWO distinct values: 0 and 1.
; So x > 0 (i.e. x = 1,2,...) is satisfiable — the domain has more than {0}.
; Without ADM (kappa could be 0): chi(x) in [0,1) = {0}, making x > 0 unsat.
; With ADM (kappa >= 1): chi(x) can be 1, satisfying x > 0.
; CONV(pbvugt x 0) = chi(x) > 0. SAT.
(set-logic PBV)
(declare-fun x () PBitVec)
(assert (pbvugt x (int_to_pbv (pbvsize x) 0)))
(check-sat)
