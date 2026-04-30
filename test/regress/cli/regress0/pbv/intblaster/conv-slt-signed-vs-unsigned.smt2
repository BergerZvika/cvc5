; EXPECT: unsat
; SLT vs ULT distinction: the key test that exercises utsSym.
; At k=4: 13 (= 0b1101 = -3 in signed) is LESS THAN 3 signed,
; but GREATER THAN 3 unsigned.
; pbvslt (int_to_pbv 4 13) (int_to_pbv 4 3) should be TRUE:
;   utsSym(4, 13) = 13 - 16 = -3,  utsSym(4, 3) = 3.  -3 < 3. Yes.
; pbvult (int_to_pbv 4 13) (int_to_pbv 4 3) should be FALSE:
;   13 < 3 is false.
; We assert both relations together and check consistency.
; (NOT pbvult) AND (pbvslt) must be satisfiable.
(set-logic PBV)
(declare-fun k () Int)
(assert (= k 4))
(assert (pbvslt (int_to_pbv k 13) (int_to_pbv k 3)))
(assert (not (pbvult (int_to_pbv k 13) (int_to_pbv k 3))))
(check-sat)
