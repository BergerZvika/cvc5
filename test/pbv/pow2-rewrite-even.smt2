(set-logic ALL)
(set-option :produce-models true)
(set-option :incremental true)
(declare-const k Int)
(declare-const _pbv_s Int)
(declare-const _pbv_t Int)
(assert (> k 0))
(assert (and (and (and (and (distinct (<= _pbv_s (- (^ 2 k) (+ _pbv_s 1))) (< _pbv_s (- (^ 2 k) (+ _pbv_s 1)))) (>= _pbv_s 0)) (< _pbv_s (^ 2 k))) (= k k)) (> k 0)))
(check-sat)
(exit)


