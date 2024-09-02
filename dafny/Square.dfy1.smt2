(declare-const x Int)
(assert (not (=> (and (> x 0) true) (and (<= 0 x) (= 0 (* 0 x))))))
(check-sat)