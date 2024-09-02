(declare-const x Int)
(assert (not (=> (and (> x 0) true) (<= 0 x))))
(check-sat)