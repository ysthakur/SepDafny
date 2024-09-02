(declare-const x Int)
(declare-const y Int)
(assert (not (=> (and (<= y x) (< y x)) (<= (+ y 1) x))))
(check-sat)