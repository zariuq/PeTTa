;; Characterize the direct once/select fast path for compiled equation calls.
;; Multi-equation calls keep first-produced visible order.
;; Single-equation multivalue calls keep source-produced visible order too.

(= (multi-choice) 1)
(= (multi-choice) 2)

(= (single-choice) (superpose (1 2 3)))

!(test (assertEqual (collapse (multi-choice)) (1 2)) ())
!(test (assertEqual (once (multi-choice)) 1) ())
!(test (assertEqual (select (multi-choice)) 1) ())

!(test (assertEqual (collapse (single-choice)) (1 2 3)) ())
!(test (assertEqual (once (single-choice)) 1) ())
!(test (assertEqual (select (single-choice)) 1) ())
