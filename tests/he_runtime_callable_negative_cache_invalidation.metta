!(test (assertEqual (foo 1) (foo 1)) ())
!(add-atom &self (= (foo $x) (bar $x)))
!(test (assertEqual (foo 1) (bar 1)) ())
