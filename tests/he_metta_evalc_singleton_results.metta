; Regression: HE metta/evalc result collection must not duplicate the same
; answer by falling back from the &self path into the generic space path.
!(test (collapse (metta (+ 1 2) %Undefined% &self)) (3))
!(test (collapse (evalc (+ 2 3) &self)) (5))
