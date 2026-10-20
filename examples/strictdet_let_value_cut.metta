(: let-cut-choice (-[det]-> Atom %Undefined%))
(= (let-cut-choice $value) (cut))
(= (let-cut-choice a) a)

!(test (collapse (let-cut-choice a)) (True))
