; Type and error representatives from the HE specification algorithms.

(: he-num-id (-> Number Number))
(= (he-num-id $x) $x)

!(test (he-num-id 7) 7)
!(test (he-num-id (+ 2 3)) 5)
!(test (repr (collapse (he-num-id a)))
       "(a)")
!(test (repr (collapse (he-num-id 1 2)))
       "((Error (he-num-id 1 2) IncorrectNumberOfArguments))")

(: he-expr-id (-> Expression Expression))
(= (he-expr-id $x) $x)
!(test (repr (he-expr-id (+ 1 2))) "(+ 1 2)")

(: he-atom-id (-> Atom Atom))
(= (he-atom-id $x) $x)
!(test (repr (he-atom-id (+ 1 2))) "(+ 1 2)")

(: he-symbol-id (-> Symbol Symbol))
(= (he-symbol-id $x) $x)
!(test (he-symbol-id raw-symbol) raw-symbol)

(: he-grounded-id (-> Grounded Grounded))
(= (he-grounded-id $x) $x)
!(test (he-grounded-id 7) 7)

(: he-cast-number Number)
(: he-cast-symbol Symbolish)

!(test (metta he-cast-number Number &self) he-cast-number)
!(test (metta he-cast-number Atom &self) he-cast-number)
!(test (repr (collapse (metta he-cast-number String &self)))
       "((Error he-cast-number (BadType String Number)))")
!(test (metta he-cast-symbol Symbolish &self) he-cast-symbol)
!(test (repr (collapse (metta he-cast-symbol OtherSymbolish &self)))
       "((Error he-cast-symbol (BadType OtherSymbolish Symbolish)))")

(: he-bad-ret (-> Number Symbol))
(= (he-bad-ret $x) (+ $x 1))

!(test (repr (collapse (he-bad-ret 1)))
       "((Error (he-bad-ret 1) (BadType Symbol Number)))")

!(return 42)
