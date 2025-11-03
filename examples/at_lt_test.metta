;; Test @< family of lexicographic comparison operators
;; These are Prolog's standard term comparison operators
;; exposed in PeTTa for string/atom comparison

!(println! "=== Testing @< (lexicographic less-than) ===")
!(println! (@< "apple" "banana"))     ; true - "apple" < "banana"
!(println! (@< "zebra" "apple"))      ; false - "zebra" > "apple"
!(println! (@< "abc" "abcd"))         ; true - shorter strings are less
!(println! (@< "hello" "hello"))      ; false - equal strings

!(println! "")
!(println! "=== Testing @> (lexicographic greater-than) ===")
!(println! (@> "zebra" "apple"))      ; true
!(println! (@> "apple" "banana"))     ; false

!(println! "")
!(println! "=== Testing @=< (lexicographic less-than-or-equal) ===")
!(println! (@=< "apple" "banana"))    ; true
!(println! (@=< "hello" "hello"))     ; true - equal

!(println! "")
!(println! "=== Testing @>= (lexicographic greater-than-or-equal) ===")
!(println! (@>= "zebra" "apple"))     ; true
!(println! (@>= "hello" "hello"))     ; true - equal

!(println! "")
!(println! "=== Multi-character strings ===")
!(println! (@< "aardvark" "zebra"))           ; true
!(println! (@< "metamath" "metta"))           ; true
!(println! (@< "verification" "verified"))    ; false

!(println! "")
!(println! "=== Case sensitivity ===")
!(println! (@< "Apple" "apple"))      ; true - uppercase < lowercase in ASCII
!(println! (@< "Z" "a"))              ; true - uppercase letters come before lowercase

!(println! "")
!(println! "=== Using in a function ===")
(: string< (-> String String Bool))
(= (string< $x $y) (@< $x $y))

!(println! "Testing string< function:")
!(println! (string< "first" "second"))        ; true
!(println! (string< "second" "first"))        ; false
