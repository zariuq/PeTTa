; Executable representatives for the copied HE spec text.

; Syntax / interpretation: non-bang forms are added atom-by-atom.
(spec-added before-bang)
!name
42
"literal # (inside) ; still string"
!(test (match &self (spec-added before-bang) ok) ok)
!(test (match &self !name ok) ok)
!(test (match &self 42 ok) ok)
!(test (match &self "literal # (inside) ; still string" ok) ok)
! (test (+ 2 3) 5)
!(+ 1 2)
!(test (match &self 3 ok) ())

; Special expressions: (= ...) with exactly two arguments defines functions;
; malformed (= ...) remains ordinary atomspace data.
(= (spec-inc $x) (+ $x 1))
!(test (spec-inc 41) 42)
(= spec-data too many args)
!(test (match &self (= spec-data too many args) ok) ok)

; Type assignment and function type atoms.
(: spec-typed SpecType)
(: spec-inc (-> Number Number))
!(test (get-type spec-typed) SpecType)
!(test (match &self (: spec-inc (-> Number Number)) ok) ok)

; Elementary meta-types.
!(test (get-metatype spec-typed) Symbol)
!(test (get-metatype 42) Grounded)
!(test (get-metatype "forty two") Grounded)
!(test (get-metatype (unknown-meta-expression 1)) Expression)
!(test (get-metatype $x) Variable)

; Special result atoms.
!(test (collapse (empty)) ())
!(test (eval (Error some-atom BadType)) (Error some-atom BadType))

; Minimal MeTTa instructions.
!(test (eval (+ 1 2)) 3)
!(test (evalc (+ 2 3) &self) 5)
!(test (chain (+ 2 3) $x (* $x 2)) 10)
!(test (unify (A $x) (A B) yes no) yes)
!(test (unify (A $x) (C B) yes no) no)
!(test (decons-atom (a b c)) (a (b c)))
!(test (cons-atom a (b c)) (a b c))
!(test (function (return 42)) 42)
!(test (repr (function (if True (return (+ 20 22)) 0))) "(+ 20 22)")
; collapse-bind packet rendering and direct superpose-bind packet acceptance
; differ across engines; the stable HE contract is the roundtrip.
!(test (collapse (superpose-bind (collapse-bind (superpose (1 2 3))))) (1 2 3))
!(test (metta (+ 1 2) %Undefined% &self) 3)
!(test (repr (metta (+ 1 2) Atom &self)) "(+ 1 2)")
!(test (metta spec-typed SpecType &self) spec-typed)
!(test (repr (collapse (metta spec-typed OtherType &self)))
       "((Error spec-typed (BadType OtherType SpecType)))")
!(test (context-space) &self)
!(test (match-types Atom Number matched missed) matched)
!(test (match-types %Undefined% Number matched missed) matched)
!(test (match-types Number Bool matched missed) missed)

; Call behavior: unknown expression returns unchanged; no result collapses to ().
!(test (unknown-spec-call 1 2) (unknown-spec-call 1 2))
!(test (collapse (empty)) ())

; Matching representatives.
(spec-pair A B)
!(test (match &self (spec-pair A B) ok) ok)
!(test (match &self (spec-pair $x B) $x) A)
!(test (match &self (spec-pair A $y) $y) B)
!(test (match &self (spec-pair $z $z) ok) ())
!(test (match &self (spec-pair $x $y) ($x $y)) (A B))
