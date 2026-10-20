!(import! &self (library lib_builtin_types))
!(import! &self (library lib_he))

(: a A)

; The value of eval, of an undeclared function, of a closure without an arrow
; type or of catch has no static type: a declared output receiving it is
; checked at runtime, and an A is rejected where a B is required.
(= (untyped-id $x) $x)

(: via-eval (-> A B))
(= (via-eval $x) (eval $x))

(: via-untyped (-> A B))
(= (via-untyped $x) (untyped-id $x))

(: via-closure (-> A B))
(= (via-closure $x) (let $f untyped-id ($f $x)))

(: via-catch (-> A B))
(= (via-catch $x) (catch (untyped-id $x)))

!(test (car-atom (catch (via-eval a))) Error)
!(test (car-atom (catch (via-untyped a))) Error)
!(test (car-atom (catch (via-closure a))) Error)
!(test (car-atom (catch (via-catch a))) Error)

; A value that fits passes the same check.
(: kept (-> A A))
(= (kept $x) (untyped-id $x))

!(test (kept a) a)
