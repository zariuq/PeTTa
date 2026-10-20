!(import! &self (library lib_builtin_types))
!(import! &self (library lib_he))

(: a A)
(: b B)
(: aa (-> A A))
(= (aa a) a)

; catch produces its argument's value or an (Error Detail Ctx) expression, so
; its result has no static type: the declared output is checked at runtime,
; where an A is rejected as a B.
(: bad-catch (-> A B))
(= (bad-catch $x) (catch (aa $x)))

!(bad-catch a)
