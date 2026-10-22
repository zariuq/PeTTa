# Types in PeTTa

A type declaration is a contract. `(: f (-> A1 .. An R))` says that `f`'s
arguments have the types `A1 .. An` and its results the type `R`. The compiler
checks a contract where a value meets a declared type: an argument of a call,
a function's result, `(the T E)`. At each such boundary it compares what it
knows of the value, its *static type* `S`, with the required type `T`:

- `S` establishes `T`: nothing is compiled, the check could not fail;
- `S` and `T` cannot agree: a type error at compile time;
- otherwise: a fast runtime check of what is known of `T`.

A failing check raises a type error. Checks never bind variables and never
filter answers, so a run without type errors computes exactly what the program
computes with `--no-type-checks`. Typed code therefore costs what untyped code
costs, and a function without a declaration is simply untyped.

The implementation is `src/types.pl`. Determinism modes are an optional module,
`lib/lib_det.pl` (section 6).

## 1. What the compiler produces

Typed code compiles like untyped code. `loop`'s arguments are established
`Number`s, so its clause is the same as an undeclared loop's:

```metta
(: loop (-> Number Number Number))
(= (loop $n $acc) (if (== $n 0) $acc (loop (- $n 1) (+ $acc $n))))
```
```prolog
loop(A, B, C) :-
    (   A==0
    ->  C=B
    ;   D is A+ -1,
        E is B+A,
        loop(D, E, C)
    ).
```

A value of unknown type is checked where it meets a declared one. The result
of the undeclared `lookup-width` is checked as `half`'s argument:

```metta
(= (lookup-width $k) (match &self (width $k $w) $w))
(: half (-> Number Number))
(= (half $x) (/ $x 2))
(= (half-width $k) (half (lookup-width $k)))
```
```prolog
'half-width'(A, B) :-
    'lookup-width'(A, C),
    (   number(C)
    ->  true
    ;   typecheck_or_error(C, 'Number')
    ),
    half(C, B).
```

Patterns learn from the declaration: the field of a `circle` is a `Number`, so
the arithmetic needs no check.

```metta
(: circle (-> Number Shape))
(: area (-> Shape Number))
(= (area (circle $r)) (* 3.14 (* $r $r)))
```
```prolog
area([circle, A], B) :-
    C is A*A,
    B is 3.14*C.
```

A closure is known only at runtime, and its arrow type is checked as its arity,
so its result is checked where the arrow's result type is demanded:

```metta
(: twice (-> (-> Number Number) Number Number))
(= (twice $f $x) ($f ($f $x)))
```
```prolog
twice(A, B, C) :-
    apply_fn1(A, B, D),
    (   number(D)
    ->  true
    ;   typecheck_or_error(D, 'Number')
    ),
    apply_fn1(A, D, C),
    (   number(C)
    ->  true
    ;   typecheck_or_error(C, 'Number')
    ).
```

## 2. Types and values

- `Number`, `String`, `Bool` and `(List T)` are fixed by their representation.
  A symbol declared with one of them must be one of its values.
- A declared name, `(: Shape Type)`, has as values exactly the symbols declared
  with it and the applications of its constructors (functions declared with the
  name as result and without equations). Two names share values only through a
  symbol or constructor declared with both. Rules of the program for `get-type`
  can give any value any type; they take part in checks only if no effect is
  reachable from them, so that a check never acts.
- An atom in a type that names no declared type is a literal tag: its one value
  is the symbol itself, as the head of `(STV Number)` is `STV`.
- A tuple type `(T1 .. Tn)` is a fixed-length expression, checked element by
  element.
- `%Undefined%` (also written `_`), `Atom` and `Expression` say nothing.
- `(| A B)` is a union. A value of a union fits a type only if every alternative
  does (narrow it with `(the T E)`); a value fits a union if it fits one
  alternative.
- `(: N (Alias T))` names `T`.
- `(: N (Newtype R))` is a type of its own, represented as `R`. Only
  `(brand N E)` makes a value of `N`: it checks `E` against `R`. A brand fits
  what its representation fits, a head pattern matches the representation, and
  brands are erased at runtime.
- `(: &s (SpaceOf Row))` declares a space whose `match` patterns may apply a
  function with one `det` declaration, such as the as-pattern `(@ $whole pat)`.
- `(: Heap (Foreign 1))` is an opaque type of values made by Prolog code.

## 3. Type variables

A type variable in a declaration is chosen by each call.

- Inside the body, a variable that is a parameter's whole type, or the element
  type of a list parameter, is rigid: the body is parametric in it, so
  `(: f (-> $a Number)) (= (f $x) (+ $x 1))` is a type error.
- A variable inside a structured parameter type, `(-> ($a $b) Number)`, names
  an unknown part of it.
- A result returned at a type variable is trusted (section 5).
- An argument's runtime check tests the declared type with its variables
  unknown: what one argument instantiates never decides another's check.

## 4. Calls

- A direct call is checked against the declarations its arguments may fit;
  with one declaration the function's own clauses check its result.
- A call reached only at runtime - a closure, a partial application, `reduce`,
  a function picked from a space - is checked by the same contract: with
  several declarations, the ones the arguments fit admit the call, the body
  runs once, and each result must fit one of them jointly with the arguments.
- A check of a value with unbound parts holds those parts to the type: each is
  checked when it is bound. Comparisons of values (`=alpha`, `=@=`, `test`) do
  not see these held checks.
- `reduce` turns a call that fails into data, but a type error inside it is an
  error.
- `Atom` holds an argument or a result unevaluated under `->`; under the other
  arrows `Atom` is any value, computed as usual.
- `(-[det]-> ..)` and `(-[semidet]-> ..)` commit a function to its first
  matching clause; a function with several declarations commits when all of
  them do. The other arrows (`-[nondet]->`, `-[multi]->`, effect-polymorphic
  `-[$e]->`) do not commit.

## 5. What is guaranteed, and what is trusted

**Erasure.** A run that raises no type error computes what the program computes
with every check removed, answers and effects alike.

**Static types are sound.** A value with static type `S` fits `S` at runtime,
so a check left out because `S` establishes `T` would have succeeded.

**Compile-time errors** follow conventional static typing, each with a stated
guarantee: two atomic types that conflict share no value; a union conflicts
with a type when one of its alternatives does, and for atomic alternatives
that branch can never fit; two list types whose element types are atomic and
conflict share only `()`; conflicting arrows differ in length, in a parameter
or in the result, and a call through the demanded arrow with an argument of a
conflicting atomic parameter type breaks the callee's contract. (Nested types
are compared part by part: `(List (List Number))` and `(List (List String))`
conflict although `(())` fits both.)

These hold under the following trust:

1. Builtins implemented in Prolog return their declared types and check their
   own arguments.
2. A result returned at a type variable fits the caller's instance.
3. Foreign results that are not numbers, strings or booleans.
4. Declarations come before code relies on them; removing a declaration does
   not recompile its callers.

The rules are formalized in Lean, in MeTTapedia's
`Mettapedia/Languages/MeTTa/PeTTa/ContractTyping` (no `sorry`, standard
axioms only): establishment and its soundness, each conflict rule's
guarantee, rigid type variables, Newtypes and brand erasure, the call
contract and its independence of the route a call takes, the check of
arguments against their declared types, erasure with held checks, and the
determinism grades together with the soundness of the exhaustiveness check
below. The table there names each Lean definition after its predicate here.
Not modelled: effect-polymorphic arrows, the program's `get-type` rules,
metatypes, and arguments that share an unbound variable.

## 6. Determinism modes (optional)

`!(import! &self (library lib_det))` checks determinism declarations when the
definitions in use are complete. `-[det]->` promises exactly one answer,
`-[semidet]->` at most one, `-[multi]->` at least one, `-[nondet]->` any
number.

- A body is graded by the answer counts of what it does: literals and
  arithmetic give one, `superpose` several, `match` any, `if` and `case` one of
  their branches, `once` at most one, and a declared function its arrow's
  grade. An effect-polymorphic arrow takes the grade of the function passed to
  it; an undeclared function is graded from its clauses.
- A det or semidet function answers with its first matching clause; it gives
  no answer unless its heads cover the declared types, which is decided by
  the pattern-matrix check (constructors of declared names, lists, Bool,
  tuples, unions, Newtype representations; `Atom`, `Expression` and other
  open types are covered by variables only).
- A function passed to a parameter declared with a determinism arrow must
  have that grade or a finer one; this is checked for functions passed by
  name, partial application or lambda, and for parameters passed on. A
  closure computed at runtime is trusted to keep its declared grade.
- A body that surely gives more answers than its arrow allows is an error. A
  body that may give fewer than `det` or `multi` need, or depends on a call the
  module cannot grade, is reported as a warning (an error under
  `--strict-det`).
- `(det-verdict f)` returns `f`'s verdicts.

The module adds no code to any clause: a program computes the same with or
without it.

## 7. Changes from v1.1

Removed: `--strict`, determinism checking in the core (now `lib_det`), type
inference for undeclared functions, flow-sensitive narrowing, deferred checks
of conflicting uses, trust waivers by library, typed rows of spaces.

Changed:

- A type error is always an error; v1.1 dropped some answers instead.
- Type names are closed, as in section 2.
- A union fits a type only if every alternative does.
- A type variable that only the result mentions is the function's own choice.
- `car-atom` of `()` is `()`.
- A call reached at runtime checks its callee's whole contract.
