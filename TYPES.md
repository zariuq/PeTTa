# Types in PeTTa

A type declaration is a contract. `(: f (-> A1 .. An R))` says that `f`'s
arguments have the types `A1 .. An` and its answers the type `R`. Wherever a
value meets a declared type (a call's argument, a function's answer,
`(the T E)`, a row added to a typed space), the compiler compares what it
knows of the value, its *static type* `S`, with the required type `T`:

- `S` establishes `T`: nothing is compiled, since the check could not fail;
- `S` and `T` cannot agree: a type error at compile time;
- otherwise: a runtime check.

A failing check raises a type error. Checks never bind variables, never fail,
never act and never filter answers, so a run without type errors computes what
the program computes with `--no-type-checks`. Code whose types are known
compiles as untyped code does, and a function without a declaration is simply
untyped.

The implementation is `src/types.pl` (what the compiler concludes) and
`src/types_runtime.pl` (what compiled code calls when a value was not proven to
fit). Determinism checking is an optional library, `lib/lib_det.pl`
(section 9).

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

A value of unknown type is checked where it meets a declared one. The answer of
the undeclared `lookup-width` is checked as `half`'s argument:

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

## 2. Types and values

- `Number`, `String` and `Bool` are fixed by their representation. A symbol
  declared with one of them must already be one of its values.
- `(List T)` is the finite lists of `T`s; a tuple type `(T1 .. Tn)` is the
  expressions of length n whose elements have those types.
- A declared name, `(: Shape Type)`, has as values exactly the symbols declared
  with it and the applications of its constructors. A constructor is a
  function declared with the name (or the name applied to types, as
  `(Maybe $a)`) as its result and without equations. Two names share values
  only through a symbol or constructor declared with both, so unrelated names
  can be told apart at compile time.
- An atom in a type that names no declared type is a literal tag: its one value
  is the symbol itself, as the head of `(STV Number)` is `STV`.
- `(| A B)` is a union. A value of a union establishes a type when every
  alternative does; `(the T E)` narrows it.
- `%Undefined%` (also written `_`), `Atom` and `Expression` say nothing about
  the value.
- `(: N (Alias T))` names `T`.
- `(: N (Newtype R))` is a type of its own, represented as `R`. Only an
  evaluated `(brand N E)` makes a value of `N`, and it checks `E` against `R`.
  Brands are erased at runtime, so a runtime check of `N` is a check of `R`.
  The expression `(brand N E)` held as data (in a row given to `add-atom`, say)
  is an expression, not a value of `N`.
- `(: N (Refine R P))` is the values of `R` for which the predicate `P` gives
  `True` (section 7).
- `(: &s (SpaceOf Row))` types a space (section 6).
- `(: Heap (Foreign 1))` is an opaque type of values made by Prolog code.

## 3. Open values

A value with unbound parts fits a type when some binding of those parts would.
A check of such a value holds its open parts to what the type asks of them,
the way `dif/2` holds a constraint: a later binding that breaks it raises a type
error at that binding.

```metta
(: f (-> Shape Shape))
(= (f $x) $x)
!(let $v (circle $r) (let $_ (f $v) (let $r 3 $v)))      ; (circle 3)
!(let $v (circle $r) (let $_ (f $v) (let $r "s" $v)))    ; a type error
```

Held checks are part of the value. They travel with every copy PeTTa makes
(`collapse`, a row stored in a space, an equation added at runtime), restricted
to the parts the copy contains. A union whose open value fits several
alternatives keeps the value fitting one of them as a whole; overloaded calls
keep each answer fitting one declaration together with its arguments.

## 4. Calls

- A direct call is checked against the declarations its arguments may fit. With
  one declaration, the function's own clauses check their answers; with several,
  each answer must fit one declaration jointly with the arguments.
- **One contract on every route.** A call through a variable, a partial
  application, `reduce`, a function found in a space, or a specialized copy
  checks the callee's own contract, as the direct call does.
- **`Atom` holds an argument unevaluated**, under every arrow kind and on every
  route. A call through a variable reads the callee's declaration first, then
  passes the source where the callee holds and evaluates every other argument:

  ```metta
  (= (call-it $g) ($g (+ 1 2) 4))
  ```
  ```prolog
  'call-it'(A, B) :-
      (   held_mask(A, 2, [C, _]) ->  true ;   true ),
      (   C=='Atom' ->  D=[+, 1, 2] ;   D=3 ),
      apply_fn2(A, D, 4, B).
  ```
  Under the plain arrow `->`, an `Atom` result returns the body unevaluated;
  under the other arrows an `Atom` result is any computed value.
- `Expression` is a value type: an `Expression` argument is evaluated. (HE also
  holds an expression argument of an `Expression` parameter.)
- **Partial application and currying.** `(f a)` with fewer arguments than `f`
  takes is a closure whose type is the rest of `f`'s arrow; applying it is a
  call of `f`. A function declared `(-> A (-> B C))` whose body is a partial
  application returns that closure, checked against `(-> B C)`, and its body
  runs once per closure. The same declaration types calls with two arguments as
  `(-> A B C)`.
- A closure applied where its arrow type is known has its answer checked
  against that arrow's result.
- `reduce` turns a call that fails into data, but a type error inside it is an
  error.
- `(-[det]-> ..)` and `(-[semidet]-> ..)` commit a function to its first
  matching clause; a function with several declarations commits when all of
  them do. The other arrows (`-[nondet]->`, `-[multi]->`, effect-polymorphic
  `-[$e]->`) do not commit.

## 5. Type variables

A type variable in a declaration is chosen by each call.

- Inside the body, a variable that is a parameter's whole type, or the element
  type of a list parameter, is rigid: the body is parametric in it, so
  `(: f (-> $a Number)) (= (f $x) (+ $x 1))` is a type error.
- A variable inside a structured parameter type, `(-> ($a $b) Number)`, names
  an unknown part of it.
- At runtime a check tests the declared type with its variables unknown: what
  one argument instantiates never decides another's check.
- A caller treats a result at a type variable as the type the arguments
  instantiate only when the function is parametric: each of its clauses returns
  a value whose static type carries the rigid variables there. Otherwise the
  caller checks the result. A clause added later that breaks this has the
  callers that relied on it compiled again.

## 6. Typed spaces

`(: &s (SpaceOf Row))` declares that the space holds rows of `Row`.

- Each row added is checked against `Row`: inside `add-atom` for a space passed
  in a variable, and as a boundary at a literal space, where a row of known
  type compiles no check. The row's open parts are held and stored with it.
- `match` on a literal declared space gives the pattern's variables the types
  of `Row`'s parts, and `get-atoms` gives `Row`. Code that consumes a typed read
  compiles without a check.
- Declaring `(SpaceOf Row)` for a space that already holds rows checks them
  first; a row that does not fit rejects the declaration.
- A space in a variable gives no read types. Rows written by Prolog code past
  `add-atom` are trusted.

## 7. Type tests

The program's rules for `get-type` can give values types, and they take part
in checks only if everything they reach is pure: no output, state, space
write, randomness, foreign code, or call through a variable, so that a check
never acts. A rule that is not pure stays an ordinary introspection query, with
a warning. A rule opens only the names it can return.

A refinement is usually the better way to write such a type:

```metta
(: is-even (-> Number Bool))
(= (is-even $n) (== (% $n 2) 0))
(: EvenNumber (Refine Number is-even))
(: halve (-> EvenNumber Number))
(= (halve $n) (/ $n 2))
(= (halve-twice $n) (halve (+ $n $n)))
```
```prolog
'halve-twice'(A, B) :-
    C is A+A,
    typecheck_or_error(C, 'EvenNumber'),
    halve(C, B).
```

`EvenNumber` establishes what `Number` does and conflicts with what `Number`
conflicts with, so names stay closed; `(List EvenNumber)` composes; the
predicate is checked for purity once, and runs only at runtime.

## 8. What is guaranteed, and what is trusted

**Erasure.** A run that raises no type error has the same output, answers and
effects alike, as the run of the same program with `--no-type-checks`.

**Check elimination.** A check left out because a static type establishes the
required one would have succeeded: `--oracle` compiles every check, and gives
the same output as the default build, type errors included (which check
reports a type error first may differ).

**Route independence.** A call means the same on every route (section 4).

**Observation boundary.** Held checks are attributes of variables. Comparisons
of terms (`=alpha`, `=@=`, `test`) and the standard order of unbound variables
(`@<`) do not see them, and are outside the erasure claim.

These hold under the following trust:

1. Builtins implemented in Prolog return their declared types and check their
   own arguments. (Arithmetic follows SWI-Prolog: a one-character string is
   its character code.)
2. Foreign results other than numbers, strings and booleans.
3. Rows written to spaces by Prolog code.
4. Declarations come before the code that relies on them.

**Testing.** `tests/typing/` holds programs run checked, with `--oracle` and
with `--no-type-checks`, compared on full output; `tests/typing/differential.py`
generates typed programs (open values, unions, overloads, curried and dynamic
calls, typed spaces) and checks the same invariants on them; `test.sh` runs
both.

## 9. Determinism (optional)

`!(import! &self (library lib_det))` checks determinism declarations when the
definitions in use are complete. `-[det]->` promises exactly one answer,
`-[semidet]->` at most one, `-[multi]->` at least one, `-[nondet]->` any
number. Each declaration gets a verdict:

- **proven**: the body's answer counts are within the declaration's, assuming
  the declarations of the functions it calls;
- **refuted**: the body surely gives at least two answers where one at most is
  allowed, or surely none where one is needed;
- **unproved**: anything else, including whatever the library cannot grade
  soundly (aggregates and maps, `case` with `Empty`, effect-polymorphic arrows,
  builtins whose answer counts depend on how bound their arguments are, names
  that `get-type` rules can extend).

A refuted declaration is an error; an unproved one is a warning (an error
under `--strict-det`). Functions passed to parameters declared with a
determinism arrow are checked in bodies and in runnables. `(det-verdict f)`
returns `f`'s verdicts. The library adds no code to any clause: a program
computes the same with or without it.

## 10. Changes from v1.2.0

- Held checks are one constraint store on variables, carried by every copy;
  stored rows and runtime equations keep theirs.
- Static evidence comes only from what ran or was checked: builtin results,
  `and-then`/`or-else`, `brand`, constructor results, and polymorphic results
  (section 5).
- Every call route checks the callee's contract and lets the callee decide
  which arguments it holds; curried declarations type every arity.
- Typed spaces (section 6) and refinements (section 7) are new.
- `get-type` rules take part in checks only when pure.
- `lib_det` no longer proves false verdicts (section 9).
