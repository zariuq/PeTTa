# Types in PeTTa

This document describes the type checker of PeTTa (`src/types.pl` and the
calls into it from `src/translator.pl`): what a declaration means, the rules
the compiler applies, the code they generate, why they are sound, and how they
relate to PeTTa v1.0.6 and v1.1. It is meant to be enough to maintain the
checker, or to reimplement it.

## 1. Contracts

A declaration `(: f (-> A1 .. An R))` is a contract: each argument of `f` has
the type `Ai`, each result the type `R`. The compiler enforces contracts at
*boundaries*:

- an argument passed to a declared function,
- a result returned by a clause of a declared function,
- the value of `(the T E)`,
- an argument passed through a closure or `reduce` to a declared function.

At a boundary a value whose *static type* is `S` meets a *required type* `T`.
There are three outcomes:

| `S` and `T` | generated code |
|---|---|
| `S` establishes `T` (`S ⊑ T`) | nothing |
| `S` and `T` are inconsistent (`S ≁ T`) | none: a type error at compile time |
| otherwise | a check at runtime of the part of `T` that is known |

A runtime check that fails raises a type error. A check never fails silently
and never binds a variable, so it never removes an answer. Hence:

> **Erasure.** A run that raises no type error computes the same answers, in
> the same order and with the same effects, as the same program compiled with
> every check removed (`--no-type-checks`).

Types are an optional layer: they stop a wrong run early, with a message naming
the value and the type, and they let the compiler drop the checks it can prove
redundant, but they never change what a correct run computes. Two parts of a
declaration are not checks, and erasure keeps them: `Atom`, which passes an
argument unevaluated (§2.10), and the clause commitment of `-[det]->` and
`-[semidet]->` (§2.8).

## 2. The rules

### 2.1 Values and types

PeTTa's values are numbers, strings, `True`/`False`, symbols (Prolog atoms),
expressions (Prolog lists), functions (a function's name, or
`partial(F, Args)`), and *foreign* values: any other Prolog term or blob, such
as a heap from `library(heaps)`.

The *value relation* `typecheck_ok(V, T)` decides at runtime whether `V` fits
`T`:

| `T` | the values that fit |
|---|---|
| `Number`, `String`, `Bool` | numbers, strings, `True` and `False` |
| `%Undefined%`, `Atom`, `Expression` | every value |
| `(List E)` | lists whose elements fit `E`; for an unknown `E`, lists (the first cell is tested: MeTTa's expressions are proper lists) |
| `(-> A1 .. An R)` | functions and constructors taking `n` arguments |
| `(\| T1 .. Tn)` | values that fit some `Ti` |
| a name `N` | symbols declared `(: s N)`; applications `(c X1 ..)` of a constructor declared `(: c (-> A1 .. N))` whose fields fit the `Ai` |
| a tuple `(T1 .. Tn)` | expressions of `n` elements fitting the `Ti`, where an atom `Ti` is also fitted by itself: `(STV 0.9 0.8)` fits `(STV Number Number)` |
| anything else | what `get-type` or `get-metatype` say: `Symbol`, `Grounded`, `Variable`, and the types of user `get-type` rules |

An unbound value fits every type: a check describes the value as it is, it does
not constrain later bindings. A foreign value fits every type except the
primitive, list and arrow types: it cannot be inspected.

### 2.2 Static types

While translating, the compiler gives each value a *static type*, a type that
every runtime value of it fits (§4.2), or `%Undefined%` when nothing is known.
A variable inside a static type is free: the value fits each instance, as `()`
fits `(List $a)` for every `$a`.

| value | static type |
|---|---|
| a number, a string, `True`/`False` | `Number`, `String`, `Bool` |
| `()` | `(List $a)` |
| a symbol with exactly one declared type `T` | `T` |
| a function's or constructor's name; a partial application | its arrow type (the rest of it), if it has one declaration; for an undeclared function, `(-> %Undefined% ..)` of its arity |
| a constructor application `(c X1 .. Xn)` | the declared result, if the fields establish the declared field types |
| other data `(X1 .. Xn)` | `(List T)` if the elements' types agree on `T`, else the tuple of their types; unknown if `X1` is a symbol without a type, as for the call of an undeclared function |
| a parameter of the clause | its declared type (§2.8) |
| a head argument rebuilt in the body | the parameter's type |
| a variable bound by a pattern | the part of the matched value's type (§2.9) |
| a call of a declared function | its declared result under the instance (§2.7) |
| `(the T E)` | `T` |
| `(collapse E)` | `(List S)`, for `E` of type `S` |
| `if`, `case`, `superpose`, `hyperpose` | the *merge* of the alternatives |
| `(foldall F G I)`, `foldl-atom` | the merge of the initial value and the step's result |
| `map-atom`; `filter-atom` | `(List S)` for the body's `S`; the list's type |
| `forall`, `and-then`, `or-else`, `add-atom`, `remove-atom` | `Bool` |
| `let`, `match`, `sealed`, `progn`, `once`, ... | the type of the value they return |
| `catch`, `eval`, an undeclared function's result | `%Undefined%` |

The merge of alternatives `S1 .. Sn` is the type they agree on (unify to), else
their union `(| S1 .. Sn)`.

### 2.3 Establishment: `S ⊑ T`

`S` establishes `T` when every value of type `S` fits `T`, so that no check is
needed:

- `T` is a variable or a wildcard (`%Undefined%`, `Atom`, `Expression`), or `S`
  is a variable (the value fits every instance), but a wildcard `S`
  establishes nothing else;
- a union `S` establishes `T` if each alternative does; a union `T` is
  established if one of its alternatives is;
- `(List A) ⊑ (List B)` if `A ⊑ B`; a tuple `⊑ (List B)` if each element `⊑ B`;
- an atom or a rigid type (§2.8) establishes only itself;
- tuples and arrows of the same length: element by element.

The variables of `S` are copied first, so that each use of `()` is independent;
a variable of `T` stands for any type.

A *value* is established at `T` by its static type; if it is ground at compile
time, by a check then; and if it is data `(X1 .. Xn)` and `T` a tuple type
`(T1 .. Tn)`, element by element, where a symbol establishes itself, as in the
value relation. This is checking mode for data: the result of
`(= (enqueue $e (queue $in $out $n)) (queue (cons $e $in) $out (+ $n 1)))`
establishes `(queue (List $a) (List $a) Number)` although `queue` has no type.

### 2.4 Consistency: `S ~ T`

Two types are *consistent* (Siek and Taha 2006) unless they disagree where both
are known:

- a variable, a wildcard or a metatype (`Symbol`, `Grounded`, `Variable`) is
  consistent with every type;
- a union `S` if each of its alternatives is consistent with `T`; a union `T`
  if one of its alternatives is consistent with `S`;
- a rigid type `S` (§2.8) only with itself, while every type is consistent
  with a rigid `T`;
- two names if they are equal or may share values (§2.5);
- a name and a tuple if the tuple's head is unknown or one of the name's
  constructors;
- `(List A)` and a tuple if each element of the tuple is consistent with `A`;
- otherwise if they have the same length and are consistent element by
  element. So a primitive type is consistent with nothing else, and a list
  type with no name and no arrow.

Inconsistent types are a *conflict*, a type error at compile time.

### 2.5 Type names are closed

The values of a declared name are the ones declared with it: symbols
`(: s N)` and applications of constructors `(: c (-> ... N))`, a constructor
being a declared function without equations. Two names share values only
through a symbol or constructor declared with both, so `A` and `B` conflict
unless, say, both `(: x A)` and `(: x B)` are declared. This is the
closed-world assumption of logic programming, applied to declarations: a name
has no values that the program does not declare.

The assumption fails when the program adds rules to `get-type`, which can give
any value any type: `examples/types_dependent.metta` makes even numbers an
`EvenNumber`. Defining `get-type` therefore opens every non-primitive name: it
becomes consistent with every type and is checked only at runtime. The
primitive types stay closed, since the value relation decides them without
`get-type`.

### 2.6 Checks

What a runtime check can test of a required type is its *known part*: its type
variables, rigid or not, are unknown there. `(List $a)` is checked as a list,
`(-> $a $b)` as a function of one argument, and a rigid result type not at all
(§4.4). A boundary needs no check when the value is established at this known
part (§2.3).

A check is compiled to an inline test of the common case, falling back to the
value relation: `(number(V) -> true ; typecheck_or_error(V, 'Number'))`, and
for a tuple type the same test on each element of the list.

### 2.7 Calls

A call `(f X1 .. Xn)` of a function with one declaration `(-> A1 .. An R)`:

1. A fresh copy of the declaration is instantiated with what the arguments'
   static types establish, `$a := Number` for an argument `(1 2)` at
   `(List $a)`, before any argument is checked, so that the outcome does not
   depend on the order of the arguments.
2. Each argument passes the boundary at its instantiated type.
3. The call has the type `R` under the instance. Type variables left open are
   unknown; so are those that no argument mentions, which are the function's
   own choice, except in the exact result of a builtin or a constructor:
   `(empty)` fits every type.

A function with several declarations is *overloaded*. The declarations its
arguments may fit, those without a conflict, are kept; if none is, the call is
a compile error. At runtime the arguments must fit one of them before the call
(else `no_matching_overload`), and the arguments and the result must fit one
of them together after it. Tests that the static types establish are left
out, and a test is dropped when one declaration surely fits.

A partial application `(f X1 .. Xk)` checks its `k` arguments against the first
`k` parameter types. A closure call `($f X1 .. Xk)` is checked like a call when
the static type of `$f` is an arrow. When the callee is known only at runtime
(`apply_fn1` .. `apply_fnN`, `reduce`), the known parts of its parameter types
(`checked_params/3`) are checked there: the same check a known call would have
compiled. A constructor's name is a function too: `(map-flat Wrap $xs)` builds
`(Wrap X)` for each element.

A builtin implemented in Prolog (a `native_builtin`: arithmetic, comparisons,
...) gets no argument checks, as it tests its own arguments, but its conflicts
are still errors: `(+ 1 "a")` does not compile. A function imported from
Prolog (`import_prolog_function`) has its result checked when its declared
result type is `Number`, `String` or `Bool`: a foreign declaration is a promise
the compiler cannot verify.

### 2.8 Clauses

A clause `(= (f P1 .. Pn) Body)` is compiled against its *contract*: the
declarations of `f` that its constant head arguments can fit, instantiated by
them. A clause `(= (f 1) 2)` of `(: f (-> $a $a))` is checked as
`(-> Number Number)`, which is also how a specialization's closure arguments
are taken into account.

- With one such declaration the parameters get its types, and the result of
  the body passes the boundary at its result type.
- With several, the clause is compiled unchecked: each call is checked against
  the declarations its arguments fit (§2.7).
- With none, it is a compile error.

The body sees its own declaration from the inside (`body_contract/4`). A type
variable that a parameter type mentions is *rigid*: the caller chooses it, so
all the body knows is that it is some fixed type. A value of a rigid type
cannot be used at any other type, `(+ $x 1)` with `$x : $a` is a conflict, but
any value can be returned at a rigid type: this is the one place where the
checker trusts the program (§4.4). A type variable that only the result
mentions is the function's own choice, and unknown.

`-[det]->` and `-[semidet]->` compile to a cut after the head: the function
commits to the first clause whose head matches.

### 2.9 Patterns

A pattern matched against a value of type `T` (a parameter, a `let`, a `case`
branch) gives its variables the types that `T` gives their positions: the
elements of a `(List E)`, the fields of a constructor application, the
positions of a tuple, also behind the pattern's own tag: `(queue $in $out $n)`
against `(queue (List $a) (List $a) Number)`. Nothing is learned where `T` says nothing. The variable
of `map-atom`, `filter-atom` and `foldl-atom` gets the element type of the list.

### 2.10 Evaluation policy

`Atom` in a declaration is an instruction too. A parameter that every
declaration of the function types `Atom` receives its argument unevaluated, and
a function declared to return `Atom` returns its body as data: an `Atom` result
is the declarative `quote`. This holds for every arrow (v1.1 applied the result
rule to `->` only).

## 3. Generated code

The compiled clauses below are printed by `sh run.sh FILE` (without `-s`).

**Typed code compiles like untyped code.** Both loops compile to the same
clause: the arguments are established `Number`s, so no check is needed, and the
arithmetic is native.

```metta
(: loop (-> Number Number Number))
(= (loop $n $acc) (if (== $n 0) $acc (loop (- $n 1) (+ $acc $n))))
(= (untyped-loop $n $acc) (if (== $n 0) $acc (untyped-loop (- $n 1) (+ $acc $n))))
```
```prolog
loop(A, B, C) :-
    (   A==0
    ->  C=B
    ;   D is A+ -1,
        E is B+A,
        loop(D, E, C)
    ).
'untyped-loop'(A, B, C) :-        % the same body
```

**A value of unknown type is checked where it meets a declared one.** The
result of the untyped `lookup-width` is checked as an argument of `half`, and
as the result of the declared `width-of`:

```metta
(= (lookup-width $k) (match &self (width $k $w) $w))
(: half (-> Number Number))
(= (half $x) (/ $x 2))
(= (half-width $k) (half (lookup-width $k)))
(: width-of (-> Symbol Number))
(= (width-of $k) (lookup-width $k))
```
```prolog
'half-width'(A, B) :-
    'lookup-width'(A, C),
    (   number(C)
    ->  true
    ;   typecheck_or_error(C, 'Number')
    ),
    half(C, B).
'width-of'(A, B) :-
    'lookup-width'(A, B),
    (   number(B)
    ->  true
    ;   typecheck_or_error(B, 'Number')
    ).
```

**Patterns learn from the declaration.** The fields of a `Shape` constructor are
`Number`s, so the arithmetic needs no checks:

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

**Overloads.** `42` fits only the first declaration, so no argument test is
compiled; the body of an overloaded function is not checked against either
declaration, so its result is:

```metta
(: describe (-> Number String))
(: describe (-> String String))
(= (describe $x) (repr $x))
!(describe 42)
```
```prolog
:- findall(A,
           ( describe(42, A),
             (   typecheck_ok(A, 'String')
             ->  true
             ;   throw(error(literal_type_mismatch(A, 'String'), typecheck))
             )
           ),
           _).
```

**Higher-order code.** The generic clause calls its closure through
`apply_fn1`, which checks the callee's parameters if it has declared ones; the
specializer then compiles the call with `(+ 1)` to native arithmetic:

```metta
(: twice (-> (-> $a $a) $a $a))
(= (twice $f $x) ($f ($f $x)))
!(twice (+ 1) 5)
```
```prolog
twice(A, B, C) :-
    apply_fn1(A, B, D),
    apply_fn1(A, D, C).
'twice_Spec_[partial(+,[1])]'(partial(+, [1]), A, B) :-
    C is 1+A,
    B is 1+C.
```

**A conflict stops the compilation**, here because one alternative of an `if` is
a `Number`:

```metta
(: label (-> Shape String))
(= (label $s) (if (== $s (circle 0)) "dot" 0))
```
```
Type error at g3.metta:4 in:
  (= (label $s) (if (== $s (circle 0)) "dot" 0))
... Type conflict: value is constrained as (| String Number) but also required as String
```

## 4. Why the rules are sound

### 4.1 Erasure

Compile a program `P` twice: as usual, and with `--no-type-checks`, giving
`P°`. The two compilations differ only in their checks:

- the runtime checks of boundaries, `(number(V) -> true ; typecheck_or_error(V,
  'Number'))` and `typecheck_or_error(V, T)`;
- the argument and result tests of overloaded calls,
  `(Tests -> true ; throw(...))`;
- the parameter checks of calls through closures and `reduce`
  (`checked_params/3`);
- the type errors raised while compiling.

Everything else, the evaluation policy (`Atom`), the clause commitments, the
specializations and the arithmetic inlining, comes from the declarations alone
and is the same in both. Each check is a goal that either succeeds once, without
binding a variable and without effect, or throws: `typecheck_ok/2` only tests
(its unifications are with fresh variables or under `\+ \+`). Deleting a goal
that succeeds once without bindings or effects changes nothing else in a run.
A run of `P` that raises no type error is one in which every check succeeded,
so `P°` has the same run. ∎

`examples/soundness_matrix.sh` (phase B) runs every example both ways and
compares the results of every run that raises no type error.

### 4.2 Static types are sound

*Claim.* If the compiler gives a value the static type `S`, then at runtime the
value fits `S`, under the trust assumptions of §4.4. *Argument*, by the rule
that gave `S` (§2.2):

- literals, `()`, a function's name: by inspection of the value;
- a symbol with one declared type: `get-type` gives it that type;
- a constructor application: its fields were established at the declared field
  types, and the value relation accepts the application by the declaration;
- other data: each element fits its own static type, by induction;
- a parameter: every caller either established the argument's type or checked
  its known part (§2.6, §2.7), and a call through a closure or `reduce` checks
  it at runtime; the type variables are the caller's instance;
- a call's result: the callee's clauses check their result against its type
  (§2.8), instantiated by the caller's arguments, which is where rigid type
  variables are trusted;
- a pattern variable: it is a part of a value of the pattern's static type;
- `(the T E)`: checked against `T` unless established;
- a merge: each alternative fits its own type, hence the union.

*Claim.* If `S ⊑ T` and a value fits `S`, it fits `T`. *Argument*, by induction
on the rules of §2.3, against the table of §2.1: every rule of `⊑` is one of
the value relation read for all the values of `S`. Data established element by
element fits a tuple type by the tuple row of §2.1, and a ground value fits at
runtime as it did when it was checked at compile time. So a check that the
compiler leaves out, because the value is established at the known part of `T`,
would have succeeded.

`examples/soundness_matrix.sh` (phase A, `--oracle`) compiles every example
with the left-out checks put back in, and requires that none of them fails.

### 4.3 Conflicts

Consistency is the static check of gradual typing (Siek and Taha 2006): the
unknown type `%Undefined%` is consistent with everything, and known types must
agree in every part that both determine. A conflict is the standard static
type error of the discipline.

For the primitive types, the arrows and the closed names a conflict also means
that no value fits both types, since the value relation keeps them apart. A list
type and a name conflict even though PeTTa represents a constructor
application as a list: as in any nominal type system, a value of a name is
used through its name.

### 4.4 Trust

The checker trusts, and does not check:

1. **Builtins implemented in Prolog** (the table in `types.pl`): their results
   have their declared types, and they test their own arguments. SWI-Prolog's
   arithmetic is lax in places: it evaluates a one-character string as its
   character code and `e`, `pi`, `inf` and `nan` as numbers. A typed program
   never reaches these cases with a mistyped value, but untyped code can.
2. **Results at type variables.** Any value can be returned at a rigid type
   variable (§2.8); a result type such as `(List $a)` has its known part
   checked, the list, but not its elements. Polymorphic gradual typing (Ahmed, Jamner, Siek and Wadler
   2017) checks such a value at runtime by *sealing* it, which a Prolog
   representation of values cannot do cheaply. So the result of
   `(: id (-> $a $a))` is trusted to have the caller's type: a body returning
   `5` for `(id "s")` is not detected. Every use of a value of a rigid type
   at another type is rejected (§2.4), so the trust covers only what is
   returned at a type variable.
3. **Foreign results that are not primitive**, which may be opaque Prolog
   terms, and foreign values, which fit every non-primitive type.
4. **Declarations are made before they are relied on.** A file's declarations
   are all read before its functions are compiled, and a function whose own
   declarations change is recompiled; a removed declaration does not recompile
   its callers, and `get-type` rules defined after a function was compiled do
   not reopen the names it was checked against.

Untyped code is not checked at all: a function without a declaration is
dynamically typed.

### 4.5 Polymorphism, unions and names in the literature

- *Consistency* and the unknown type: Siek and Taha, "Gradual Typing for
  Functional Languages", 2006.
- *Rigid type variables*: a type variable is consistent only with itself (and
  the unknown type) inside the function: Ahmed, Jamner, Siek and Wadler,
  "Theorems for Free for Free: Parametricity, With and Without Types", ICFP
  2017. Without sealing, this checker trusts results (§4.4).
- *Result-only type variables* are existential, as Mercury requires them to be
  declared (`some [T]`): the function picks the type, the caller learns nothing.
- *Unions*: the type of a merge is the union of its alternatives, and every
  alternative must fit its use, as in Typed Racket (Tobin-Hochstadt and
  Felleisen 2008) and in set-theoretic gradual types (Castagna and Lanvin,
  ICFP 2017). There is no occurrence typing: `(the T E)` narrows explicitly.
- *Closed type names* are negation as failure (Clark 1978) over declarations.

Making a program's types less precise, replacing a type by `%Undefined%`, never
turns an accepted program into a rejected one, since `%Undefined%` is
consistent with every type, and never turns a run without type errors into one
with errors, since it only removes checks: the static and dynamic gradual
guarantees (Siek, Vitousek, Cimini and Boyland 2015), up to the trust of §4.4
and to `Atom`, which is not a type here but an evaluation policy.

## 5. Changes

### From v1.1

Removed, each with the examples that tested it (§7):

- the `--strict` and `--strict-det` modes;
- determinism checking: validation of `-[det]->` and `-[semidet]->` bodies,
  clause overlap, exhaustiveness, boundness of arguments, the determinism of
  closures and builtins, effect-polymorphic arrows `-[$e]->` (accepted, and
  read as `->`), and the commits v1.1 added at call sites. `-[det]->` and
  `-[semidet]->` still commit a function to its first matching clause;
- type inference for undeclared functions, which are now dynamically typed;
- `Newtype`, `brand`, `Alias` and `Foreign` declarations;
- typed spaces (`SpaceOf`) and match patterns typed by relation schemas;
- flow-sensitive narrowing: branch facts, and unions narrowed by `case`, `if`
  and `=`. `(the T E)` narrows explicitly;
- deferred checks of unbound values, re-run when they are bound;
- trust waivers by library origin;
- contextual typing of `data` and `make-list` elements;
- the builtin registry: a table of 20 builtin signatures replaces it.

Changed:

- **Type errors are errors.** v1.1 sometimes dropped an answer whose overloaded
  result did not fit (`examples/types_nondet.metta`); now it is a type error,
  as everywhere else. Erasure (§4.1) depends on it.
- **Type names are closed** (§2.5). v1.1 let open nominal types overlap and
  turned a variable's conflicting uses into deferred intersection checks; now
  `A` and `B` conflict unless a declared atom has both, or the program defines
  `get-type` rules.
- **Branches are unions** (§2.2): every alternative must fit where the value is
  used.
- **Result-only type variables are existential** (§2.8): v1.1 rejected
  `(: magic (-> $a))` with the body `0`; now `(magic)` is simply of unknown
  type to its callers.
- **`Atom` results** hold the body for every arrow, not only for `->` (§2.10).
- **`catch`** has the unknown type: its result may be an `Error` expression,
  and `if-error` cannot narrow it away.
- **A type error in a `!` expression** ends that expression with an `(Error
  ...)` result and makes the run exit with status 2; a type error in a
  definition still stops the load.
- **`car-atom` of `()`** is `()` again, as in v1.0.6.
- Error messages print values and types as MeTTa terms.

### From v1.0.6

v1.0.6 checked a typed call at runtime only: each argument, and the result,
was tested with `get-type`, and a failed test made the call fail without an
answer. Each declaration of an overloaded function was a separate
alternative, and only `->` arrows were declarations. The chainer cannot be run
on v1.0.6 at all: it relies on semantics added since (the commit of
`-[det]->` among them), and under v1.0.6 `(map-flat internalize-proof-structure
...)` over a one-element list produces answers without end, so the first
`compileadd` never returns.

Compared with v1.0.6 the checker adds compile-time errors, drops the checks it
can prove redundant (v1.0.6's typed numeric loop costs twice its untyped one;
here they compile to the same clause), raises an error where v1.0.6 returned
no answer (erasure), and keeps v1.0.6's runtime relation, `get-type`, for the
types it cannot decide statically.

## 6. Size

| | v1.0.6 | v1.1 | now |
|---|---:|---:|---:|
| `src/*.pl` | 1,229 | 13,661 | 2,595 |
| type checking | ~40 (in the translator) | 10,357 (`src/typecheck*`) + the translator's typing | 423 (`src/types.pl`) + ~80 lines of calls into it and error messages |
| `src/translator.pl` | 475 | 1,566 | 687 |

`src/types.pl` is about 265 lines of code and 115 of comments. The rest of the
growth since v1.0.6 is not type checking: the load cache (`load_cache.pl`),
specialization, `hyperpose`, and the other changes of v1.1, all kept.

Where v1.1's checker went:

| v1.1 | lines | now |
|---|---:|---|
| `type_lang`, `decl_store`, `flags_arrows`: type syntax, declaration store, kinds | 1,194 | the declarations section of `types.pl` |
| `builtin_registry` | 449 | the builtin table |
| `value_checks` | 495 | the value relation (`typecheck_ok/2`) |
| `clause_checks`, typed calls in the translator | 544 + | `clause_contract/6`, `type_call/6`, `type_boundary/4` |
| `inference` | 191 | removed |
| `det_analysis`, `det_proofs`, `det_validate`, `analysis_proofs` | 2,120 | removed; the commit cut is one line of the translator |
| `abstract_domain`, `call_summaries`, `relational_ir`, `ir_analyzer`, `unified_checker_bridge`, `unified_checker_cache` | 4,988 | removed |
| `dependency_graph` | 266 | `recompile_function_clauses/1` and `symbol_use/2` in the translator |
| `oracles`, `typecheck.pl` | 110 | the `--oracle` and `--no-type-checks` flags |

## 7. Tests

`sh test.sh` runs the parser and fold unit tests, every example, the code
generation checks of `examples/type_dispatch_matrix.sh`, and the soundness
oracles of `examples/soundness_matrix.sh`: 291 examples under `--oracle`
(phase A) and 278 compared under `--no-type-checks` (phase B; 13 raise type
errors on purpose and are skipped). It takes about 2 minutes on 4 cores; v1.1's
took about 9.

Of v1.1's 497 examples, 151 tested a removed mechanism and are deleted:

| removed mechanism | examples |
|---|---:|
| determinism checking | 79 |
| `Newtype`, `brand`, `Alias`, `Foreign` | 23 |
| flow-sensitive narrowing | 16 |
| typed spaces | 10 |
| library trust waivers (with `lib_trust_fixture`, `lib_unified_cache_fixture`) | 10 |
| strict modes | 6 |
| deferred checks | 3 |
| inference | 2 |
| `car-atom` of `()` raising | 1 |
| parametric result-only type variables | 1 |

The matrices that drove them (`builtin_registry_matrix.sh`, `fuzz_matrix.sh`,
`lib_trust_matrix.sh`, `typecheck_boundary_matrix.sh`,
`unified_checker_matrix.sh`) are deleted, and `type_dispatch_matrix.sh` and
`soundness_matrix.sh` are rewritten for this checker.

Seven examples changed their expectations: `types_nondet` (an error, not an
empty result), `type_previous_try_coverage` (the static conflict is reported),
`fail_catch_output_mismatch` and `type_runtime_output_fallback` (catch has the
unknown type; the latter now tests the runtime checks of `eval`, untyped
results, closures and `catch`), `strictdet_let_value_cut` and
`strictdet_space_update_payload` (an `Atom` result holds the body; they declare
`%Undefined%` instead), and `strict_contextual_list` (no contextual typing of
`make-list`). The `strict_` and `strictdet_` prefixes of the remaining examples
are historical: they run like all the others.

The chainer's own tests (its `tests/*.metta`, run from its root) give the same
results as on v1.1: the same 370 passing tests in 30 files, and the same two
files that fail to load on both, since they import files that are not where
they look. They run in 19 seconds, against 83 on v1.1.

## 8. Measurements

Inferences, exact, and median CPU seconds, SWI-Prolog 10.1.9 on a 4-vCPU
machine. `measure.pl` (from the review bundle) separates setup, the compilation
of the query and its execution; the v1.1 and current chainer and nilbc runs
were interleaved, 6 of each (18 for nilbc), since times vary by 10% or more from
run to run.

| | v1.0.6 | v1.1 | v1.1 candidate | now |
|---|---:|---:|---:|---:|
| typed numeric loop, 5 × 100,000 | 6,000,125 / 0.30 | 500,119 / 0.013 | 500,119 / 0.015 | 500,119 / 0.013 |
| untyped numeric loop | 3,000,095 / 0.10 | 500,089 / 0.013 | 500,089 / 0.018 | 500,089 / 0.014 |
| nilbc, 20 queries | 291,542,965 / 19.5 | 2,307,804 / 0.48 | 2,307,804 / 0.49 | 2,319,684 / 0.50 |
| nilbc setup | 18,350,330 / 1.16 | 847,672 / 0.09 | 829,173 / 0.09 | 367,937 / 0.06 |
| chainer, 100 queries | does not run | 2,685,672 / 0.62 | 3,546,872 / 1.42 | 2,488,524 / 0.56 |
| chainer setup | | 31,884,900 / 3.05 | 32,112,454 / 3.41 | 4,460,946 / 0.63 |
| chainer peak memory | | 64 MB | 81 MB | 29 MB |

v1.1 cannot load the chainer as released: `if-error` is defined in both
`lib_he` and `lib_roman` with overlapping `-[det]->` clauses. Its chainer
column uses v1.1 with the candidate's `lib_error` (keeping `lib_roman`'s
`(List $a)` result for `\?/`, on which v1.1's type unification loops).

The chainer runs 7% fewer inferences than on v1.1, in 9% less time. nilbc runs
0.5% more, as a variable-headed expression in its proofs goes through
`apply_fn1` before `reduce`, and is within the noise in time: over 18
interleaved runs its median is 3.5% and its fastest run 1.6% slower. Loading the
chainer takes a seventh of v1.1's inferences and a fifth of its time, in less
than half its memory. With `--no-type-checks` the chainer runs 2,458,724
inferences: its checks, at the boundaries between its untyped code and the
typed libraries, cost 1.2%. `examples/tilepuzzle.metta`, an untyped search over
the typed queues of `lib_datastructures`, runs 20,196,335 inferences, against
20,151,892 in v1.1.

## 9. Next steps

- **Determinism**, if wanted, as a separate optional analysis that reports
  `-[det]->` declarations its clauses do not honor, rather than a part of type
  checking. The commit cut stays the only semantics of the arrow.
- **Choice points of folds.** PeTTa asserts clauses dynamically, and SWI-Prolog
  does not index a dynamic two-clause predicate on its third argument, so
  `fold-flat` over a proper list leaves a choice point (v1.1 cut it at call
  sites it proved deterministic). Compiling clauses into static predicates, or
  reordering the arguments of the library's folds, would let first-argument or
  JIT indexing remove it.
- **Results at type variables** could be checked by the caller, where the
  instance is known, for functions whose body returned a value of unknown type
  at a rigid type (§4.4), at the cost of recording that per function.
- **Removed declarations** could recompile their callers, as changed
  declarations recompile the function itself.
