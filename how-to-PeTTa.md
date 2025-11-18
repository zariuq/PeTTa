# How to Program in PeTTa (and MeTTa)

> ⚠️ **CRITICAL:** PeTTa's `match` does NOT work with `new-space`! You MUST use &self with tagged atoms. See [Spaces and Match](#spaces-and-match-critical) for details.

> ⚠️ **CRITICAL:** PeTTa does NOT have a `>=` operator! Use `<=` with countdown instead. See [Available Operators](#available-operators-in-petta) for details.

## Table of Contents
1. [Spaces and Match (CRITICAL)](#spaces-and-match-critical)
2. [Critical Rule: Non-Deterministic Evaluation](#critical-rule-non-deterministic-evaluation)
3. [The Fundamental Anti-Pattern: Catch-All Wildcards](#the-fundamental-anti-pattern-catch-all-wildcards)
4. [Performance Patterns (NEW)](#performance-patterns-avoiding-exponential-slowdown)
5. [Available Operators in PeTTa](#available-operators-in-petta)
6. [Correct Patterns for Control Flow](#correct-patterns-for-control-flow)
7. [PeTTa-Specific Features](#petta-specific-features)
8. [Working Examples](#working-examples)
9. [Common Pitfalls and Solutions](#common-pitfalls-and-solutions)

---

## Spaces and Match (CRITICAL)

### ⚠️ PeTTa's `match` Does NOT Work with `new-space`!

**THE PROBLEM:**
In PeTTa, `match` completely fails to find atoms in spaces created with `new-space` and populated with `add-atom`. This is a fundamental PeTTa limitation.

```metta
;; ❌ THIS DOES NOT WORK IN PETTA!
!(bind! &kb (new-space))
!(add-atom &kb (foo bar))
!(match &kb (foo bar) FOUND)  ; Returns nothing! Match is broken!
```

**THE SOLUTION: Use &self with Tagged Atoms**

Instead of creating separate spaces, tag all atoms in `&self` with a space identifier:

```metta
;; ✅ THIS WORKS IN PETTA!
;; Instead of: !(bind! &kb (new-space))
;; Just use &self and tag atoms:

!(add-atom &self (kb (foo bar)))
!(collapse (match &self (kb (foo bar)) FOUND))  ; Returns: (FOUND) ✅
```

### The Tagged Atom Pattern

**Key Rules:**
1. **Use `&self` only** - Don't use `new-space` or `bind!`
2. **Tag all atoms** with a space identifier as the first element
3. **Wrap `match` with `collapse`** to get proper list results
4. **Pattern match returns** `(result)` on success, `()` on failure

**Complete Example:**

```metta
;; Function that manages a "knowledge base" using tagged atoms
(= (add_c $space-tag $tok)
   (case (collapse (match &self ($space-tag (Constant $tok (Type "$c"))) found))
     (((found)
        (Error (Constant $tok) "Already exists"))
      (()
        (let $_ (add-atom &self ($space-tag (Constant $tok (Type "$c"))))
          (Constant $tok (Type "$c")))))))

;; Usage - note we pass 'kb1' as a tag, not a space reference
!(add_c kb1 foo)           ; Adds (kb1 (Constant foo ...)) to &self
!(add_c kb1 foo)           ; Returns error - already exists
!(add_c kb2 foo)           ; Works - different tag/namespace
```

**Why This Works:**
- `&self` is the only space where `match` reliably works in PeTTa
- Tagging creates logical namespaces within `&self`
- `collapse` converts match results to usable lists
- Each "space" is just a different tag prefix

**Case Matching on Results:**
```metta
;; collapse + match returns (value) or ()
(case (collapse (match &self (kb $x) $x))
  ((($value)      ; Matched - $value bound
     (do-something $value))
   (()            ; Empty - no match
     (do-nothing))))
```

See `metamath/add_c.metta` for a complete working example of this pattern.

---

## Critical Rule: Non-Deterministic Evaluation

**MeTTa uses parallel pattern matching, NOT sequential "first match wins"!**

From the MeTTa documentation (minimal-metta.md):
> "This is called non-deterministic evaluation... An interpreter extracts atom and bindings from the plan and evaluates the atom. The result of the operation is a set of pairs."

### What This Means in Practice

When you write multiple pattern-matching clauses for the same function:

```metta
(= (foo 1) result-a)
(= (foo 2) result-b)
(= (foo $_) result-c)   ; DANGER! This matches EVERYTHING including 1 and 2!
```

**ALL matching clauses execute in parallel.** If you call `(foo 1)`, BOTH the first and third clauses match, creating multiple solution paths and non-deterministic behavior.

This is fundamentally different from languages like Haskell, OCaml, or Prolog where pattern matching is sequential and stops at the first match.

---

## The Fundamental Anti-Pattern: Catch-All Wildcards

### NEVER Do This

```metta
;; ❌ BROKEN - creates non-determinism!
(= (complementary (lit $x) (nlit $x)) True)
(= (complementary (nlit $x) (lit $x)) True)
(= (complementary $_ $_) False)  ; Matches EVERYTHING including the above cases!

;; ❌ BROKEN - both clauses match (eq-check a a)
(= (eq-check $x $x) yes)
(= (eq-check $_ $_) no)  ; Also matches ($x $x) case!

;; ❌ BROKEN - wildcard matches Nil too!
(= (is-empty-clause Nil) True)
(= (is-empty-clause $_) False)  ; Matches Nil as well!
```

### Why This Fails

The pattern `(= (func $_ $_) result)` matches **EVERY** two-argument call to `func`, including inputs that also match more specific patterns. This creates parallel execution paths where:

1. The specific pattern returns its result
2. The catch-all pattern ALSO returns its result
3. MeTTa evaluates both paths non-deterministically
4. Your program produces multiple conflicting results

The issue is that `(complementary (lit p) (nlit p))` matches BOTH:
- `(= (complementary (lit $x) (nlit $x)) True)` → returns `True`
- `(= (complementary $_ $_) False)` → ALSO matches, returns `False`

**This paradigm is INVALID in MeTTa.** You cannot use the traditional functional programming pattern of:
- Specific cases first
- Catch-all case last

---

## Performance Patterns: Avoiding Exponential Slowdown

PeTTa's non-deterministic evaluation can amplify performance issues that wouldn't matter in sequential languages. Here are critical patterns learned from implementing a resolution theorem prover.

### ✅ Pattern 1: Skip Self-Operations in Set Iterations

When iterating over a set to combine elements, **skip self-operations** to avoid redundant work:

```metta
;; ❌ SLOW - resolves clause against itself unnecessarily
(= (resolve-against-all $clause Nil) Nil)
(= (resolve-against-all $clause (Cons $other $rest))
   (let $resolvent (resolve $clause $other)
     (if (== $resolvent (no-resolvent))
         (resolve-against-all $clause $rest)
         (Cons $resolvent (resolve-against-all $clause $rest)))))

;; ✅ FAST - skip when same clause
(= (resolve-against-all $clause Nil) Nil)
(= (resolve-against-all $clause (Cons $other $rest))
   (if (== $clause $other)  ; ✅ Skip self!
       (resolve-against-all $clause $rest)
       (let $resolvent (resolve $clause $other)
         (if (== $resolvent (no-resolvent))
             (resolve-against-all $clause $rest)
             (Cons $resolvent (resolve-against-all $clause $rest))))))
```

**Why this matters:** In resolution proving, a clause set of size N generates N² pairs. Skipping self-operations cuts this to N(N-1)/2, **halving the work**.

### ✅ Pattern 2: Early Discard of Invalid Results

**Filter during generation**, not after. Check validity BEFORE adding to results:

```metta
;; ❌ SLOW - generates tautologies then filters later
(= (try-resolve-lit $lit1 (Cons $lit2 $rest2) $orig1 $orig2)
   (if (== (complementary $lit1 $lit2) True)
       (let $rem1 (remove-lit $lit1 $orig1)
         (let $rem2 (remove-lit $lit2 $orig2)
           (append-lits $rem1 $rem2)))  ; Always return, filter later
       (try-resolve-lit $lit1 $rest2 $orig1 $orig2)))

;; ✅ FAST - discard tautologies immediately
(= (try-resolve-lit $lit1 (Cons $lit2 $rest2) $orig1 $orig2)
   (if (== (complementary $lit1 $lit2) True)
       (let $rem1 (remove-lit $lit1 $orig1)
         (let $rem2 (remove-lit $lit2 $orig2)
           (let $resolvent (append-lits $rem1 $rem2)
             (if (== (is-tautology $resolvent) True)  ; ✅ Check NOW
                 (no-resolvent)  ; Discard
                 $resolvent))))  ; Keep
       (try-resolve-lit $lit1 $rest2 $orig1 $orig2)))
```

**Why this matters:** Tautologies (clauses with both `p` and `¬p`) are always true and useless for resolution. Discarding them **immediately** prevents exponential growth of useless clauses.

### ✅ Pattern 3: Deduplication in Iterative Algorithms

When iteratively generating new results, **deduplicate** to prevent exponential accumulation:

```metta
;; ❌ SLOW - keeps duplicates, exponential growth
(= (prove-loop $clauses $all-seen $remaining)
   (if (== (contains-empty $clauses) True)
       (proof-found (- 10 $remaining))
       (if (<= $remaining 0)
           (max-iterations 0)
           (let $new-clauses (resolve-all-pairs $clauses $clauses)
             (prove-loop
               (append-sets $clauses $new-clauses)  ; ❌ No dedupe!
               (append-sets $all-seen $new-clauses)
               (- $remaining 1))))))

;; ✅ FAST - deduplicate new clauses
(= (prove-loop $clauses $all-seen $remaining)
   (if (== (contains-empty $clauses) True)
       (proof-found (- 10 $remaining))
       (if (<= $remaining 0)
           (max-iterations 0)
           (let $new-clauses (resolve-all-pairs $clauses $clauses)
             (let $deduped (dedupe $new-clauses)  ; ✅ Dedupe!
               (prove-loop
                 (append-sets $clauses $deduped)
                 (append-sets $all-seen $deduped)
                 (- $remaining 1)))))))
```

**Implementation of dedupe:**

```metta
(= (member? $x Nil) False)
(= (member? $x (Cons $first $rest))
   (if (== $x $first) True (member? $x $rest)))

(= (dedupe Nil) Nil)
(= (dedupe (Cons $first $rest))
   (if (== (member? $first $rest) True)
       (dedupe $rest)  ; Skip duplicate
       (Cons $first (dedupe $rest))))  ; Keep unique
```

**Why this matters:** Without deduplication, resolution can generate the same clause multiple times per iteration, leading to **exponential** set growth. Deduplication keeps growth **linear** in unique clauses.

### ✅ Pattern 4: Size Limits on Recursive Growth

When recursion can generate unbounded results, **add size caps** to prevent runaway computation:

```metta
;; ❌ DANGEROUS - can explode to millions of clauses
(= (prove-loop $clauses $all-seen $remaining)
   (if (== (contains-empty $clauses) True)
       (proof-found (- 10 $remaining))
       (if (<= $remaining 0)
           (max-iterations 0)
           (let $new-clauses (resolve-all-pairs $clauses $clauses)
             (prove-loop
               (append-sets $clauses $new-clauses)
               (append-sets $all-seen $new-clauses)
               (- $remaining 1))))))

;; ✅ SAFE - cap set size
(= (prove-loop $clauses $all-seen $remaining)
   (if (== (contains-empty $clauses) True)
       (proof-found (- 10 $remaining))
       (if (<= $remaining 0)
           (max-iterations 0)
           (let $size (length $clauses)
             (if (> $size 100)  ; ✅ Size cap!
                 (size-limit-exceeded $size)
                 (let $new-clauses (resolve-all-pairs $clauses $clauses)
                   (prove-loop
                     (append-sets $clauses $new-clauses)
                     (append-sets $all-seen $new-clauses)
                     (- $remaining 1))))))))
```

**Why this matters:** Some problems generate clauses exponentially. A cap prevents **runaway** memory usage and provides a clear failure mode instead of hanging indefinitely.

### Anti-Patterns to Avoid

Based on optimizing a resolution prover from 30s to 17.5s (43% improvement), here are the **poor PeTTa programming patterns** to avoid:

#### ❌ Anti-Pattern 1: No Deduplication in Iterative Algorithms
**Symptom:** Exponential growth of duplicate results
**Fix:** Add `dedupe` after each generation step

#### ❌ Anti-Pattern 2: Self-Operations in Set Iterations
**Symptom:** N² work when only N(N-1)/2 needed
**Fix:** Add `(if (== $x $y) skip-case continue-case)` guard

#### ❌ Anti-Pattern 3: Generate-Then-Filter Instead of Filter-During-Generation
**Symptom:** Creating millions of invalid results only to discard them
**Fix:** Check validity **before** adding to result set

#### ❌ Anti-Pattern 4: No Size Limits on Recursive Growth
**Symptom:** Runaway memory, infinite loops, hangs
**Fix:** Add size/depth caps with clear failure reporting

#### ❌ Anti-Pattern 5: Using `unify` for Sequential Control Flow
**Symptom:** Added overhead from extra pattern matching
**Fix:** Use `if` for simple branching, save `unify` for actual pattern extraction

**Real-world example:** Trying to "flatten" functions with `unify` to reduce clauses made performance **worse** (68s vs 17s). The pattern-matching overhead outweighed any benefit. Domain-specific optimizations (dedupe, tautology check, skip self) gave 43% speedup instead.

### When Optimizations Don't Help

**Failed optimization attempts** from the resolution prover:

1. **Using `unify` to flatten multi-clause functions**: SLOWER (68s vs 17s)
   - PeTTa's pattern matching is already optimized
   - Adding `unify` just adds overhead
   - Only use `unify` when you actually need to **extract** pattern structure

2. **Using `car-atom`/`cdr-atom` on expression atoms `()`**: Infinite loop/hang
   - Expression atoms `()` are NOT the same as `Cons/Nil` lists
   - `car-atom`/`cdr-atom` only work on expression atoms
   - Stick with `Cons/Nil` for proper list operations

**Key lesson:** PeTTa runtime immaturity means it's slower than HE MeTTa for now (1.8x on benchmarks). Focus on **algorithmic** optimizations (dedupe, early discard, skip redundant work), not micro-optimizations.

---

## Available Operators in PeTTa

### ⚠️ CRITICAL: `>=` Does NOT Exist in PeTTa!

**PeTTa has these comparison operators:**
- ✅ `==` - Equality (returns True/False)
- ✅ `<` - Less than (returns True/False)
- ✅ `>` - Greater than (returns True/False)
- ✅ `<=` - Less than or equal (returns True/False)
- ❌ **`>=` - DOES NOT EXIST!** Returns unevaluated expression `(>= x y)`

**Evidence:**
```metta
!(== 5 5)     ; Returns: [True]
!(< 5 10)     ; Returns: [True]
!(> 10 5)     ; Returns: [True]
!(<= 5 10)    ; Returns: [True]
!(>= 10 5)    ; Returns: [(>= 10 5)]  ❌ UNEVALUATED!
```

### Workaround: Use `<=` with Inverted Logic

Instead of count-up with `>=`, use **countdown with `<=`**:

```metta
;; ❌ BROKEN (>= doesn't exist):
(= (loop $iter $max)
   (if (>= $iter $max)
       done
       (loop (+ $iter 1) $max)))

;; ✅ CORRECT (use <= with countdown):
(= (loop $remaining)
   (if (<= $remaining 0)
       done
       (loop (- $remaining 1))))
```

**Real example from working resolution prover:**
```metta
;; Start with max iterations and count DOWN
(= (prove $clauses $max-iter)
   (prove-loop $clauses $clauses $max-iter))

;; Use <= to check if we've run out of iterations
(= (prove-loop $clauses $all-seen $remaining)
   (if (<= $remaining 0)           ; Works!
       (max-iterations 0)
       (prove-loop ... (- $remaining 1))))
```

---

## Correct Patterns for Control Flow

### Pattern 1: Single Clause with `if-then-else`

The safest pattern is to use a **single clause** with explicit `if` statements:

```metta
;; ✅ CORRECT - single clause, explicit conditions
(= (is-empty-clause $clause)
   (if (== $clause Nil)
       True
       False))

;; ✅ CORRECT - nested if for multiple conditions
(= (fib $n)
   (if (< $n 2)
       $n
       (+ (fib (- $n 1))
          (fib (- $n 2)))))

;; ✅ CORRECT - explicit equality checks
(= (factorial $n)
   (if (== $n 0)
       1
       (* $n (factorial (- $n 1)))))
```

### Pattern 2: Multiple Specific Patterns (NO Catch-All)

You can use multiple clauses if they are **completely non-overlapping** and you **DO NOT** include a catch-all:

```metta
;; ✅ CORRECT - specific patterns only, no catch-all
(= (complementary (lit $x) (nlit $x)) True)
(= (complementary (nlit $x) (lit $x)) True)
;; Note: NO third clause! If neither matches, MeTTa returns nothing.

;; ✅ CORRECT - recursive list processing
(= (remove-lit $lit Nil) Nil)
(= (remove-lit $lit (Cons $head $tail))
   (if (== $lit $head)
       $tail
       (Cons $head (remove-lit $lit $tail))))
```

**Key insight:** It's okay for a function to return nothing (fail to match) for some inputs. This is better than creating non-deterministic behavior.

### Pattern 3: Using `unify` for Pattern Matching ✅

The `unify` function provides explicit then/else branches. **Requires**: `!(import! &self lib/lib_he)`

```metta
;; ✅ CORRECT - unify with explicit branches
(= (complementary $lit1 $lit2)
   (unify $lit1 (lit $x)
       ;; Then branch: $lit1 matched (lit $x)
       (unify $lit2 (nlit $x)
           True    ; Both matched
           False)  ; $lit2 didn't match
       ;; Else branch: $lit1 didn't match (lit $x)
       (unify $lit1 (nlit $y)
           (unify $lit2 (lit $y) True False)
           False)))
```

**Verified Working**: 6/6 tests passing in PeTTa. See `UNIFY_TEST_SUMMARY.md` for details.

**Note**: `unify` is a **built-in** operation in HE MeTTa (Rust), but in PeTTa it's implemented in MeTTa code in `lib/lib_he.metta`. Both work identically.

### Pattern 4: Direct `==` Comparison

When you need to check equality, use `==` directly instead of pattern matching:

```metta
;; ✅ CORRECT - direct equality check
(= (find-in Nil $target) no)
(= (find-in (Cons $h $t) $target)
   (if (== $h $target)
       yes
       (find-in $t $target)))

;; Instead of the broken:
;; ❌ (= (eq-check $x $x) yes)
;; ❌ (= (eq-check $_ $_) no)
```

### Pattern 5: `let*` Return Values ✅

**`let*` is built-in and works correctly in both PeTTa and HE MeTTa!**

The body of `let*` (after all bindings) is the return value:

```metta
;; ✅ Direct value return
!(let* (($a 1) ($b 2))
  (+ $a $b))
; Returns: 3

;; ✅ Return from if
!(let* (($x 5))
  (if (> $x 3)
      (result-big)
      (result-small)))
; Returns: (result-big)

;; ✅ Multiple bindings with recursive call
(= (test-pattern $list $count)
  (if (<= $count 0)
      (timeout)
      (if (== $list Nil)
          (saturated)
          (let* (($first (car $list))
                 ($rest (cdr $list))
                 ($processed (process $first)))
            (if (== $processed (stop-signal))
                (found-it)
                (test-pattern $rest (- $count 1)))))))

!(test-pattern Nil 10)
; Returns: (saturated) ✅
```

**Key points:**
- `let*` is **built-in** - no import needed
- Works identically in PeTTa and HE MeTTa (only difference: HE wraps in `[value]`)
- The **last expression** in the `let*` body is the return value
- Works correctly with `if`, recursion, and early returns
- Can bind multiple values sequentially: `(let* (($a 1) ($b 2) ($c 3)) ...)`

### Pattern 6: Side Effects in `let*` and Sequential Execution ✅

**Requires**: `!(import! &self lib/lib_metta4)` for `progn`/`prog1`

#### Side Effects in `let*` Bindings

**CRITICAL FIX:** In PeTTa, the HE MeTTa pattern `(() (expr))` doesn't work. Use `($_  (expr))` instead!

```metta
;; ❌ BROKEN IN PETTA - using () as pattern
!(let*
  (
    ($a 1)
    (() (println! ("Debug: a =" $a)))  ; ❌ Does NOT execute in PeTTa!
    ($b 2)
  )
  (+ $a $b))
; Output in PeTTa: (nothing!)
; Output in HE: ("Debug: a =" 1) ✅

;; ✅ WORKS IN BOTH - using $_ as pattern
!(let*
  (
    ($a 1)
    ($_ (println! ("Debug: a =" $a)))  ; ✅ Executes in both HE and PeTTa!
    ($b 2)
  )
  (+ $a $b))
; Output: ("Debug: a =" 1)
; Returns: 3
```

**Why this works:**
- `()` is an empty constant pattern that can't bind to anything, so PeTTa skips evaluation
- `$_` is a variable that CAN bind, forcing PeTTa to evaluate the expression
- **Both HE and PeTTa support `$_`**, making it the portable solution!

**Alternative variable names:**
```metta
($_ (println! ...))           ; ✅ Underscore (conventional for "ignore")
($ignore (println! ...))      ; ✅ Explicit name
($_temp (println! ...))       ; ✅ Any variable name works
```

**Porting HE code to PeTTa:** Simply replace `(() ` with `($_ ` in all `let*` bindings:
```bash
# Quick fix for porting
sed -i 's/(() /(($_  /g' your_file.metta
```

#### Sequential Execution with `progn` and `prog1`

For multiple sequential operations, use `progn` (return last) or `prog1` (return first):

```metta
;; ✅ progn - executes all, returns LAST value
(= (add-and-report $space-tag $atom)
  (progn
    (println! ("Adding atom:" $atom))     ; Side effect 1
    (add-atom &self ($space-tag $atom))   ; Side effect 2
    (add-atom &self ($space-tag (log added $atom)))  ; Side effect 3
    success))  ; ← Returns this
; Returns: success

;; ✅ prog1 - executes all, returns FIRST value
(= (add-and-return $space-tag $atom)
  (prog1
    $atom                                    ; ← Returns this
    (println! ("Returning:" $atom))          ; Side effect 1
    (add-atom &self ($space-tag $atom))      ; Side effect 2
    (add-atom &self ($space-tag (log added $atom)))))  ; Side effect 3
; Returns: $atom
```

**Key differences:**
- `(progn a b c)` → executes a, b, c → returns c (last)
- `(prog1 a b c)` → executes a, b, c → returns a (first)
- Both work up to 50 arguments
- Both require `!(import! &self lib/lib_metta4)`

**When to use which:**
- Use `progn` when the return value is computed last (e.g., accumulation)
- Use `prog1` when you have the return value first but need side effects after (e.g., logging)
- Use `let*` with `$_` for side effects mixed with bindings

**Real example from metamath/add_f.metta:**
```metta
(= (add_f $space-tag $label $typecode $var $level)
  ...
  (let $hyp ((Label $label) FHyp (FSDepth $level) ...))
    (prog1
      $hyp                           ; Return the hypothesis ← returns this
      (update-flist ...)             ; Side effect 1
      (add-atom &self ... $hyp))))   ; Side effect 2
```

### Pattern 7: Sentinel Values

When you need to distinguish between "no result" and "empty result", use a sentinel value:

```metta
;; ✅ CORRECT - sentinel for "no resolvent found"
(= (try-resolve-lit $lit1 Nil $orig1 $orig2) (no-resolvent))
(= (try-resolve-lit $lit1 (Cons $lit2 $rest2) $orig1 $orig2)
   (if (== (complementary $lit1 $lit2) True)
       ;; Return resolvent (could be Nil = empty clause!)
       (let $rem1 (remove-lit $lit1 $orig1)
         (let $rem2 (remove-lit $lit2 $orig2)
           (append-clause $rem1 $rem2)))
       ;; Keep searching
       (try-resolve-lit $lit1 $rest2 $orig1 $orig2)))

;; Now Nil means "empty clause" and (no-resolvent) means "failed to resolve"
```

---

## PeTTa-Specific Features

### List Operations: `car-atom` and `cdr-atom`

PeTTa uses **regular S-expression lists** `()` with special operations, NOT `Cons/Nil`:

```metta
;; PeTTa list operations (from greedy_chess.metta)
(= (nth $n $list)
   (if (== $n 1)
       (car-atom $list)      ; Get head of list
       (nth (- $n 1) (cdr-atom $list))))  ; Get tail of list

;; Note: Use regular list syntax
!(test (car-atom (a b c)) a)
!(test (cdr-atom (a b c)) (b c))
```

For prover code using `Cons/Nil`, that's a custom data structure, not built-in lists.

### Testing: HE MeTTa (Current Standard)

**Note**: Files in `demos/` use **HE MeTTa** (Hyperon Experimental), not PeTTa Prolog!

Use `assertEqual` and `assertEqualToResult`:

```metta
;; ✅ CORRECT - HE MeTTa syntax
!(assertEqual (fib 10) 55)
!(assertEqual (factorial 5) 120)
!(assertEqualToResult (match &kb (Constant $name $_) $name) ("0" "+" "="))

;; Output: [()] if test passes
```

**Running tests:**
```bash
conda run -n hyperon metta yourfile.metta
```

From `atomops.metta:15`, tests can use various list operations:

```metta
!(test (cons-atom 0 (1 2 3)) (0 1 2 3))
!(test (car-atom (a b c)) a)
!(test (cdr-atom (a b c)) (b c))
```

### Comments

```metta
;; Single-line comment starts with ;;

;; Multi-line comments use the same syntax:
;; Comment line 1
;; Comment line 2
```

### Case Expressions (when available)

```metta
;; case provides pattern matching in a single expression
(= (casetest $x)
   (case $x
     ((4 42)                    ; If $x == 4, return 42
      ($otherpattern 44)        ; If $x matches pattern, return 44
      ($otherother $45))))      ; Else return $45
```

**Note:** `case` is an alternative to nested `if` statements, but the same rule applies: avoid overlapping patterns.

---

## Verified PeTTa Features

**Test Results**: 243/243 tests passing (100%) across 97 examples
**See**: `PETTA_FEATURES_VERIFIED.md` for complete feature list
**See**: `EXAMPLE_TEST_RESULTS.md` for all test results

### Core Operations That Work

✅ **List Operations**: `cons-atom`, `car-atom`, `cdr-atom`, `index-atom`
✅ **Boolean Logic**: `and`, `or`, `not`
✅ **Arithmetic**: `+`, `-`, `*`, `/`, `<`, `>`, `<=`, `==`
✅ **String Comparison**: `@<` (lexicographic, Prolog-style)
✅ **Control Flow**: `if`, `case`, `let`, `let*`, `chain`
✅ **Evaluation**: `call`, `quote`, `eval`, `reduce`, `collapse`
✅ **Spaces**: `new-space`, `add-atom`, `match`, `remove-atom`
✅ **Types**: Type annotations, `get-type`, function types
✅ **Aggregation**: `foldall`, `forall`
✅ **Advanced**: `superpose`, `empty`, `cut`, `repr`, `=alpha`

## Working Examples

### Example 1: Fibonacci (Simple Recursion)

```metta
;; From examples/fib.metta
(= (fib $N)
   (if (< $N 2)
       $N
       (+ (fib (- $N 1))
          (fib (- $N 2)))))

!(test (fib 30) 832040)
```

**Pattern used:** Single clause with `if-then-else`

### Example 2: Factorial (Explicit Equality)

```metta
;; From examples/factorial.metta
(= (facF $n)
   (if (== $n 0)
       1
       (* $n (facF (- $n 1)))))

!(test (facF 10) 3628800)
```

**Pattern used:** Single clause with explicit `==` check

### Example 3: Binary Resolution (NO Catch-All)

```metta
;; From demos/resolution_prover.metta
;; Correct: specific patterns only
(= (complementary (lit $x) (nlit $x)) True)
(= (complementary (nlit $x) (lit $x)) True)
;; NO third clause!

;; List removal with conditional
(= (remove-lit $lit Nil) Nil)
(= (remove-lit $lit (Cons $head $tail))
   (if (== $lit $head)
       $tail
       (Cons $head (remove-lit $lit $tail))))
```

**Pattern used:** Multiple non-overlapping clauses, no catch-all

### Example 4: Empty Clause Detection (Fixed)

```metta
;; ❌ BROKEN VERSION:
;; (= (is-empty-clause Nil) True)
;; (= (is-empty-clause $_) False)  ; Matches Nil too!

;; ✅ FIXED VERSION:
(= (is-empty-clause $clause)
   (if (== $clause Nil) True False))
```

**Pattern used:** Single clause with explicit equality

### Example 5: Clause Equality (Recursive with Base Cases)

```metta
;; Multiple specific patterns, no catch-all
(= (clauses-equal Nil Nil) True)
(= (clauses-equal Nil $_) False)   ; OK because $_ only in ONE position
(= (clauses-equal $_ Nil) False)   ; Different clause from above
(= (clauses-equal (Cons $h1 $t1) (Cons $h2 $t2))
   (if (== $h1 $h2)
       (clauses-equal $t1 $t2)
       False))
```

**Note:** These are DIFFERENT clauses - each has `$_` in a different argument position, so they don't overlap. The dangerous pattern is `(= (func $_ $_) ...)` where BOTH arguments in the SAME clause are wildcards, matching all inputs and creating non-deterministic behavior.

### Example 6: List Operations (from atomops.metta)

```metta
!(test (cons-atom 0 (1 2 3)) (0 1 2 3))  ; ✅
!(test (car-atom (1 2 3)) 1)              ; ✅
!(test (cdr-atom (1 2 3)) (2 3))          ; ✅
!(test (index-atom (1 2 3) 1) 2)          ; ✅
```

**All 9/9 tests pass** - Basic list operations work perfectly

### Example 7: chain - Sequential Binding (from chain.metta)

```metta
!(test (chain (+ 2 4) $n (* 3 $n)) 18)  ; ✅
!(test (chain (+ 1 3) $n (chain (* 2 $n) $m (+ $n $m))) 12)  ; ✅
```

**Pattern used:** `chain` for sequential operations with variable binding

### Example 8: case - Pattern Matching (from case.metta)

```metta
(= (casetest $x)
   (case $x ((4 42)
             ($otherpattern 44)
             ($otherother $45))))

!(test (casetest 5) 44)  ; ✅
```

**Pattern used:** `case` for multi-way branching

### Example 9: collapse - Collecting Results (from collapse.metta)

```metta
!(test (collapse (1 2 3)) ((1 2 3)))  ; ✅
```

**Pattern used:** `collapse` to collect non-deterministic results into a list

### Example 10: Types (from concrete_types.metta)

```metta
(: a A)
(: b B)
(: A Type)

!(test (get-type a) A)     ; ✅
!(test (get-type b) B)     ; ✅
!(test (get-type A) Type)  ; ✅
```

**All 7/7 tests pass** - Type system works correctly

### Example 11: add_c - Metamath Utility (case+match pattern)

```metta
!(import! &self lib/lib_he)

;; Add constant to Metamath knowledge base
;; Pattern: Use case+match instead of nested unify
(= (add_c $space $tok)
   (case (match $space (Constant $tok (Type "$c")) found)
     ((Empty
        (case (match $space (Var $tok $_ (Type "$v")) found)
          ((Empty
             (add-atom $space (Constant $tok (Type "$c"))))
           ($_ (Error (Var $tok) "Active variable")))))
      ($_ (Error (Constant $tok) "Already declared")))))

;; Usage
!(bind! &kb (new-space))
!(add_c &kb foo)           ; Adds constant
!(add_c &kb foo)           ; Returns error - already exists
```

**Pattern used**: `case` + direct `match` instead of nested `unify` calls

**Why this works in PeTTa**:
- ✅ No nested function calls (avoids PeTTa reordering bug)
- ✅ No `%Undefined%` type annotation issues
- ✅ Space passed as parameter (avoids compilation bug)
- ✅ Flattened control flow using `case`

**Why nested `unify` fails in PeTTa**:
- ❌ Nested calls execute in reverse order (bottom-up)
- ❌ `%Undefined%` type breaks `collapse` + `match` combination
- ❌ Side effects (add-atom) happen before checks

**See**: `add_c_petta.metta` for working implementation

---

## Common Pitfalls and Solutions

### Pitfall 1: Using `new-space` with `match`

**Problem:** `match` does NOT work with custom spaces in PeTTa!

```metta
;; ❌ BROKEN - match fails silently!
!(bind! &kb (new-space))
!(add-atom &kb (foo bar))
!(match &kb (foo bar) $x)  ; Returns nothing!
```

**Solution:** Use `&self` with tagged atoms instead

```metta
;; ✅ CORRECT
!(add-atom &self (kb (foo bar)))
!(collapse (match &self (kb (foo bar)) FOUND))  ; Returns: (FOUND)
```

See [Spaces and Match (CRITICAL)](#spaces-and-match-critical) for complete details.

### Pitfall 2: "It Times Out"

**Reality:** Programs often don't time out - they terminate early due to non-deterministic evaluation creating multiple solution paths.

**Symptoms:**
- `println!` at the end DOES execute
- No error messages
- Simply produces no output or wrong output

**Cause:** Catch-all wildcard patterns creating parallel evaluation

**Solution:** Remove all catch-all patterns, use single-clause `if-then-else`

### Pitfall 2: Overlapping Patterns

```metta
;; ❌ BROKEN
(= (process-lit (lit $x)) (positive $x))
(= (process-lit (nlit $x)) (negative $x))
(= (process-lit $_) unknown)  ; Overlaps with above!

;; ✅ CORRECT
(= (process-lit $lit)
   (unify $lit (lit $x)
       (positive $x)
       (unify $lit (nlit $x)
           (negative $x)
           unknown)))
```

### Pitfall 3: Assuming Sequential Pattern Matching

MeTTa is NOT like Haskell or OCaml. Patterns don't match sequentially.

```metta
;; This is NOT "first match wins"!
(= (foo 1) a)
(= (foo 2) b)
(= (foo $_) c)  ; ALL THREE might execute for (foo 1)!
```

### Pitfall 4: Confusing Nothing with False

In MeTTa, a function can:
1. Return `False` (explicit boolean value)
2. Return nothing (no pattern matched)

These are different!

```metta
;; Returns True or nothing (not False!)
(= (complementary (lit $x) (nlit $x)) True)
(= (complementary (nlit $x) (lit $x)) True)

;; To get explicit True/False, wrap in if:
(= (complementary $lit1 $lit2)
   (if (== (comp-helper $lit1 $lit2) True)
       True
       False))
```

### Pitfall 5: Using Pattern Matching for Equality

```metta
;; ❌ BROKEN - pattern matching creates ambiguity
(= (eq-check $x $x) yes)
(= (eq-check $_ $_) no)

;; ✅ CORRECT - explicit comparison
(= (are-equal $a $b)
   (if (== $a $b) yes no))
```

---

## Summary: The Golden Rules

1. **⚠️ CRITICAL: `>=` does NOT exist in PeTTa!** Use `<=` with countdown instead
2. **Avoid catch-all wildcard patterns** like `$_ $_` or `(= (func $_) ...)`
3. **Prefer single-clause definitions** with `if-then-else` for control flow
4. **Use explicit `==` comparisons** instead of pattern matching for equality
5. **Multiple pattern clauses are OK** if they are completely non-overlapping and you omit the catch-all
6. **Use sentinel values** to distinguish "no result" from "empty result"
7. **Remember: ALL matching clauses execute in parallel**, not sequentially
8. **Test with `!(test actual expected)`** to verify behavior
9. **In PeTTa, use `car-atom`/`cdr-atom`** for list operations on regular `()` lists

### Available Comparison Operators (Quick Reference)
- ✅ `==`, `<`, `>`, `<=` - All work correctly
- ❌ `>=` - **Does NOT exist!** Use `(not (< x y))` or countdown with `<=`

---

## PeTTa Libraries

PeTTa includes several powerful libraries for specialized tasks. See `LIBRARY_REFERENCE.md` for complete documentation.

### lib/lib_he.metta - HE MeTTa Compatibility ✅

**Import**: `!(import! &self lib/lib_he)`

Provides functions that are built-in to HE MeTTa but implemented in MeTTa code for PeTTa:

**Key Functions**:
- `unify` - Pattern matching with then/else branches ✅ (6/6 tests passing)
- `assertEqual` - Test assertions (HE style)
- `if-equal` - Conditional based on equality
- `add-reduct` - Add reduced function definition to space
- `if-error` - Error handling
- `is-function` - Type checking for function types

**Example**:
```metta
!(import! &self lib/lib_he)

(hello world)
!(unify &self (hello world) "found" "not-found")  ; Returns: "found"
!(if-equal 5 5 "yes" "no")                         ; Returns: "yes"
```

### lib/lib_resolution.metta - Binary Resolution

**Import**: `!(import! &self lib/lib_resolution)`

Binary resolution for propositional logic in CNF format.

**Key Functions**:
- `resolve` - Binary resolution on two clauses
- `complementary` - Check if literals are complementary
- `dedupe` - Remove duplicates from list

**Example**:
```metta
!(import! &self lib/lib_resolution)

;; Resolve (p ∨ q) with (¬p ∨ r) → (q ∨ r)
!(resolve ((lit p) (lit q)) ((nlit p) (lit r)))
; Returns: (((lit q) (lit r)))
```

### lib/lib_pln.metta - Probabilistic Logic Networks

**Import**: `!(import! &self lib/lib_pln)`

Full PLN inference engine with truth values `(stv $strength $confidence)`.

**Key Functions**:
- `Truth_Deduction`, `Truth_Induction`, `Truth_Abduction` - Syllogistic inference
- `Truth_ModusPonens` - Forward inference
- `Truth_Revision` - Merge conflicting evidence
- `PLN.Derive` - Backward chaining engine
- `PLN.Query` - Query system for specific terms

### lib/lib_nars.metta - NARS Inference

**Import**: `!(import! &self lib/lib_nars)`

NARS (Non-Axiomatic Reasoning System) with NAL-1 through NAL-5 rules.

**Key Functions**:
- NAL-1: Inheritance syllogisms
- NAL-3: Set decomposition
- NAL-5: Higher-order logic (conjunction, implication)
- `NARS.Derive` - Backward chaining engine
- `NARS.Query` - Query system

### lib/lib_mm2.metta - MORK/MM2 Integration

**Import**: `!(import! &self lib/lib_mm2)`

Simplified operators for MORK (Minimal Operational Reasoning Kernel).

**Key Operators**:
- `＋` - Add atom to &mork space
- `－` - Remove atom from &mork space
- `?` - Query/match pattern in &mork space
- `~>` - Add transformation rule and execute

**Example**:
```metta
!(import! &self lib/lib_mm2)

!(＋ (hello world))          ; Add to space
!(? (hello $X) $X)           ; Query: $X = world
!(~> (inc $x) (+ $x 1))     ; Add transformation rule
```

### lib/lib_prolog.metta - Prolog Integration

**Import**: `!(import! &self lib/lib_prolog)`

Import Prolog predicates as MeTTa functions.

**Key Functions**:
- `import_prolog_function` - Import single predicate
- `import_prolog_functions_from_file` - Import multiple from file

### lib/lib_metta4.metta - Procedural Extensions

**Import**: `!(import! &self lib/lib_metta4)`

Adds `progn` and `prog1` for procedural execution (auto-generated for 1-50 arguments).

### lib/lib_llm.metta - LLM Integration

**Import**: `!(import! &self lib/lib_llm)`

Integration with OpenAI GPT API (requires Python and openai package).

**Key Function**:
- `useGPT` - Send prompt to GPT and get response

**See**: `LIBRARY_REFERENCE.md` for complete function signatures and examples.

---

## Further Reading

- **Library Reference:** `LIBRARY_REFERENCE.md` - Complete documentation of all PeTTa libraries
- **Feature Catalog:** `PETTA_FEATURES_VERIFIED.md` - All verified PeTTa features (243/243 tests passing)
- **Example Test Results:** `EXAMPLE_TEST_RESULTS.md` - Results from 97 tested examples
- **Unify Analysis:** `UNIFY_TEST_SUMMARY.md` - Comparison of HE vs PeTTa `unify` implementation
- **PeTTa Examples:** `/examples/` directory - 119 working code patterns chosen by Patrick Hammer
- **MeTTa Documentation:** `hyperon-experimental/docs/minimal-metta.md` - Non-deterministic evaluation semantics

---

## Debugging Checklist

When your MeTTa/PeTTa code fails mysteriously:

- [ ] Do you have ANY catch-all wildcard patterns like `$_ $_`?
- [ ] Are any of your pattern-matching clauses overlapping?
- [ ] Did you assume "first match wins" behavior?
- [ ] Are you using pattern matching where `==` would be clearer?
- [ ] Did you test with `!(test ...)` to verify actual behavior?
- [ ] If using sentinel values, are you checking for them consistently?
- [ ] Are you mixing up `Cons/Nil` (custom structure) with `()` lists (PeTTa built-in)?

**When in doubt: use a single clause with explicit `if (== ...) then else`!**
