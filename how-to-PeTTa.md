# How to Program in PeTTa (and MeTTa)

> ⚠️ **CRITICAL:** PeTTa's `match` does NOT work with `new-space`! You MUST use &self with tagged atoms. **However**, `bind!` with `new-state` works fine! See [Spaces and Match](#spaces-and-match-critical) for details.

> ⚠️ **CRITICAL:** PeTTa does NOT have a `>=` operator! Use `<=` with countdown instead. See [Available Operators](#available-operators-in-petta) for details.

> ⚠️ **DEBUG TIP:** "Timeout" might be silent failure, not hanging! Add `!(println! "DEBUG: checkpoint")` BEFORE suspect code to verify it runs. See [DEBUGGING_GUIDE.md](./DEBUGGING_GUIDE.md) for full details.

## Table of Contents
1. [Spaces and Match (CRITICAL)](#spaces-and-match-critical)
2. [Critical Rule: Non-Deterministic Evaluation](#critical-rule-non-deterministic-evaluation)
3. [The Fundamental Anti-Pattern: Catch-All Wildcards](#the-fundamental-anti-pattern-catch-all-wildcards)
4. [Performance Patterns (NEW)](#performance-patterns-avoiding-exponential-slowdown)
5. [Available Operators in PeTTa](#available-operators-in-petta) - Including soft cut `*->` (NEW)
6. [Correct Patterns for Control Flow](#correct-patterns-for-control-flow)
7. [PeTTa-Specific Features](#petta-specific-features) - Including lambdas `|->` (NEW)
8. [Testing and Project Conventions](#testing-and-project-conventions)
9. [Verified PeTTa Features](#verified-petta-features) - Including operator checking (NEW)
10. [Working Examples](#working-examples)
11. [Common Pitfalls and Solutions](#common-pitfalls-and-solutions)

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

**⚠️ IMPORTANT: States Work Fine with `bind!`**

Unlike spaces, **states DO work with `bind!` in PeTTa**:

```metta
;; ✅ THIS WORKS IN PETTA!
!(bind! &fd (new-state 0))       ; States work with bind!
!(get-state &fd)                  ; Returns: 0
!(change-state! &fd 42)
!(get-state &fd)                  ; Returns: 42
```

**Summary:**
- ❌ `!(bind! &space (new-space))` - **BROKEN** - use tagged atoms in &self instead
- ✅ `!(bind! &state (new-state value))` - **WORKS** - use freely!

### The Tagged Atom Pattern

**Key Rules:**
1. **Use `&self` only for spaces** - Don't use `new-space` or `bind!` with spaces
2. **Tag all atoms** with a space identifier as the first element
3. **Wrap `match` with `collapse`** to get proper list results
4. **Pattern match returns** `(result)` on success, `()` on failure
5. **States are fine** - `bind!` with `new-state` works normally

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

### Using `$_` for "Don't Care" Values

**`$_` is just a variable name** - it works like any other variable (`$x`, `$y`), but signals you don't care about the value.

```metta
;; ✅ Use $_ for single "don't care" values
(= (fol-is-var (Var $_)) true)           ; Works fine - one variable
(= (get-first (Cons $x $_)) $x)          ; Ignore tail

;; ❌ BROKEN - reusing same variable name twice means "must be equal"!
(= (occurs (Var $_) (Const $_)) false)   ; FAILS - requires both $_ equal!
(= (mgu $_ $_) None)                     ; FAILS - requires both args equal!

;; ✅ CORRECT - use different names for different values
(= (occurs (Var $_x) (Const $_c)) false) ; Each $_ unique
(= (mgu $_1 $_2) None)                   ; $_1 and $_2 are different
```

**The rule:** Using the same variable name twice (whether `$_`, `$x`, or anything) creates an **equality constraint**. Use `$_1`, `$_2`, `$_3` when you have multiple "don't care" values.

### NEVER Do This (Catch-All Patterns)

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

### Boolean Values: Lowercase Only

**Use `true`/`false` (lowercase), not `True`/`False`:**
```metta
;; ❌ Capitals are just symbols, not booleans
(if (== $x True) ...)    ; Won't match comparison results

;; ✅ Lowercase works
(if (== $x true) ...)    ; Matches (< 5 10) → true
```

### Soft Cut Operator `*->` (NEW)

**PeTTa now has a soft cut operator** `*->` for conditional execution with committed choice:

```metta
;; ✅ Use soft cut for type checking with fallback
(= (process-value $val $type)
   ('get-type'($val, $type) *->
       (process-typed $val $type)
     ; (else-branch)))

;; Equivalent to: "if the goal succeeds, commit to this branch"
;; Used in translate_args_by_type for type validation
```

**When to use:**
- Conditional execution where success should commit to a branch
- Type checking with fallback behavior
- Pattern matching with conditional continuation

**Implementation:** `*->` is Prolog's soft cut (if-then-else without full commitment), integrated into PeTTa's translator for use in type system operations.

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

**Note**: `progn` and `prog1` are built-in to PeTTa - no import needed!

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

**⚠️ CRITICAL: Cannot Reuse `$_` in the Same `let*` Block!**

In PeTTa, you **MUST use unique variable names** for each binding. Reusing `$_` will cause the function to return `()` instead of the expected result!

```metta
;; ❌ BROKEN IN PETTA - reusing $_ causes failure!
(= (broken-function $kb $stmt)
  (let* (
    ($result1 (computation-1))
    ($_ (side-effect-1))        ; First use of $_
    ($_ (side-effect-2))        ; ❌ Reusing $_ breaks everything!
    ($final (computation-2))
  )
  $final))  ; Returns () instead of $final value!

;; ✅ CORRECT - use unique variable names
(= (working-function $kb $stmt)
  (let* (
    ($result1 (computation-1))
    ($_1 (side-effect-1))       ; ✅ Unique name
    ($_2 (side-effect-2))       ; ✅ Different name
    ($final (computation-2))
  )
  $final))  ; Returns $final correctly!
```

**Real-world example that failed:**
```metta
;; This pattern from make_assertion returned () due to $_ reuse:
($_ (map-atom $e_hyps_toks $tok (add-mand-var $kb $tok)))
($_ (map-atom $stmt $tok (add-mand-var $kb $tok)))        ; ❌ Reused $_
($_ (collapse (match &self ($kb (MandVar $var)) ...)))    ; ❌ Third reuse!

;; Fix: Use $_1, $_2, $_3
($_1 (map-atom $e_hyps_toks $tok (add-mand-var $kb $tok)))
($_2 (map-atom $stmt $tok (add-mand-var $kb $tok)))       ; ✅ Unique
($_3 (collapse (match &self ($kb (MandVar $var)) ...)))   ; ✅ Unique
```

**Alternative variable names:**
```metta
($_1 (println! ...))          ; ✅ Numbered underscores (recommended)
($_2 (println! ...))          ; ✅ Clear sequence
($ignore1 (println! ...))     ; ✅ Explicit numbered names
($_temp (println! ...))       ; ✅ Any unique variable name works
```

**Porting HE code to PeTTa:**
1. Replace `(() ` with `($_N ` where N is a unique number for each binding
2. Manual inspection required - automatic replacement is not safe due to numbering requirement

```bash
# Step 1: Find all (() patterns (for manual review)
grep -n '(() ' your_file.metta

# Step 2: Manually replace with $_1, $_2, $_3, etc.
# No safe automated solution - each must be uniquely numbered!
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
- Both are built-in to PeTTa - no import needed

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

### Lambda Expressions (NEW)

**PeTTa now supports lambda expressions** using the `|->` syntax for anonymous functions with closure support:

```metta
;; ✅ Lambda syntax with closure
(= (make-adder $n)
   (|-> ($x) (+ $n $x)))  ; Captures $n from environment

!(let $add5 (make-adder 5)
  ($add5 3))  ; Returns: 8

;; ✅ Lambda with multiple arguments
(= (make-calculator $op)
   (|-> ($a $b) ($op $a $b)))

!(let $multiply (make-calculator *)
  ($multiply 6 7))  ; Returns: 42
```

**Key features:**
- Syntax: `(|-> (args...) body)`
- Supports closure over variables from outer scope
- Generates readable names (`lambda_1`, `lambda_2`, etc.) via `next_lambda_name/1`
- Implemented in `src/translator.pl`

**When to use lambdas:**
- Passing functions as arguments
- Creating function factories (closures)
- Callbacks and higher-order functions

**Current code patterns work well without lambdas** - use them only when closures or function factories are needed. For simple transformations like `map-atom`, the existing variable pattern syntax (`$x`, `$tok`) remains clearer.

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

**⚠️ Warning:** The `.` dot notation (e.g., `($h . $t)`) is Lisp/Scheme syntax and does NOT work reliably in PeTTa. Use `car-atom`/`cdr-atom` for expression atom lists, or `Cons/Nil` for proper list data structures.

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

## Testing and Project Conventions

### PeTTa's Native Test Function

**PeTTa has a built-in `!(test <actual> <expected>)` function - use it!**

```metta
;; ✅ Use PeTTa's native test - clean and simple
!(test (+ 1 2) 3)
!(test (collapse (map-pairs (a b) (x y) make-pair))
       ((((a x) (a y)) ((b x) (b y)))))

;; Returns: true (on success)
;; Fails with error message if values don't match
```

**Note:** PeTTa's `test` function is implemented as a special form in the translator (`src/translator.pl`), providing proper Context parameter handling for file-relative imports. It evaluates the expression, collects all results via `findall`, and compares against the expected value using `test/3`.

**DON'T redefine your own test function:**
```metta
;; ❌ Unnecessary - PeTTa already has this!
(= (test $name $actual $expected)
  (if (== $actual $expected)
    (progn (println! (✅ $name passed)) True)
    (progn (println! (❌ $name failed)) False)))
```

**When to use PeTTa's native test:**
- ✅ For unit tests in test files
- ✅ For inline verification during development
- ✅ When you want automatic pass/fail checking
- ✅ In examples and documentation

**Comparison with HE MeTTa:**
- **HE MeTTa**: Uses `assertEqual` which passes silently `[()]`
- **PeTTa**: Uses `!(test ...)` which returns `true` on success
- Both are built-in, no imports needed

### File Naming Conventions

**Use `_petta` suffix when maintaining both PeTTa and HE MeTTa versions:**

```bash
# ✅ Clear which implementation
my_module_petta.metta        # PeTTa version
my_module.metta              # HE MeTTa version

# When both versions coexist in same directory
test_utils_petta.metta       # PeTTa tests
test_utils.metta             # HE tests
```

**Why use `_petta` suffix?**
- Makes implementation choice explicit
- Allows both versions to coexist
- Makes PeTTa-specific code easy to find via grep
- Prevents confusion about which runtime to use

### `let*` Best Practices

**`let*` works great for regular sequential bindings! ✅**

```metta
;; ✅ Clean, readable, works perfectly
(= (process-data $input)
  (let* (($parsed (parse $input))
         ($validated (validate $parsed))
         ($transformed (transform $validated))
         ($result (finalize $transformed)))
    (output $result)))

;; Much better than nested let:
;; ❌ Ugly nested let version:
(= (process-data $input)
  (let $parsed (parse $input)
    (let $validated (validate $parsed)
      (let $transformed (transform $validated)
        (let $result (finalize $transformed)
          (output $result))))))
```

**Only ONE pattern is broken:** The `(() side-effect)` pattern for ignored bindings.

```metta
;; ❌ BROKEN in PeTTa (but works in HE)
(let* (($a 1)
       (() (println! $a))    ; ❌ Won't execute!
       ($b 2))
  (+ $a $b))

;; ✅ WORKS in both PeTTa and HE
(let* (($a 1)
       ($_ (println! $a))    ; ✅ Executes correctly
       ($b 2))
  (+ $a $b))
```

**Guidelines:**
- ✅ **Use `let*`** for clean sequential bindings (much better than nested `let`)
- ✅ **Use `$_`** (not `()`) for side effects in bindings
- ✅ **Use `progn`/`prog1`** when you have multiple statements without intermediate bindings
- ❌ **Avoid deeply nested `let`** - use `let*` instead!

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

### Operator Checking in `reduce` (NEW)

**PeTTa now prevents operators from being called as regular predicates** in `reduce/2`:

```prolog
% In src/translator.pl - prevents misuse of operators
reduce([F|Args], Out) :-
    nonvar(F), atom(F), fun(F)
    -> length(Args, N),
       Arity is N + 1,
       ( current_predicate(F/Arity),
         \+ (current_op(_, _, F), Arity =< 2)  % ✅ Operator check!
         -> append(Args,[Out],CallArgs),
            Goal =.. [F|CallArgs],
            catch(call(Goal),_,fail)
          ; Out = partial(F,Args) )
```

**What this does:**
- Checks if `F` is both a registered predicate AND an operator
- Prevents operators (`+`, `-`, `*`, `/`, etc.) from being called via `reduce`
- Ensures operators are only used in their proper syntactic position
- Avoids confusion between function application and operator usage

**Why it matters:**
- Type safety - operators must be used correctly
- Better error messages - catches misuse early
- Consistent semantics - operators behave as expected

This feature was integrated from the main branch during the merge with mmverify.

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

### Pitfall 2: Pattern Definitions Don't Auto-Evaluate ⚠️

**Problem:** You define data with `=` and expect it to evaluate automatically, but it remains an unevaluated symbol.

```metta
;; ❌ WRONG EXPECTATION - Pattern doesn't evaluate
(= my-data (Data ABC))

!(process my-data)
;; Passes the SYMBOL my-data, not (Data ABC)!
;; Output: (Processed my-data)  <-- symbol, not data!
```

**Cause:** **Atom types in MeTTa DO NOT get evaluated automatically.** This is standard MeTTa semantics in both HE MeTTa and PeTTa. When you write `(= name value)`, you're defining a pattern/atom type, not a variable.

**Solution 1:** Use inline data

```metta
!(process (Data ABC))  ; ✅ Direct data works!
```

**Solution 2:** Define as a zero-argument function (recommended for reusable data)

```metta
;; ✅ CORRECT - Zero-argument function
(= (my-data) (Data ABC))

!(process (my-data))  ; Function call evaluates to (Data ABC)
```

**Solution 3:** Define data inline within your function

```metta
;; ✅ RECOMMENDED PATTERN for complex workflows
(= (test-with-data)
   (let $data (cons-atom (A) (cons-atom (B) ()))  ; Inline definition
     (let $result (process $data)
        (println! (:: "Result:" $result)))))

!(test-with-data)
```

**Comparison: Patterns vs Functions vs Inline**

| Syntax | Evaluates? | Use Case |
|--------|-----------|----------|
| `(= name value)` | ❌ No (atom type) | Pattern matching, types |
| `(= (name) value)` | ✅ Yes (when called) | Reusable evaluated data |
| `(inline value)` | ✅ Always | Direct immediate data |

**Verified behavior (both HE MeTTa and PeTTa):**

```metta
(= test-pattern (Data ABC))
(= (test-function) (Data ABC))

!(println! test-pattern)           ; Prints: test-pattern (symbol!)
!(println! (test-function))        ; Prints: (Data ABC) ✅
!(println! (Data ABC))             ; Prints: (Data ABC) ✅
```

**Direct function calls: `!(function-name)` behavior differs between implementations**

**HE MeTTa 0.2.8**: Direct calls work and return the value in bracket notation:

```metta
(= (get-data) (Data ABC))

!(get-data)                    ; ✅ Returns: [(Data ABC)]
!(println! (get-data))         ; ✅ Prints: (Data ABC)
```

**PeTTa**: Use explicit `println!` for clear output:

```metta
(= (get-data) (Data ABC))

!(get-data)                    ; ⚠️ Output unclear/mixed
!(println! (get-data))         ; ✅ Clean: (Data ABC)
```

**Recommendation**: For code that works in both implementations, use `println!` explicitly for clear, consistent output formatting.

**Real example from PeTTaRes superposition prover:**

```metta
;; ✅ Data defined inline - works correctly!
(= (test-contradiction)
   (let $axioms (cons-atom
                  (Clause (((⩳ (Fun P ((Fun a ()))) true) true)))  ; Inline
                  (cons-atom
                    (Clause (((⩳ (Fun P ((Fun a ()))) true) false)))  ; Inline
                    ()))
     (let $result (prove $axioms (FIFO))
       (if (== $result (UNSAT))
           (println! "✅ Detected contradiction!")
           (println! (:: "❌ Expected UNSAT, got:" $result))))))

!(test-contradiction)  ; Works! Prints success message
```

**Key takeaway:** This is NOT a bug - it's standard MeTTa semantics! Use functions `(= (name) ...)` or inline data, not patterns `(= name ...)`.

### Pitfall 3: "It Times Out"

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

### Pitfall 6: Using `(list ...)` Syntax

**⚠️ CRITICAL:** PeTTa does NOT have a `list` function! The syntax `(list 1 2 3)` returns **unevaluated** `(list 1 2 3)`, not a proper list `(1 2 3)`.

**Problem:**
```metta
;; ❌ BROKEN - list is not a function in PeTTa!
!(let $my-list (list 1 2 3)
  (println! $my-list))
; Output: (list 1 2 3)  ← Unevaluated! Not a proper list!

;; This will fail mysteriously:
!(let $my-list (list (Clause ...) (Clause ...))
  (car-atom $my-list))    ; Returns: list  ← Wrong!
```

**Solution: Use `cons-atom` chains**
```metta
;; ✅ CORRECT - explicit cons-atom chains
!(let $my-list (cons-atom 1 (cons-atom 2 (cons-atom 3 ())))
  (println! $my-list))
; Output: (1 2 3)  ← Proper list! ✅

;; For clause sets:
!(let $clause-set (cons-atom (Clause (((⩳ (Fun P ((Fun a ()))) true) true)))
                   (cons-atom (Clause (((⩳ (Fun Q ((Fun b ()))) true) true)))
                              ()))
  (car-atom $clause-set))    ; Returns: (Clause ...) ✅
```

**Why This Matters:**
- List operations like `car-atom`, `cdr-atom`, and custom recursion will fail
- Tests will hang or produce no output when operating on unevaluated `(list ...)` expressions
- PeTTa's list pattern matching expects proper cons structures `(head . tail)` notation

**Real-World Example (PeTTaRes Phase 4):**
```metta
;; This caused 6 tests to fail with "no output" (hanging):
!(let $clause-set (list (Clause ...) (Clause ...))  ; ❌ BROKEN
  (forward-subsume $new-clause $clause-set))         ; Hangs!

;; Fixed by using cons-atom:
!(let $clause-set (cons-atom (Clause ...)          ; ✅ CORRECT
                   (cons-atom (Clause ...)
                              ()))
  (forward-subsume $new-clause $clause-set))        ; Works! ✅
```

**Note:** Unlike HE MeTTa which may have built-in `list`, PeTTa requires explicit construction using `cons-atom`.

---

## Summary: The Golden Rules

1. **⚠️ CRITICAL: `>=` does NOT exist in PeTTa!** Use `<=` with countdown instead
2. **⚠️ CRITICAL: Cannot reuse `$_` in the same `let*` block!** Use `$_1`, `$_2`, `$_3`, etc. for unique bindings
3. **⚠️ CRITICAL: `(list ...)` is NOT a function in PeTTa!** Use `cons-atom` chains to build proper lists
4. **Avoid catch-all wildcard patterns** like `$_ $_` or `(= (func $_) ...)`
5. **Prefer single-clause definitions** with `if-then-else` for control flow
6. **Use explicit `==` comparisons** instead of pattern matching for equality
7. **Multiple pattern clauses are OK** if they are completely non-overlapping and you omit the catch-all
8. **Use sentinel values** to distinguish "no result" from "empty result"
9. **Remember: ALL matching clauses execute in parallel**, not sequentially
10. **Test with `!(test actual expected)`** to verify behavior
11. **In PeTTa, use `car-atom`/`cdr-atom`** for list operations on regular `()` lists

### Available Comparison Operators (Quick Reference)
- ✅ `==`, `<`, `>`, `<=` - All work correctly
- ❌ `>=` - **Does NOT exist!** Use `(not (< x y))` or countdown with `<=`

---

## PeTTa Libraries

PeTTa includes several powerful libraries for specialized tasks. See `LIBRARY_REFERENCE.md` for complete documentation.

### Import Resolution (File-Relative Paths)

**As of November 2025**, PeTTa imports are **file-relative**, resolving paths relative to the importing file's directory (not the main script).

**How it works:**
```metta
; File: demos/my_prover/main.metta
!(import! &self ../lib/lib_he)        ; Resolves relative to demos/my_prover/
!(import! &self helpers/util)         ; Resolves to demos/my_prover/helpers/util.metta
```

**Rules:**
1. **Relative paths** (no leading `/`) resolve relative to the importing file's directory
2. **Absolute paths** (leading `/`) resolve from filesystem root
3. **File extension** `.metta` is added automatically

**Example Project Structure:**
```
PeTTa/
├── lib/
│   ├── lib_he.metta          # Base libraries
│   └── lib_resolution.metta
├── demos/
│   ├── tptp/
│   │   ├── solver.metta      # Can import ../../lib/lib_he
│   │   └── helpers/
│   │       └── cnf.metta     # Can import ../../../lib/lib_he
│   └── examples/
│       └── test.metta        # Can import ../../lib/lib_he
```

**Benefits:**
- Nested projects can organize imports cleanly
- Libraries can be placed anywhere in the directory tree
- Import statements remain valid when moving file groups together

**Backward Compatibility:**
All existing import patterns work unchanged - imports from `lib/` to `examples/` continue to work as before.

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

### lib/lib_prolog.metta - Prolog Integration ✅

**Import**: `!(import! &self lib/lib_prolog)`

Import Prolog predicates as MeTTa functions for powerful term manipulation and comparison.

**Key Functions**:
- `import_prolog_function` - Import single Prolog predicate
- `import_prolog_functions_from_file` - Import multiple predicates from file
- `import_prolog_functions_from_module` - Import all from Prolog module

**Critical Use Case: Term Ordering with `@<`**

Prolog's `@<` operator provides **standard term ordering** - a total ordering on all terms that is:
- **Deterministic**: Same terms always compare the same way
- **Lexicographic**: Follows standard dictionary ordering
- **Complete**: Works on any Prolog terms (atoms, numbers, compounds)

**Example: Using `@<` for Sorting**
```metta
!(import! &self lib/lib_prolog)
!(import_prolog_function @<)

;; Use @< for term comparison
!(println! (@< a b))          ; true (a comes before b)
!(println! (@< b a))          ; false
!(println! (@< P Q))          ; true (P comes before Q)
!(println! (@< 1 2))          ; true (numbers ordered numerically)

;; Perfect for implementing sort/comparison functions
(= (symbol-less-than $s1 $s2)
   (@< $s1 $s2))

;; Now you have deterministic ordering!
!(println! (symbol-less-than foo bar))  ; false (foo > bar lexicographically)
!(println! (symbol-less-than bar foo))  ; true (bar < foo)
```

**Real-World Example: PeTTaRes Superposition Prover**

Problem: Needed deterministic literal sorting for clause normalization in theorem prover.

Solution:
```metta
!(import! &self lib/lib_prolog)
!(import_prolog_function @<)

;; Replace stub comparison with Prolog's standard ordering
(= (symbol-less-than $s1 $s2)
   (@< $s1 $s2))

;; Now normalization is deterministic:
;; normalize(P(a) | Q(b)) = normalize(Q(b) | P(a))  ✅
```

**Result**: Fixed non-deterministic sorting, all tests passing!

**Other Useful Prolog Predicates**:
- `@>` - Greater than in standard ordering
- `@=<` - Less than or equal
- `@>=` - Greater than or equal
- `compare` - Three-way comparison (returns <, =, or >)

**When to Use `@<`**:
- ✅ Sorting terms for canonical representation
- ✅ Implementing total orderings (KBO, LPO, etc.)
- ✅ Building discrimination trees or indices
- ✅ Comparing complex structured terms
- ✅ Any time you need deterministic, stable comparison

**Why Not Implement Your Own?**
- Prolog's `@<` is **battle-tested** (decades of use)
- **Optimized** in C for performance
- **Handles all edge cases** (variables, numbers, atoms, compounds)
- **Standard** - matches behavior across Prolog systems

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

### ~~lib/lib_metta4.metta~~ - Procedural Extensions (OBSOLETE)

**Status**: Obsolete - `progn` and `prog1` are now built-in to PeTTa.

Previously provided `progn` and `prog1` for procedural execution (auto-generated for 1-50 arguments).
These functions are now implemented directly in PeTTa's translator (`src/translator.pl`).

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

## Constants and Special Symbols in PeTTa

### Boolean Constants: `true` vs `$true`

**⚠️ CRITICAL:** In PeTTa, `$true` and `$false` are **logic variables**, NOT constants!

```metta
;; ❌ WRONG - $true is a logic variable
!(println! (:: "$true =" $true))    ; Output: (:: $true = $_39086) ← Variable!

;; ✅ CORRECT - Use lowercase without $
!(println! (:: "true =" true))      ; Output: (:: true = true) ✅
```

**The Problem:**
When you use `$true` in clauses, PeTTa binds it to internal variable identifiers like `$_XXXX`:

```metta
;; ❌ This will fail mysteriously
(= (my-function)
   (Clause (((⩳ (Var X) (Var X)) false) ((⩳ (Fun P ()) $true) $true))))

;; What actually gets stored:
;; (Clause (((⩳ (Var X) (Var X)) false) ((⩳ (Fun P ())) $_1032) $_1032))
```

**The Solution:**
Always use lowercase `true` and `false` without the `$` prefix:

```metta
;; ✅ Correct boolean constants
(= (my-function)
   (Clause (((⩳ (Var X) (Var X)) false) ((⩳ (Fun P ()) true) true))))

;; Comparison tests
!(== true true)        ; → true  ✅
!(== $true $true)      ; → false ❌ (different variables each time!)
```

**Why This Matters:**
- Clauses with `$true` won't match expected patterns
- Tests comparing boolean values will fail
- Substitutions applied to clauses will produce unexpected results

**Example from PeTTaRes Superposition Prover:**
```metta
;; Using $true caused 5 tests to fail with mysterious silent errors
;; Changing to true fixed all of them immediately

;; Before (broken):
(Clause (((⩳ (Var X) (Var Y)) $true)))    ; Becomes (... $_1234)

;; After (working):
(Clause (((⩳ (Var X) (Var Y)) true)))     ; Stays as intended
```

### Unicode Symbols for Domain Separation

When building theorem provers or systems with rich syntax, avoid collision between meta-level operators (MeTTa's `=`) and object-level operators (your logic's equality).

**Problem: Symbol Collision**
```metta
;; ❌ Using = for both MeTTa definitions AND equality atoms
(= (equal-atom $x $y) (= $x $y))    ; AMBIGUOUS! Which = is which?

;; MeTTa evaluates the inner = before you can use it
!(let $lit (= (Var X) (Var Y))
  (println! $lit))                  ; Output: false ← Evaluated! Not what we want!
```

**Solution: Unicode Operators**
Use Unicode symbols for object-level syntax to avoid collision:

```metta
;; ✅ Clear separation
;; MeTTa meta-level: =, if, let, case
;; Logic object-level: ⩳ (U+2A73) for equality atoms

(= (superposition-into-literal $s $t $lit)
   (case $lit
     ((((⩳ $lhs $rhs) true)           ; ← ⩳ is data, not evaluation!
       (let $subst (mgu $s $lhs)
         ...)))))

;; Now we can build/manipulate equality atoms as data:
!(let $atom ((⩳ (Var X) (Fun a ())))  ; Create equality atom
  (println! $atom))                    ; Output: ((⩳ (Var X) (Fun a ()))) ✅
```

**Recommended Unicode Operators:**
- `⩳` (U+2A73) - Equals sign above tilde - for equality atoms
- `≠` (U+2260) - Not equal - for disequality
- `→` (U+2192) - Rightwards arrow - for implications
- `∀` (U+2200) - For all - for universal quantification
- `∃` (U+2203) - There exists - for existential quantification

**How to Type Unicode in Editors:**
- **Emacs**: `C-x 8 RET` then type the hex code or name
- **Vim**: Insert mode, `Ctrl-V u` then type hex code
- **VS Code**: Install "Unicode Math Input" extension
- **Copy-paste**: Keep a reference file with commonly used symbols

**Example: Full ATP Implementation**
```metta
;; Term representation
(= (my-term) (Fun f ((Var X))))

;; Atoms using Unicode
(= (my-atom) (⩳ (Fun f ((Var X))) (Fun g ((Var Y)))))

;; Rules using Unicode
(= (my-rule) (∀ X (→ (⩳ X X) true)))

;; No collision with MeTTa's = operator!
(= (process-atom $atom)    ; MeTTa definition
   (case $atom
     (((⩳ $lhs $rhs)        ; Pattern match on object-level equality
       (apply-superposition $lhs $rhs)))))
```

---

## Debugging Checklist

When your MeTTa/PeTTa code fails mysteriously:

- [ ] **Are you using `$true`/`$false` instead of `true`/`false`?** (PeTTa treats `$X` as logic variables!)
- [ ] **Are you reusing `$_` in the same `let*` block?** (PeTTa-specific - causes return value to become `()`)
- [ ] **Are you using `(list ...)` syntax?** (PeTTa doesn't have a `list` function - use `cons-atom` chains!)
- [ ] Do you have ANY catch-all wildcard patterns like `$_ $_`?
- [ ] Are any of your pattern-matching clauses overlapping?
- [ ] Did you assume "first match wins" behavior?
- [ ] Are you using pattern matching where `==` would be clearer?
- [ ] Did you test with `!(test ...)` to verify actual behavior?
- [ ] If using sentinel values, are you checking for them consistently?
- [ ] Are you mixing up `Cons/Nil` (custom structure) with `()` lists (PeTTa built-in)?
- [ ] **Are meta-level and object-level operators colliding?** (Consider Unicode separation)

**When in doubt: use a single clause with explicit `if (== ...) then else`!**
