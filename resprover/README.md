# Resolution Theorem Prover

A complete resolution-based SAT solver in MeTTa with redundancy elimination (subsumption, tautology detection).

## Quick Start

```bash
# Run test suite (28 problems, all ≤10 clauses)
./test_suite_small.sh

# Test single problem
./run.sh demos/resprover.metta demos/test_problems/php32.cnf
```

## Features

- ✅ **Binary resolution** with derivation tracking
- ✅ **Forward/backward subsumption** (Vampire-style redundancy elimination)
- ✅ **UNSAT core extraction** (minimal axiom set)
- ✅ **Derivation trace** (step-by-step proof)
- ✅ **SAT detection** via saturation
- ✅ **Clause normalization** (set-based comparison)
- ✅ **Tautology deletion**
- ✅ **Size limits** (max 10 literals/clause, 10k clauses)

## Files

- **resprover.metta** - Main entry point (CNF parser + prover)
- **resolution_prover_with_redundancy.metta** - Core prover logic
- **cnf_parser.pl** - Prolog DIMACS CNF parser
- **test_problems/** - 28 test cases (0-10 clauses)
- **test_suite_small.sh** - Automated test runner

## Test Results: 28/28 Passing ✓

```
contradiction_2                (2  clauses) ✓ UNSAT
simple_unsat_3                 (3  clauses) ✓ UNSAT
modus_ponens_3                 (3  clauses) ✓ UNSAT
pigeonhole_21_unsat            (3  clauses) ✓ UNSAT
binary_counter_unsat_4         (5  clauses) ✓ UNSAT
symmetric_unsat_4              (4  clauses) ✓ UNSAT
xor_unsat_4                    (4  clauses) ✓ UNSAT
horn_unsat_5                   (4  clauses) ✓ UNSAT
tautology_5                    (5  clauses) ✓ UNSAT
resolution_chain_4             (4  clauses) ✓ UNSAT
chain_implications_5           (6  clauses) ✓ UNSAT
transitivity_6                 (6  clauses) ✓ UNSAT
php32                          (9  clauses) ✓ UNSAT
empty_0                        (0  clauses) ✓ SAT
single_unit_1                  (1  clauses) ✓ SAT
simple_sat_2                   (2  clauses) ✓ SAT
pure_literal_sat_2             (2  clauses) ✓ SAT
two_models_sat_2               (2  clauses) ✓ SAT
subsumption_test_3             (2  clauses) ✓ SAT
disjunction_3                  (3  clauses) ✓ SAT
majority_sat_3                 (3  clauses) ✓ SAT
unit_clauses_3                 (3  clauses) ✓ SAT
equivalence_sat_3              (2  clauses) ✓ SAT
diamond_sat_4                  (4  clauses) ✓ SAT
resolution_diamond_6           (4  clauses) ✓ SAT
horn_sat_4                     (4  clauses) ✓ SAT
three_sat_3vars                (5  clauses) ✓ SAT
php22                          (6  clauses) ✓ SAT
```

Run with: `./test_suite_small.sh`

## Performance

| Problem | Clauses | Result | Time | Status |
|---------|---------|--------|------|--------|
| simple_sat_2 | 2 | SAT | < 1s | ✅ |
| simple_unsat_3 | 3 | UNSAT | < 1s | ✅ |
| php22 | 6 | SAT | 0.5s | ✅ |
| php32 | 9 | UNSAT | 1.8s | ✅ |

**Working Range**: 0-10 clauses
**Limitation**: Stack overflow on 50+ clauses (Prolog backtracking explosion)

## Example Output

### UNSAT with Proof
```
$ ./run.sh demos/resprover.metta demos/test_problems/php32.cnf
"UNSAT"

Input clauses used (UNSAT core):
(Clause 0 : (1 2))
(Clause 1 : (3 4))
(Clause 2 : (5 6))
...

Derivation trace:
(1211 . () (resolve 151 456))
(151 . (-3) (resolve 3 76))
...
```

### SAT
```
$ ./run.sh demos/resprover.metta demos/test_problems/majority_sat_3.cnf
"SAT"
```

## How It Works

### Key Technique: Redundancy Elimination

Without redundancy elimination, even simple problems like PHP(3,2) generate clauses indefinitely. With Vampire-style redundancy elimination:

1. **Forward subsumption**: Don't add clauses subsumed by existing ones
2. **Backward subsumption**: Remove existing clauses when better ones arrive
3. **Normalization**: Sort literals for order-independent comparison
4. **Tautology deletion**: Remove trivially true clauses

Result: PHP(3,2) goes from infinite loop to solving in 1.8s\!

### Architecture

```
DIMACS CNF → Prolog Parser → MeTTa Converter → Resolution Engine → Result
                                                      ↓
                                          Redundancy Elimination
                                                      ↓
                                          Proof/Model Extraction
```

## Limitations

**Working range: 0-10 clauses**

Larger problems (50+ clauses) hit stack overflow due to:
- Prolog choicepoint explosion (5M+ choicepoints)
- Non-deterministic clause matching
- No given-clause selection strategy

Future improvements needed:
- Add determinism annotations (once/!)
- Implement given-clause algorithm
- Optimize clause indexing

## References

- Riazanov & Voronkov. "The Design and Implementation of Vampire" (2002)
- Schulz. "System Description: E" (2002)
- Mitchell et al. "Hard and Easy Distributions of SAT Problems" (1992)

## Summary

Complete resolution prover with Vampire-style redundancy elimination.
- **28/28 tests passing** (0-10 clauses)
- Proves UNSAT with derivation traces
- Detects SAT via saturation
- Shows redundancy elimination is essential for practical resolution proving
