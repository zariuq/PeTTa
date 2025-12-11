# Resolution Theorem Prover

A resolution-based SAT/UNSAT prover with Vampire-style redundancy elimination for PeTTa.

## Quick Start

```bash
# Run comprehensive correctness tests (9 problems, all < 10 clauses)
./test_correctness.sh

# Test single problem
ulimit -v 6291456 && ./run.sh demos/resprover.metta demos/test_problems/php32.cnf --silent

# With timing
/usr/bin/time -f "Time: %E | Memory: %M KB" \
    bash -c "ulimit -v 6291456 && ./run.sh demos/resprover.metta problem.cnf --silent"
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

```
demos/
├── README.md                              # This file
├── resolution_prover_with_redundancy.metta  # Core prover engine
├── resprover.metta                        # CLI wrapper with DIMACS parser
├── cnf_parser.pl                          # Prolog CNF parser
└── test_problems/                         # Test suite (9 CNF files)
    ├── simple_unsat_3.cnf                # UNSAT: minimal contradiction
    ├── transitivity_6.cnf                # UNSAT: transitivity chain
    ├── xor_unsat_4.cnf                   # UNSAT: XOR contradiction
    ├── tautology_5.cnf                   # UNSAT: tautology removal test
    ├── php32.cnf                         # UNSAT: Pigeonhole (3,2)
    ├── simple_sat_2.cnf                  # SAT: trivial
    ├── disjunction_3.cnf                 # SAT: simple disjunctions
    ├── unit_clauses_3.cnf                # SAT: all unit clauses
    └── php22.cnf                         # SAT: Pigeonhole (2,2)
```

## Test Suite

All 9 test problems have < 10 clauses and are verified against MiniSat.

### UNSAT Problems (5)

| Problem | Clauses | Description |
|---------|---------|-------------|
| simple_unsat_3 | 3 | {p∨q}, {¬p}, {¬q} |
| xor_unsat_4 | 4 | XOR contradiction |
| tautology_5 | 5 | Tests tautology deletion |
| transitivity_6 | 6 | Transitivity chain |
| php32 | 9 | Pigeonhole: 3 pigeons, 2 holes |

### SAT Problems (4)

| Problem | Clauses | Description |
|---------|---------|-------------|
| simple_sat_2 | 2 | {p}, {q} |
| unit_clauses_3 | 3 | All unit clauses |
| disjunction_3 | 3 | Simple disjunctions |
| php22 | 4 | Pigeonhole: 2 pigeons, 2 holes |

### Run Tests

```bash
# Comprehensive test suite
cd /home/zar/claude/hyperon/PeTTa
./test_correctness.sh

# Expected output:
# Passed: 9
# Failed: 0
# Errors: 0
# ALL TESTS PASSED\! ✓
```

## Performance

| Problem | Clauses | Result | Time | Status |
|---------|---------|--------|------|--------|
| simple_unsat_3 | 3 | UNSAT | < 1s | ✅ |
| php22 | 4 | SAT | 0.5s | ✅ |
| transitivity_6 | 6 | UNSAT | < 1s | ✅ |
| php32 | 9 | UNSAT | 1.8s | ✅ |

**Working Range**: < 10 clauses  
**Stack Overflow**: 15-20 clauses (PeTTa/Prolog limitation)

## Example Output

### UNSAT with Proof
```
UNSAT

Input clauses used (UNSAT core):
Clause 0 : (1 2)
Clause 1 : (3 4)
Clause 2 : (5 6)
...

Derivation trace:
(636 . () (resolve 151 456))
(151 . (-3) (resolve 3 76))
...
```

### SAT
```
SAT

Variable assignments:
()
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

- **Stack overflow** on 15+ clauses due to PeTTa/Prolog deep recursion
- **No given-clause algorithm** (resolves everything at once)
- **No literal ordering** (Vampire uses ordered resolution)
- **Naive data structures** (O(n²) subsumption checks)

## References

- Riazanov & Voronkov. "The Design and Implementation of Vampire" (2002)
- Schulz. "System Description: E" (2002)
- Mitchell et al. "Hard and Easy Distributions of SAT Problems" (1992)

## Credits

Implements modern ATP techniques from Vampire/E theorem provers for the PeTTa platform.
Demonstrates that redundancy elimination is essential - pure resolution is unusable even on small problems\!
