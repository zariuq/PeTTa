# Resolution Prover for PeTTa

A resolution-based SAT solver in MeTTa with redundancy elimination.

## Quick Start

```bash
cd /home/zar/claude/hyperon/PeTTa
./run.sh resprover/resprover.metta resprover/benchmarks/01_modus_ponens_3cl_unsat.cnf --silent
```

## Files

```
resprover/
├── resprover.metta                      # Main prover (entry point)
├── resolution_prover_with_redundancy.metta  # Core resolution engine
├── cnf_parser.pl                        # DIMACS CNF parser
├── benchmarks/                          # 13 verified test problems
│   ├── 01_modus_ponens_3cl_unsat.cnf   # Classic logic (3 clauses)
│   ├── 02_xor_4cl_unsat.cnf            # XOR constraint (4 clauses)
│   ├── ...                              # More UNSAT problems
│   ├── 09_contradiction_50cl_unsat.cnf  # Largest UNSAT (50 clauses)
│   ├── 10_horn_4cl_sat.cnf             # Horn clauses SAT (4 clauses)
│   ├── ...                              # More SAT problems
│   └── 13_custom_25cl_sat.cnf          # Largest SAT (25 clauses)
└── archive/                             # Additional test problems (not staged)
```

## Features

- Binary resolution with derivation tracking
- Forward/backward subsumption (redundancy elimination)
- Tautology deletion
- UNSAT core extraction
- Clause size limits (10 literals max)

## Example Output

### UNSAT with proof:
```
"UNSAT"

Input clauses used (UNSAT core):
(Clause 0 : (1 2))
(Clause 1 : (-1 2))
...

Derivation trace:
(4 . () (resolve 2 3))
(2 . (2) (resolve 0 1))
...
```

### SAT:
```
"SAT"
```

## Performance

| Problem Type | Max Clauses | Time | Status |
|-------------|------------|------|---------|
| Simple UNSAT | 1-10 | <1s | ✅ |
| Complex UNSAT | 10-30 | 1-5s | ✅ |
| Large UNSAT | 50 | ~1s | ✅ |
| Structured SAT | 25 | 1-2s | ✅ |
| Random SAT | 20+ | - | ❌ Stack overflow |

**Memory Limit**: Always run with 6GB limit:
```bash
ulimit -v 6291456 && ./run.sh resprover/resprover.metta problem.cnf --silent
```

## Limitations

- Random SAT problems >20 clauses cause stack overflow
- Problems >50 clauses may overflow (depends on structure)
- No unit propagation or clause learning

## Benchmark Problems

### UNSAT (9 problems, 3-50 clauses):
- Modus ponens, XOR, transitivity
- Pigeonhole problems
- Contradictions, mutex constraints

### SAT (4 problems, 4-25 clauses):
- Horn clauses, diamond structures
- 3-SAT, custom structured problems

Run any benchmark:
```bash
./run.sh resprover/resprover.metta resprover/benchmarks/<filename> --silent
```