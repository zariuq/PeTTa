# Metamath Verifier - PeTTa Implementation

PeTTa port of the Metamath proof verifier, adapted from the HE MeTTa implementation.

## Directory Structure

```
metamath/
├── mmverify-utils_petta.metta   # Main verifier (641 lines, all-in-one, self-contained)
├── README.md                     # This file
├── tests/                        # Test files (74 files)
├── demos/                        # Demo scripts (15 files)
├── working/                      # Working implementations (7 files)
└── archive/                      # Old/debug files

```

## Main Files

### mmverify-utils_petta.metta
Complete, self-contained Metamath verifier implementation for PeTTa with all functions:
- **Utility functions**: matchc, to-list, flatten-list, etc.
- **Frame management**: push-frame, pop-frame
- **Metamath operations**: add_c, add_v, add_f, add_e, add_d, add_a, add_p
- **DV checking**: check_dvs, find_vars, check_dv_pairs
- **Proof verification**: verify, treat_assertion, treat_step

**Import:** `!(import! &self ../lib/lib_he)`

All 641 lines are needed - this is a complete, production-ready implementation.

## Key Differences from HE MeTTa

### 1. File-Relative Imports ✅ (NEW!)
```metta
; PeTTa now supports file-relative imports!
!(import! &self ../lib/lib_he)  ✅ Works!
```

### 2. progn/prog1 Built-In ✅ (NEW!)
No need to import lib_metta4 - these are now built-in to PeTTa!

```metta
; OLD (no longer needed):
; !(import! &self ../lib/lib_metta4)

; NEW (built-in):
!(progn
  (println! "First")
  (println! "Second")
  "result")  ; Returns "result"
```

### 3. Tagged Atom Pattern for Spaces
PeTTa's `match` doesn't work with `new-space`. Use tagged atoms in `&self` instead:

```metta
; ❌ Broken in PeTTa:
!(bind! &kb (new-space))
!(match &kb (foo bar) FOUND)  ; Returns nothing!

; ✅ Works in PeTTa:
!(add-atom &self (kb (foo bar)))
!(collapse (match &self (kb (foo bar)) FOUND))  ; Returns (FOUND)
```

### 4. Side Effects in let*
Use `$_` pattern instead of `()`:

```metta
; ❌ Broken in PeTTa:
!(let* ((() (println! "debug"))) ...)

; ✅ Works in PeTTa:
!(let* (($_ (println! "debug"))) ...)
```

## Running Tests

All tests now use correct file-relative imports and can be run from the PeTTa root directory.

### Individual Test
```bash
cd /home/zar/claude/hyperon/PeTTa
./run.sh metamath/tests/test_tier1_utils_petta.metta --silent
```

### All Tests (from PeTTa root)
```bash
cd /home/zar/claude/hyperon/PeTTa
for f in metamath/tests/test_*.metta; do
  echo "=== $(basename $f) ==="
  ./run.sh "$f" --silent
done
```

### Running a Demo
```bash
cd /home/zar/claude/hyperon/PeTTa
./run.sh metamath/demos/demo0_petta.metta --silent
```

## Working Implementations (working/)

Standalone implementations of individual Metamath operations:

- **add_c.metta** - Add constant
- **add_v.metta** - Add variable
- **add_f.metta** - Add floating hypothesis
- **add_e.metta** - Add essential hypothesis
- **add_d.metta** - Add disjoint variable constraint
- **push-frame.metta** - Frame management
- **add_c_he.metta** - HE MeTTa version for comparison

Each file is self-contained and demonstrates the PeTTa patterns for that operation.

## Demo Files (demos/)

### Proof Demonstrations
- **demo0_petta.metta** - Basic Metamath proof example
- **miu_petta.metta** - MIU formal system
- **disjoint2_petta.metta** - DV constraint checking

### Variations
- Multiple versions showing evolution of implementation
- Compare `_debug`, `_full`, `_minimal` versions

## Test Files (tests/)

74 test files covering:

### Core Functionality
- **test_tier1_utils_petta.metta** - Utility functions
- **test_frame_management_petta.metta** - Frame operations
- **test_substitution_petta.metta** - Substitution engine

### Individual Operations
- **test_add_[cvfed]_petta.metta** - Test each add_* operation
- **test_disjoint_vars_petta.metta** - DV checking

### Integration Tests
- **test_treat_assertion_petta.metta** - Full assertion handling
- **test_treat_hypothesis_petta.metta** - Hypothesis handling

### Language Features
- **test_let_star_*.metta** - let* behavior
- **test_progn.metta** - Sequential execution
- **test_println_*.metta** - Side effects

## Comparison with HE MeTTa

### HE MeTTa Location
`/home/zar/claude/hyperon/metamath/mmverify/`

### Key Files Correspondence

| PeTTa | HE MeTTa | Notes |
|-------|----------|-------|
| mmverify-utils_petta.metta | mmverify-utils.metta | Main verifier |
| tests/ | tests/ | Test suite |
| demos/disjoint2_petta.metta | tests/test_dv_*.metta | DV checking |

## Migration from HE MeTTa

To port an HE MeTTa test to PeTTa:

1. **Change imports:**
   ```metta
   ; HE:
   !(import! &self mmverify-utils)

   ; PeTTa:
   !(import! &self ../mmverify-utils_petta)
   ```

2. **Fix space operations:**
   - Replace `new-space` + `match` with tagged atoms in `&self`
   - Wrap `match` with `collapse`

3. **Fix side effects:**
   - Change `(() expr)` to `($_ expr)` in let* bindings

4. **Remove lib_metta4:**
   - `progn`/`prog1` are built-in now!

## Documentation

- **PeTTa How-To**: `/home/zar/claude/hyperon/PeTTa/how-to-PeTTa.md`
- **HE MeTTa How-To**: `/home/zar/claude/hyperon/how-to-MeTTa.md`
- **Relative Imports**: `PETTA_RELATIVE_IMPORTS_IMPACT.md` (in HE repo)

## Recent Changes

### 2025-11-20: Import Path Fixes
- Fixed all 50+ test files to use correct relative imports
- Fixed all 14 demo files to use correct relative imports
- Tests now use: `!(import! &self ../mmverify-utils_petta)`
- Demos now use: `!(import! &self ../mmverify-utils_petta)`
- Removed redundant `lib_he` imports (mmverify-utils_petta already imports it)
- All tests and demos verified working ✅

### 2025-11-20: Structure Cleanup
- Organized 74 test files into `tests/`
- Moved 15 demo files to `demos/`
- Moved 7 working implementations to `working/`
- Archived debug files to `archive/`
- Created comprehensive README.md

### 2025-11-20: PeTTa Updates (upstream)
- ✅ File-relative imports now work!
- ✅ `progn`/`prog1` built-in
- ✅ Backward compatible API

### 2025-11-19: DV Checking
- Implemented and tested DV constraint checking
- Multiple test files in demos/

## Next Steps

1. **Port DV test suite** from HE MeTTa (9 comprehensive tests)
2. **Create test runner** similar to HE's `test_mmverify.py`
3. **Add full proof examples** beyond demo0

## References

- Metamath specification: http://us.metamath.org/downloads/metamath.pdf
- HE MeTTa verifier: `/home/zar/claude/hyperon/metamath/mmverify/`
- PeTTa documentation: `/home/zar/claude/hyperon/PeTTa/how-to-PeTTa.md`
