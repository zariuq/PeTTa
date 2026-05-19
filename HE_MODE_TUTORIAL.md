# PeTTa `--he` Mode Tutorial

This tutorial demonstrates PeTTa's `--he` mode and the PeTTa-to-HE translator
on examples where the translation boundary is visible.

Run all commands from the PeTTa repository root.

```bash
cd /path/to/PeTTa
```

Generated `.metta` files are input data for the runtime.  Run them with
`./run.sh` or `./run.sh --he`; do not execute them as shell scripts.

## 1. Start With An Explicit Lowering

Run the PeTTa source example:

```bash
./run.sh examples/peano.metta --silent
```

Expected shape:

```text
is 301, should 301. ...
[True]
```

Run the generated HE-facing artifact:

```bash
./run.sh --he examples/he_translated/peano_he.metta --silent
```

Expected shape:

```text
is 301, should 301. ...
[True]
```

Inspect the source and target around the test:

```bash
sed -n '20,28p' examples/peano.metta
sed -n '1,16p' examples/he_translated/peano_he.metta
```

The source uses a compact PeTTa-style count:

```metta
!(test (length (collapse (demo-peano 300))) 301)
```

The HE-facing artifact makes the collection and count explicit:

```metta
!(test (let $__tr_tuple_1 (collapse (demo-peano 300))
         (size-atom $__tr_tuple_1))
       301)
```

The generated program exposes the count as an explicit HE-facing computation.

## 2. Regenerate That Artifact Yourself

The translator is maintained outside this PeTTa profile tree.  In the workspace
layout used by these examples it is available as `../translators`; if your
checkout puts it somewhere else, set `TRANSLATORS_DIR` first.

```bash
TRANSLATORS_DIR=${TRANSLATORS_DIR:-../translators}
mkdir -p .he-logs/tutorial
"$TRANSLATORS_DIR/translate.sh" petta2he \
  examples/peano.metta \
  .he-logs/tutorial/peano_he.metta
```

Inspect and run the regenerated artifact:

```bash
sed -n '1,16p' .he-logs/tutorial/peano_he.metta
./run.sh --he .he-logs/tutorial/peano_he.metta --silent
```

Expected shape:

```text
is 301, should 301. ...
[True]
```

## 3. Look At A Compatibility Boundary

Quote/eval/reduce are places where PeTTa and HE-like runtimes can differ in
visible behavior.  This example is a PeTTa-compatibility check rather than a
backend-agnostic HE-core example.

```bash
./run.sh examples/callquoteevalreduce.metta --silent
./run.sh --he examples/he_translated/callquoteevalreduce_he.metta --silent
```

Expected shape for each run:

```text
is ..., should ...
is ..., should ...
is ..., should ...
is ..., should ...
[True]
[True]
[True]
[True]
```

Inspect the translation:

```bash
sed -n '1,24p' examples/he_translated/callquoteevalreduce_he.metta
```

Look for:

```metta
(= (quoted-syntax (quote $expr)) $expr)
(unquote (quote (fib 5)))
```

`quoted-syntax` is a translator helper for preserving PeTTa-visible quote
behavior.  `unquote (quote ...)` is the explicit HE-facing evaluation request
used by this compatibility artifact.  These forms are helper/profile surfaces,
not HE core.

## 4. Compare Hyperpose Targets

`hyperpose` is a PeTTa parallel nondeterminism surface.  The default portable
translation lowers it to `superpose`; the preserve-hyperpose target keeps it
for runtimes that intentionally support it.

Inspect the source and the two generated targets:

```bash
sed -n '1,35p' examples/hyperpose_primes.metta
sed -n '1,18p' examples/he_translated/hyperpose_primes_he_sequential.metta
sed -n '1,18p' examples/he_translated/hyperpose_primes_he_parallel.metta
```

In the sequential artifact, look for:

```metta
(superpose ...)
```

In the parallel artifact, look for:

```metta
(hyperpose ...)
```

The sequential file is the portable lowering.  The parallel file targets an HE
runtime with `hyperpose` support.

## 5. Check Nondeterministic Shape

HE core does not guarantee a portable order for every nondeterministic result.
This PeTTa `--he` example checks multiplicity and the profile's observed order.
Portable programs should avoid depending on order unless their target profile
declares it.

```bash
./run.sh --he examples/he_translated/ifcasenondet_he.metta --silent
```

Expected shape:

```text
is (a b a), should (a b a). ...
is (a b a), should (a b a). ...
[True]
[True]
```

Inspect the translated file:

```bash
sed -n '1,20p' examples/he_translated/ifcasenondet_he.metta
```

## 6. Understand `test` And Quiet Assertions

Generated translations preserve source `test` by default because PeTTa `test`
prints the actual/expected comparison as part of its observable behavior.

```bash
./run.sh --he examples/he_translated/peano_he.metta --silent
```

Expected shape:

```text
is 301, should 301. ...
[True]
```

`assertEqualToEval` is still available as a quiet helper for explicit
HE-facing profile tests:

```bash
./run.sh --he tests/he_assert_equal_to_eval_surface.metta --silent
```

Expected shape:

```text
[True]
...
```

Neither PeTTa `test` nor `assertEqualToEval` is HE core.  Another HE
implementation may leave the form as data unless the helper is supplied or the
test is lowered further to core forms.  The portability checker reports that
situation as a translator-helper surface, not as a runtime failure.

## 7. Compare A Performance-Sensitive Example

The translated `fib` example should be both correct and fast under `--he`.

```bash
/usr/bin/time -f 'wall=%e rss=%M exit=%x' \
  ./run.sh examples/fib.metta --silent

/usr/bin/time -f 'wall=%e rss=%M exit=%x' \
  ./run.sh --he examples/he_translated/fib_he.metta --silent
```

Expected shape:

```text
is ..., should ...
[True]
wall=...
```

Exact timings vary by machine.  The correctness output matters first; speed is
only meaningful after the translated artifact still passes.

## 8. Run The Full Correctness And Budget Survey

Use this when you want the broad corpus result rather than individual examples.

```bash
TIMEOUT_SECONDS=60 \
WITNESS_TIMEOUT_SECONDS=20 \
HE_SURVEY_OVERWRITE=1 \
./tests/tools/run_translator_survey.sh
```

Then summarize the performance budget margins:

```bash
tests/tools/summarize_he_translation_budget.awk \
  .he-logs/he_translation_bench.tsv
```

The budget formula is:

```text
he_wall <= default_wall * 2.23 + 0.25s
```

Current expected headline:

```text
pure_portable_translated_passes: 100
pure_portable_he_runtime_gap_core: 0
pure_portable_he_runtime_extension_gap: 0
pure_portable_translator_gap_core: 0
pure_portable_perf_budget_gap: 0
```

The gap directory should be empty:

```bash
find .he-logs/he_translation_gaps -maxdepth 1 -type f | wc -l
```

Expected output:

```text
0
```

## 9. Optional Cross-Engine Portability Check

If CeTTa and an upstream HE `metta` executable are available, run:

```bash
HE_METTA_BIN=/path/to/metta \
TIMEOUT_SECONDS=30 \
tests/tools/check_generated_he_portability.sh --limit 12
```

The script writes a TSV under `.he-logs/`.  The key categories are:

| Category | Meaning |
| --- | --- |
| `portable_exact` | PeTTa `--he`, CeTTa, and upstream HE agree exactly. |
| `translator_helper_surface` | The generated file uses a source-compatibility or assertion helper that another engine leaves as data. |
| `same_elsewhere_diff_from_petta` | CeTTa and upstream agree with each other but differ from PeTTa `--he`. |
| `cross_engine_split` | CeTTa and upstream both ran, but do not agree exactly. |
| `survey_out_of_scope` | The generated file is present, but its source is outside the pure-portable survey lane. |

This check is deliberately stricter than the PeTTa `--he` internal correctness
survey.  It is for understanding portability boundaries, not for replacing the
main 100-example correctness gate.

## 10. What To Read Next

- `specs/petta-he-compatibility-profile.md`
- `specs/he-native-backend-contracts.md`
- `../translators/specs/he-petta-translation-semantics.md`
- `src/he/DIVERGENCES.md`
- `tests/tools/run_translator_survey.sh`
- `tests/tools/check_generated_he_portability.sh`
