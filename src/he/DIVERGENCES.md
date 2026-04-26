# PeTTa HE Divergences

This file records intentional or currently tolerated differences between
PeTTa `--he`, upstream Hyperon Experimental, and the copied HE spec text.

## Registry

| ID | Category | Symptom | Upstream HE | PeTTa `--he` | Spec status | Severity | Remediation |
| --- | --- | --- | --- | --- | --- | --- | --- |
| DIV-001 | arithmetic | Integer quotient/remainder names and sign conventions differ by implementation. | Observed behavior varies; copied spec text is silent here. | Core `%` is existing PeTTa behavior; explicit `math.rem`, `math.mod`, `math.quot`, `math.divmod` are extension surfaces. | Spec silent in copied text. | tolerated | Keep names explicit; do not claim `%` was missing. |
| DIV-002 | extension | PeTTa/CeTTa helper surfaces run where upstream HE reports unresolved modules or raw data. | Often unresolved `str`, `fs`, `system`, `mork`, runtime stats, PathMap, PLN helper imports, imported-bridge probes, or space-backend helpers. | Implements useful compatibility helpers for PeTTa/CeTTa work. | Outside HE-spec core unless separately specified. | tolerated | Keep extension rows classified; do not count them as HE-core conformance failures. |
| DIV-003 | import-compat | Relative, package-style, and registered-root imports resolve differently. | Often rejects relative names as illegal module names. | Resolves relative files and registered local roots for compatibility. | Mostly implementation surface, not core expression semantics. | tolerated | Keep import behavior documented; no strict/additive profile split. |
| DIV-004 | presentation | Same result with different runner formatting, variable names, or singleton-list printing. | Often prints `[x]`, numbered vars, or `GroundingSpace-0x...`. | Often prints `x`, Prolog vars, or local space atoms. | Not semantic. | tolerated | Normalize in oracle reports where safe. |
| DIV-005 | doc-surface | Documentation atoms are exposed differently. | `get-doc` support is incomplete on some lanes. | PeTTa exposes local doc forms. | Documentation surface, not HE evaluator core. | tolerated | Treat as extension/doc compatibility work. |
| DIV-006 | state-surface | State/add-atom operations may print `()` where upstream prints `true`. | Boolean success shape. | Empty tuple success shape in HE profile. | Output-shape/spec ambiguity. | fixed-in-reporting | Runner/oracle now normalize unit-like success so these no longer appear as semantic regressions. |
| DIV-007 | type-behavior | Extra typed checks or dependent-binder support produce additional passing assertions. | Some current upstream lanes lack the newer behavior. | PeTTa `--he` supports the newer behavior. | Type-application checking now follows the copied spec's sequence: argument checks first, return-type match second. | review | The remaining larger audit item is the full `metta` / `interpret_expression` bindings algorithm, not the current corpus-facing typed-call check. |
| DIV-008 | callable-head-gap | Bound callable heads such as `&pow` from `py-atom` should be invokable. | Upstream `py-atom` probe can call through the bound head. | PeTTa `--he` now resolves bound Python callables and direct `py-atom` callable heads through `py_call_callable/3`. | Outside HE-spec core; generic PeTTa interop surface. | fixed | Covered by `tests/he_foreign_callable.metta` and the corpus `foreign_py_simple_probe.metta` lane. |
| DIV-009 | support-more | Some probe lanes produce answers in PeTTa where upstream yields no results. | Returns `[]` / no result. | Returns concrete answers. | Probe/support surface, not HE-spec core. | tolerated | Count as support wins, not semantic regressions. |
| DIV-010 | extension-helper-surface | Extension/support helper surfaces often evaluate more directly in PeTTa than in upstream HE. | Commonly leaves raw helper forms such as `(collect ...)`, `(select ...)`, `(module-inventory!)`, or `(min ...)`. | Often returns the selected/evaluated value or runtime handle directly. | Extension surface outside strict HE core. | tolerated | Report as extension/support observations, not as HE-core cleanup. |

## Arithmetic Remainder And Division

The copied HE spec text does not appear to define integer division, `%`,
`mod`, or remainder sign semantics. PeTTa already had `%`; it was not
missing. `--he` should not claim a written spec requirement for a
particular `%` sign convention.

`--he` exposes explicit arithmetic helpers where names matter:

- `math.rem` / `rem`: Prolog `rem`, dividend-sign remainder.
- `math.mod` / `mod`: Prolog `mod`, divisor-sign modulo.
- `math.quot` / `quot`: integer quotient.
- `math.divmod` / `divmod`: quotient and remainder pair.

These are profile extensions, not evidence that the HE core spec mandates
one remainder convention.

## Profile Extensions

The broad corpus includes PeTTa/CeTTa-facing conveniences such as `str`,
`fs`, `system`, `mork`, runtime stats, module inventory, `select`, and
`search-policy`. They are useful in `--he` experiments, but they should be
kept separate from the HE-spec core claim unless a specific spec clause
requires them.

The full oracle-diff corpus intentionally includes many of those extension
lanes. Upstream HE often reports module-resolution errors for relative
imports such as `./support/...`, `str`, `system`, and workload helper files;
PeTTa `--he` resolves them because the profile is also testing PeTTa/CeTTa
import compatibility. Treat those oracle rows as extension coverage, not
HE-spec core disagreement.

Output shape also differs by runner. Upstream HE often prints a singleton
result as `[x]`; PeTTa `run.sh --he --silent` usually prints `x`. The oracle
diff harness normalizes passing `[()]` and `[True]` to `true`, but it does
not yet fully normalize all singleton-result pretty-printing.

## Corpus Classification

`cetta_tests/profile_he_prime_dependent_binders_compat.metta` is an
obsolete negative-compatibility lane after dependent-binder support was
added. The positive conformance lane is
`cetta_tests/profile_he_prime_dependent_binders.metta`.

`cetta_tests/support/import_parse_fail/module.metta` is a malformed import
fixture used by importer tests. It is not a top-level runnable program in
the HE corpus runner.

`cetta_tests/spec_module_inventory.metta` is a CeTTa administrative
profile-inventory probe. It asks the module-inventory space to contain
CeTTa-specific profile facts such as `(module-profile he-extended)`. That
is useful for CeTTa's own profile bookkeeping, but it is not a PeTTa `--he`
runtime semantic requirement.

## Function Return

The direct-return probe currently matches upstream HE on literal return
payloads:

```metta
(= (id $x) $x)
!(function (return (id 42)))
```

Both return the literal `(id 42)`. Do not classify return-payload evaluation
as a divergence unless a narrower oracle test or spec clause says so.
