#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "$0")" && pwd)
ROOT=$(cd -- "$SCRIPT_DIR/../.." && pwd)
SPEC_MD="$ROOT/specs/petta-he-compatibility-profile.md"
OUT_PDF="${1:-$ROOT/specs/petta-he-compatibility-profile.pdf}"
LOG_DIR="$ROOT/.he-logs"

need_cmd() {
    command -v "$1" >/dev/null 2>&1 || {
        printf 'ERROR: required command not found: %s\n' "$1" >&2
        exit 2
    }
}

need_cmd pandoc
need_cmd pdflatex

latest_corpus_log=$(ls -1t "$LOG_DIR"/petta_he_corpus_*.log 2>/dev/null | head -1 || true)
latest_suite_log=$(ls -1t "$LOG_DIR"/he_profile_suite_*.log 2>/dev/null | head -1 || true)

if [ -z "$latest_corpus_log" ]; then
    printf 'ERROR: no corpus log found under %s\n' "$LOG_DIR" >&2
    exit 2
fi

severity_tsv=$(grep '^SEVERITY_TSV ' "$latest_corpus_log" | tail -1 | cut -d' ' -f2- || true)
if [ -z "$severity_tsv" ] || [ ! -f "$severity_tsv" ]; then
    printf 'ERROR: could not resolve severity TSV from %s\n' "$latest_corpus_log" >&2
    exit 2
fi

summary_tmp=$(mktemp "$ROOT/specs/.he_profile_render.XXXXXX.md")
cleanup() {
    rm -f "$summary_tmp"
}
trap cleanup EXIT

corpus_summary=$(sed -n '/^PeTTa --he — /,$p' "$latest_corpus_log")
strict_frontier=$(cat "$severity_tsv")
generated_at=$(date -u '+%Y-%m-%d %H:%M:%SZ')

{
    cat "$SPEC_MD"
    cat <<EOF

## Appendix A. Generated State Snapshot

This appendix is generated from the latest guarded PeTTa HE logs on the local
machine.  It is intended to keep the PDF aligned with the real measured state
without requiring anyone to hand-edit the profile text.

Generated at: \`$generated_at\`

Latest guarded corpus log: \`${latest_corpus_log#$ROOT/}\`

Latest guarded severity TSV: \`${severity_tsv#$ROOT/}\`
EOF
    if [ -n "$latest_suite_log" ]; then
        cat <<EOF

Latest guarded local suite log: \`${latest_suite_log#$ROOT/}\`
EOF
    fi
    cat <<'EOF'

### A.1 Current Measured State

```text
EOF
    printf '%s\n' "$corpus_summary"
    cat <<'EOF'
```

### A.2 Strict Frontier

```tsv
EOF
    printf '%s\n' "$strict_frontier"
    cat <<'EOF'
```

### A.3 Development Notes

- The strict HE lane currently treats `test_no_return_error.metta` as an
  upstream-oracle quirk: PeTTa keeps the spec-shaped `NoReturn` result rather
  than copying the current upstream leak of a fresh variable.
- Canonical `cetta_tests/he_*.metta` mirror copies were removed from storage so
  only `corpus/hyperon_scripts/*` remains authoritative for imported upstream
  HE tests.
- CeTTa-authored `he_extended` witnesses such as the `once/collapse` probe are
  kept out of the strict HE lane when they conflict with upstream HE behavior.

### A.4 How To Refresh This PDF

```bash
cd <petta-he-profile>

# 1. Run the guarded local HE profile suite.
HE_METTA_BIN=/path/to/metta \
LIMIT_KB=3145728 SWIPL_STACK_LIMIT=1g SWIPL_THREADS=false TIMEOUT_SECONDS=180 \
tests/run_he_profile_suite.sh > .he-logs/he_profile_suite_manual_refresh.log 2>&1

# 2. Run the guarded HE corpus and regenerate the severity TSV.
HE_METTA_BIN=/path/to/metta \
LIMIT_KB=3145728 SWIPL_STACK_LIMIT=1g SWIPL_THREADS=false TIMEOUT_SECONDS=180 \
tests/run_he_corpus_bundle.sh

# 3. Re-render this PDF from the current profile + latest guarded logs.
tests/tools/render_he_profile_pdf.sh
```

The renderer uses the latest \`.he-logs/petta_he_corpus_*.log\` and its paired
\`he_core_severity_*.tsv\` as the source of truth for the measured-state appendix.
EOF
} > "$summary_tmp"

mkdir -p "$(dirname -- "$OUT_PDF")"
pandoc \
    --from=gfm+pipe_tables \
    --pdf-engine=pdflatex \
    --toc \
    -V geometry:margin=1in \
    -o "$OUT_PDF" \
    "$summary_tmp"

printf '%s\n' "$OUT_PDF"
