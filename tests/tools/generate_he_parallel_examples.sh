#!/usr/bin/env bash
set -euo pipefail

ROOT=$(cd -- "$(dirname -- "$0")/../.." && pwd)
TRANSLATE_SH=${TRANSLATE_SH:-/home/zar/claude/hyperon/translators/translate.sh}
LABEL_HE_EXAMPLES_SH=${LABEL_HE_EXAMPLES_SH:-"$ROOT/tests/tools/label_petta_he_examples.sh"}
GENERATED_DIR=${GENERATED_DIR:-"$ROOT/examples/he_translated"}

mkdir -p "$GENERATED_DIR"

generate_one() {
    local source_rel=$1
    local source="$ROOT/$source_rel"
    local base
    local generated

    base=$(basename -- "$source_rel" .metta)
    generated="$GENERATED_DIR/${base}_he_parallel.metta"

    "$TRANSLATE_SH" petta2he --preserve-hyperpose "$source" "$generated"
    "$LABEL_HE_EXAMPLES_SH" --file "$generated" "$source"
    printf '%s\n' "$generated"
}

generate_one "examples/hyperpose_primes.metta"
