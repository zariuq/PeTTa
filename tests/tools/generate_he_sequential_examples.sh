#!/usr/bin/env bash
set -euo pipefail

ROOT=$(cd -- "$(dirname -- "$0")/../.." && pwd)
TRANSLATE_SH=${TRANSLATE_SH:-"$ROOT/../translators/translate.sh"}
LABEL_HE_EXAMPLES_SH=${LABEL_HE_EXAMPLES_SH:-"$ROOT/tests/tools/label_petta_he_examples.sh"}
GENERATED_DIR=${GENERATED_DIR:-"$ROOT/examples/he_translated"}
SOURCE_DIR=${SOURCE_DIR:-"$ROOT/examples"}

EXTERNAL_OR_INTERACTIVE='greedy_chess.metta repl.metta llm_cities.metta torch.metta git_import.metta git_import2.metta python.metta python_import.metta'
PETTA_SPECIFIC='translatorrule.metta translatorrule_fib.metta translatorrule_for.metta translatepredicate.metta streamops.metta metta4_streams.metta mutex_and_transaction.metta state.metta nilbc.metta prologimport.metta myinterpreter.metta selfprog.metta smartdispatch.metta builin_types.metta parametric_types.metta recursive_types.metta meta_types.metta types_dependent.metta types_nondet.metta mettaset.metta spaces.metta spaces_find.metta spaces_removeallatoms.metta spaces_succeedspredicate.metta'

mkdir -p "$GENERATED_DIR"

in_list() {
    local needle=$1
    local hay=$2
    case " $hay " in
        *" $needle "*) return 0 ;;
        *) return 1 ;;
    esac
}

source_uses_hyperpose() {
    grep -Eq '(^|[^[:alnum:]_-])hyperpose([^[:alnum:]_-]|$)' "$1"
}

generate_one() {
    local source=$1
    local base
    local generated

    base=$(basename -- "$source" .metta)
    generated="$GENERATED_DIR/${base}_he_sequential.metta"

    "$TRANSLATE_SH" petta2he "$source" "$generated"
    "$LABEL_HE_EXAMPLES_SH" --file "$generated" "$source"
    printf '%s\n' "$generated"
}

shopt -s nullglob
for source in "$SOURCE_DIR"/*.metta; do
    base=$(basename -- "$source")
    case $base in
        he_*.metta)
            continue
            ;;
    esac
    if in_list "$base" "$EXTERNAL_OR_INTERACTIVE" || in_list "$base" "$PETTA_SPECIFIC"; then
        continue
    fi
    if ! source_uses_hyperpose "$source"; then
        continue
    fi
    generate_one "$source"
done
