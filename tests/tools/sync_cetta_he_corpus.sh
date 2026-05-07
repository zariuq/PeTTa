#!/usr/bin/env bash
set -euo pipefail

ROOT=$(cd -- "$(dirname -- "$0")/../.." && pwd)
if [ -n "${SOURCE_ROOT:-}" ]; then
    :
elif [ -d /home/zar/claude/hyperon/CeTTa/tests ]; then
    SOURCE_ROOT=/home/zar/claude/hyperon/CeTTa/tests
else
    SOURCE_ROOT=/home/zar/claude/c-projects/CeTTa/tests
fi
DEST_ROOT=${DEST_ROOT:-"$ROOT/corpus/cetta_tests"}
if [ -n "${SOURCE_LIB_ROOT:-}" ]; then
    :
elif [ -d /home/zar/claude/hyperon/CeTTa/lib ]; then
    SOURCE_LIB_ROOT=/home/zar/claude/hyperon/CeTTa/lib
else
    SOURCE_LIB_ROOT=/home/zar/claude/c-projects/CeTTa/lib
fi
DEST_LIB_ROOT=${DEST_LIB_ROOT:-"$ROOT/lib"}
SOURCE_PROJECT_ROOT=$(cd -- "$SOURCE_ROOT/.." && pwd)
DEST_TEST_SUPPORT_ROOT=${DEST_TEST_SUPPORT_ROOT:-"$ROOT/tests/support"}
DEST_RUNTIME_ROOT=${DEST_RUNTIME_ROOT:-"$ROOT/runtime"}
DEST_CANON_ROOT=${DEST_CANON_ROOT:-"$ROOT/corpus/hyperon_scripts"}

if [ ! -d "$SOURCE_ROOT" ]; then
    printf 'missing CeTTa tests tree: %s\n' "$SOURCE_ROOT" >&2
    exit 2
fi
if [ ! -d "$SOURCE_LIB_ROOT" ]; then
    printf 'missing CeTTa lib tree: %s\n' "$SOURCE_LIB_ROOT" >&2
    exit 2
fi

mkdir -p "$DEST_ROOT"
rsync -a "$SOURCE_ROOT"/ "$DEST_ROOT"/
mkdir -p "$DEST_LIB_ROOT"
rsync -a --include='*/' --include='*.metta' --exclude='*' "$SOURCE_LIB_ROOT"/ "$DEST_LIB_ROOT"/
if [ -d "$SOURCE_ROOT/support" ]; then
    mkdir -p "$DEST_TEST_SUPPORT_ROOT"
    rsync -a "$SOURCE_ROOT"/support/ "$DEST_TEST_SUPPORT_ROOT"/
fi
if [ -d "$SOURCE_PROJECT_ROOT/runtime" ]; then
    mkdir -p "$DEST_RUNTIME_ROOT"
    rsync -a "$SOURCE_PROJECT_ROOT"/runtime/ "$DEST_RUNTIME_ROOT"/
fi
pruned_canonical_mirrors=0
shopt -s nullglob
for mirrored in "$DEST_ROOT"/he_*.metta; do
    base=${mirrored##*/}
    canon=$DEST_CANON_ROOT/${base#he_}
    if [ -f "$canon" ] && cmp -s "$mirrored" "$canon"; then
        rm -f "$mirrored"
        pruned_canonical_mirrors=$((pruned_canonical_mirrors + 1))
    fi
done
shopt -u nullglob
printf 'SYNCED %s -> %s\n' "$SOURCE_ROOT" "$DEST_ROOT"
printf 'SYNCED %s -> %s\n' "$SOURCE_LIB_ROOT" "$DEST_LIB_ROOT"
if [ -d "$SOURCE_ROOT/support" ]; then
    printf 'SYNCED %s -> %s\n' "$SOURCE_ROOT/support" "$DEST_TEST_SUPPORT_ROOT"
fi
if [ -d "$SOURCE_PROJECT_ROOT/runtime" ]; then
    printf 'SYNCED %s -> %s\n' "$SOURCE_PROJECT_ROOT/runtime" "$DEST_RUNTIME_ROOT"
fi
if [ "$pruned_canonical_mirrors" -gt 0 ]; then
    printf 'PRUNED %s canonical he_* mirror copies from %s\n' "$pruned_canonical_mirrors" "$DEST_ROOT"
fi
