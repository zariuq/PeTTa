#!/usr/bin/env bash
set -euo pipefail

ROOT=$(cd -- "$(dirname -- "$0")/../.." && pwd)
TRANSLATORS_DIR=${TRANSLATORS_DIR:-"$ROOT/../translators"}
OUT_DIR=${OUT_DIR:-"$ROOT/examples/petta_translated"}

mkdir -p "$OUT_DIR"

find "$ROOT/examples" -maxdepth 1 -type f -name 'he_*.metta' | sort | while read -r src; do
    base=$(basename "$src" .metta)
    out="$OUT_DIR/${base}_petta.metta"
    echo "he2petta $src -> $out"
    (
        cd "$TRANSLATORS_DIR"
        ./translate.sh he2petta "$src" "$out"
    )
done
