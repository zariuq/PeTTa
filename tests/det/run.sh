#!/bin/sh
# Determinism tests: each program imports lib_det and runs in default mode and
# with --strict-det; its output and exit status are compared with its .expected
# file (sections "== default N" and "== strict N").
# Usage: sh tests/det/run.sh [program.metta ...]
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
TMP=${TMPDIR:-/tmp}/petta-det-$$
mkdir -p "$TMP"
trap 'rm -rf "$TMP"' EXIT
section() { awk -v m="$2" '$1 == "==" { on = ($2 == m); if (on) print $3; next } on' "$1"; }
pass=0; fail=0
if [ $# -gt 0 ]; then files="$*"; else files=$(find "$ROOT/tests/det" -name '*.metta' | sort); fi
for f in $files; do
    exp="${f%.metta}.expected"; name=${f#"$ROOT/tests/det/"}; bad=""
    for m in default strict; do
        if [ $m = strict ]; then flag=--strict-det; else flag=""; fi
        timeout 30s sh "$ROOT/run.sh" "$f" --silent $flag > "$TMP/raw" 2> /dev/null
        { echo $?; sed -e "s|$ROOT/||g" "$TMP/raw"; } > "$TMP/got"
        section "$exp" $m > "$TMP/want"
        cmp -s "$TMP/want" "$TMP/got" || bad="$bad $m"
    done
    if [ -z "$bad" ]; then pass=$((pass + 1)); else fail=$((fail + 1)); echo "FAIL $name:$bad"; fi
done
echo "determinism tests: $pass passed, $fail failed"
[ $fail -eq 0 ]
