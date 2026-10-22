#!/bin/sh
# Typing tests: each program runs checked, with every check (--oracle) and
# erased (--no-type-checks), and is compared with its .expected file:
# - checked and erased output and exit status match the expectation;
# - the oracle run matches the checked run (eliminated checks change nothing);
# - a checked run without a type error matches the erased run (erasure), unless
#   the program observes something outside the observation boundary.
# A type error prints as (Error typecheck): which check reports it first is not
# part of the contract. "== pending" files are listed, not compared.
# Usage: sh tests/typing/run.sh [program.metta ...]
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
TMP=${TMPDIR:-/tmp}/petta-typing-$$
mkdir -p "$TMP"
trap 'rm -rf "$TMP"' EXIT

run_mode() {  # file mode-flag out
    timeout 30s sh "$ROOT/run.sh" "$1" --silent $2 > "$3.raw" 2> /dev/null
    echo $? > "$3.status"
    sed -E -e 's/^\(Error \(.*\) typecheck\)$/(Error typecheck)/' -e "s|$ROOT/||g" "$3.raw" > "$3"
}
section() {  # expected-file mode -> status line then body
    awk -v m="$2" '$1 == "==" { on = ($2 == m); if (on) print $3; next } on' "$1"
}

pass=0; fail=0; pending=0
if [ $# -gt 0 ]; then files="$*"; else files=$(find "$ROOT/tests/typing" -name '*.metta' | sort); fi
for f in $files; do
    exp="${f%.metta}.expected"
    name=${f#"$ROOT/tests/typing/"}
    if grep -q '^== pending' "$exp"; then pending=$((pending + 1)); echo "PENDING $name"; continue; fi
    run_mode "$f" "" "$TMP/c"; run_mode "$f" --oracle "$TMP/o"; run_mode "$f" --no-type-checks "$TMP/e"
    bad=""
    for m in checked erased; do
        out="$TMP/${m%"${m#?}"}"
        section "$exp" "$m" > "$TMP/want"
        { cat "$out.status"; cat "$out"; } > "$TMP/got"
        cmp -s "$TMP/want" "$TMP/got" || bad="$bad $m"
    done
    { cat "$TMP/o.status"; cat "$TMP/o"; } > "$TMP/og"; { cat "$TMP/c.status"; cat "$TMP/c"; } > "$TMP/cg"
    cmp -s "$TMP/og" "$TMP/cg" || bad="$bad oracle"
    if [ "$(cat "$TMP/c.status")" = 0 ] && ! grep -q '^== boundary' "$exp"; then
        { cat "$TMP/e.status"; cat "$TMP/e"; } > "$TMP/eg"
        cmp -s "$TMP/cg" "$TMP/eg" || bad="$bad erasure"
    fi
    if [ -z "$bad" ]; then pass=$((pass + 1))
    else fail=$((fail + 1)); echo "FAIL $name:$bad"; fi
done
echo "typing tests: $pass passed, $fail failed, $pending pending"
[ $fail -eq 0 ]
