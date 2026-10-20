#!/bin/sh
# Generated code of typed programs: a check is emitted exactly where the
# compiler cannot establish a type (see TYPES.md), a definite conflict is a
# compile-time error, and the --oracle / --no-type-checks flags behave.
set -u
SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
ROOT_DIR=$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)
TMP_DIR=$(mktemp -d /tmp/type_dispatch_matrix_XXXX)
trap 'rm -rf "$TMP_DIR"' EXIT
FAILED=0

# run NAME FLAGS... < program: compiles and runs the program, keeping output and status
run() {
    name=$1; shift
    cat > "$TMP_DIR/$name.metta"
    sh "$ROOT_DIR/run.sh" "$TMP_DIR/$name.metta" "$@" > "$TMP_DIR/$name.out" 2>&1
    echo $? > "$TMP_DIR/$name.status"
}
fail() { echo "[FAIL] $1: $2"; sed 's/^/    /' "$TMP_DIR/$1.out" | tail -30; FAILED=1; }
status_is() { [ "$(cat "$TMP_DIR/$1.status")" = "$2" ] || fail "$1" "exit $(cat "$TMP_DIR/$1.status"), expected $2"; }
has() { grep -qF -- "$2" "$TMP_DIR/$1.out" || fail "$1" "missing: $2"; }
lacks() { if grep -qF -- "$2" "$TMP_DIR/$1.out"; then fail "$1" "unexpected: $2"; fi; }
# the code compiled for the program's last runnable only (not for its imports):
last_goal_lacks() { if awk '/metta runnable/ { buf = "" } { buf = buf $0 "\n" } END { printf "%s", buf }' "$TMP_DIR/$1.out" | grep -qF -- "$2"; then fail "$1" "unexpected in the last runnable: $2"; fi; }

TYPED_CALLS='
(: dbl (-> Number Number))
(= (dbl $x) (* $x 2))
(: quad (-> Number Number))
(= (quad $x) (dbl (dbl $x)))
!(test (quad 3) 12)'

# Types established statically need no check at all:
echo "$TYPED_CALLS" | run established
status_is established 0; lacks established "typecheck"; lacks established "number("

# ... and --oracle checks them at runtime anyway, which must pass:
echo "$TYPED_CALLS" | run oracle --oracle
status_is oracle 0; has oracle "typecheck_or_error"; lacks oracle "❌"

# A value of unknown type is checked where it meets a declared one:
run guard <<'EOF'
(= (untyped) 5)
(: dbl (-> Number Number))
(= (dbl $x) (* $x 2))
!(test (dbl (untyped)) 10)
EOF
status_is guard 0; has guard "number("

# ... unless --no-type-checks erases every check:
run erased --no-type-checks <<'EOF'
(= (untyped) 5)
(: dbl (-> Number Number))
(= (dbl $x) (* $x 2))
!(test (dbl (untyped)) 10)
EOF
status_is erased 0; lacks erased "number("; lacks erased "typecheck"

# Definite conflicts are compile-time errors, naming the value or the types:
run literal <<'EOF'
(: dbl (-> Number Number))
(= (dbl $x) (* $x 2))
!(dbl "s")
EOF
status_is literal 2; has literal 'Type mismatch: got "s" but expected Number'

run nominal <<'EOF'
(: a A)
(: f (-> A B))
(= (f $x) $x)
EOF
status_is nominal 2; has nominal "Type conflict: value is constrained as A but also required as B"

run poly_mismatch <<'EOF'
!(import! &self (library lib_roman))
!(map-flat (+ 1) ("s" 2))
EOF
status_is poly_mismatch 2; has poly_mismatch 'Type mismatch: got ("s" 2) but expected (List Number)'

# A polymorphic library call over established types is guard-free:
run poly_resolved <<'EOF'
!(import! &self (library lib_roman))
!(test (map-flat (+ 1) (1 2)) (2 3))
EOF
status_is poly_resolved 0; last_goal_lacks poly_resolved "typecheck"

# Overloads: arguments that fit one declaration call it directly; only the
# result, which the overloaded body does not establish, is checked:
run overload <<'EOF'
(: f (-> Number Number))
(: f (-> String String))
(= (f $x) $x)
!(test (f 1) 1)
EOF
status_is overload 0; has overload "f(1,"; lacks overload "no_matching_overload"; has overload "typecheck_ok(B, 'Number')"

# Untyped code compiles as before: native arithmetic, no checks:
sh "$ROOT_DIR/run.sh" "$ROOT_DIR/examples/fib.metta" > "$TMP_DIR/fib.out" 2>&1; echo $? > "$TMP_DIR/fib.status"
status_is fib 0; lacks fib "typecheck"; has fib "A<2"; has fib " is "

# A foreign function's primitive result is checked, not trusted:
run foreign <<'EOF'
!(import_prolog_function atom_length)
(: atom_length (-> Symbol Number))
!(test (atom_length abc) 3)
EOF
status_is foreign 0; has foreign "number("

if [ $FAILED -eq 0 ]; then echo "OK: type_dispatch_matrix.sh"; else echo "FAILURES in type_dispatch_matrix.sh"; exit 1; fi
