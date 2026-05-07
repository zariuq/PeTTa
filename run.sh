SCRIPT_DIR=$(cd -- "$(dirname -- "$0")" && pwd)
SWIPL_STACK_LIMIT=${SWIPL_STACK_LIMIT:-8g}
SWIPL_THREADS=${SWIPL_THREADS:-true}
if [ -f "$SCRIPT_DIR/mork_ffi/target/release/libmork_ffi.so" ]; then
    exec env LD_PRELOAD="$SCRIPT_DIR/mork_ffi/target/release/libmork_ffi.so" \
        swipl --threads="$SWIPL_THREADS" --stack_limit="$SWIPL_STACK_LIMIT" -q -s "$SCRIPT_DIR/src/main.pl" -- "$@" mork
else
    exec swipl --threads="$SWIPL_THREADS" --stack_limit="$SWIPL_STACK_LIMIT" -q -s "$SCRIPT_DIR/src/main.pl" -- "$@"
fi
