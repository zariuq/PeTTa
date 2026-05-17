#!/usr/bin/env bash
set -euo pipefail

ROOT=$(cd -- "$(dirname -- "$0")/../.." && pwd)
GENERATED_DIR=${GENERATED_DIR:-"$ROOT/examples/he_translated"}
SOURCE_DIR=${SOURCE_DIR:-"$ROOT/examples"}

usage() {
    cat <<'EOF'
Usage:
  label_petta_he_examples.sh
  label_petta_he_examples.sh --file <generated_he_file> <source_metta_file>

Relabels translated example headers so they explicitly declare:
  - source path
  - translation target: PeTTa HE
  - intended runtime: ./run.sh --he
  - portability warning: not claimed portable Pure HE
EOF
}

header_mode_for_generated() {
    case $1 in
        *_he_parallel.metta)
            printf '%s\t%s\n' \
                'PeTTa HE parallel' \
                'requires HE runtime with hyperpose support; not claimed portable Pure HE'
            ;;
        *_he_sequential.metta)
            printf '%s\t%s\n' \
                'PeTTa HE sequential' \
                'portable/default HE lowering; hyperpose is deparallelized to superpose'
            ;;
        *)
            printf '%s\t%s\n' \
                'PeTTa HE' \
                'portable/default HE lowering'
            ;;
    esac
}

stamp_header() {
    local generated=$1
    local source=$2
    local source_display=$source
    local tmp
    local mode_line
    local target
    local portability

    case "$source" in
        "$ROOT"/*) source_display=${source#"$ROOT"/} ;;
    esac

    mode_line=$(header_mode_for_generated "$generated")
    target=${mode_line%%$'\t'*}
    portability=${mode_line#*$'\t'}

    tmp=$(mktemp "$(dirname -- "$generated")/.label.XXXXXX")
    awk -v source="$source_display" -v target="$target" -v portability="$portability" '
        NR == 1 {
            print
            next
        }
        NR == 2 {
            print "; Source: " source
            print "; Translation target: " target
            print "; Intended runtime: ./run.sh --he"
            print "; Portability: " portability
            print ""
            next
        }
        $0 ~ /^; Source: / { next }
        $0 ~ /^; Translation target: / { next }
        $0 ~ /^; Intended runtime: / { next }
        $0 ~ /^; Portability: / { next }
        NR == 3 && $0 == "" { next }
        { print }
    ' "$generated" > "$tmp"
    mv "$tmp" "$generated"
}

label_one() {
    local generated=$1
    local source=$2

    if [ ! -f "$generated" ]; then
        printf 'missing generated file: %s\n' "$generated" >&2
        return 1
    fi
    if [ ! -f "$source" ]; then
        printf 'missing source file for generated file %s: %s\n' "$generated" "$source" >&2
        return 1
    fi
    stamp_header "$generated" "$source"
}

if [ $# -gt 0 ]; then
    case $1 in
        --file)
            if [ $# -ne 3 ]; then
                usage >&2
                exit 64
            fi
            label_one "$2" "$3"
            exit 0
            ;;
        -h|--help)
            usage
            exit 0
            ;;
        *)
            usage >&2
            exit 64
            ;;
    esac
fi

shopt -s nullglob
for generated in "$GENERATED_DIR"/*_he_sequential.metta "$GENERATED_DIR"/*_he.metta "$GENERATED_DIR"/*_he_parallel.metta; do
    case $generated in
        *_he_parallel.metta)
            base=$(basename -- "$generated" _he_parallel.metta)
            ;;
        *_he_sequential.metta)
            base=$(basename -- "$generated" _he_sequential.metta)
            ;;
        *)
            base=$(basename -- "$generated" _he.metta)
            ;;
    esac
    source="$SOURCE_DIR/${base}.metta"
    label_one "$generated" "$source"
done
