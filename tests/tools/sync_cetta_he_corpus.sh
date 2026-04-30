#!/usr/bin/env bash
set -euo pipefail

ROOT=$(cd -- "$(dirname -- "$0")/../.." && pwd)
SOURCE_ROOT=${SOURCE_ROOT:-/home/zar/claude/c-projects/CeTTa/tests}
DEST_ROOT=${DEST_ROOT:-"$ROOT/corpus/cetta_tests"}

if [ ! -d "$SOURCE_ROOT" ]; then
    printf 'missing CeTTa tests tree: %s\n' "$SOURCE_ROOT" >&2
    exit 2
fi

mkdir -p "$DEST_ROOT"
rsync -a "$SOURCE_ROOT"/ "$DEST_ROOT"/
printf 'SYNCED %s -> %s\n' "$SOURCE_ROOT" "$DEST_ROOT"
