#!/usr/bin/env bash
# Run one of the statement scans over the whole built library.
#
#   scripts/scan_statements.sh lean/StatementSizes.lean   > sizes.txt
#   scripts/scan_statements.sh lean/StatementBlowup.lean  > blowup.txt   (edit `targets` first)
#   scripts/scan_statements.sh lean/ShowSubterm.lean      > subterm.txt  (edit the calls first)
#
# Run from the repository root after `lake build`. The library has no root module (lakefile
# globs `RiemannMasullo.+`), so this prepends one `import` per module to a temporary copy.
# StatementSizes takes about 35 s on a 16-core machine.
set -euo pipefail
scan=$1
tmp=$(mktemp -d)
trap 'rm -r "$tmp"' EXIT
find RiemannMasullo -name '*.lean' | sort | sed 's|\.lean$||; s|/|.|g; s|^|import |' > "$tmp/Scan.lean"
cat "$scan" >> "$tmp/Scan.lean"
lake env lean -DmaxSynthPendingDepth=3 "$tmp/Scan.lean"
