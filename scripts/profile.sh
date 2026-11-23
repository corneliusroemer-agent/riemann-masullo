#!/usr/bin/env bash
# Profile one module of the library with the options from lakefile.toml.
#
#   scripts/profile.sh RiemannMasullo/Ch07_SchauderBasesZeta/Sec3b.lean [out.log] [extra -D options]
#
# Run from the repository root after `lake build` of the module's imports. `lake env lean` does
# not pass the package's [leanOptions], so they are read from lakefile.toml and passed with -D.
# Parallel elaboration is turned off (Elab.async=false): with it on, a proof's time includes
# waiting for other proofs, and the profiler charges that wait to whatever runs next.
# Tracing allocates, and heartbeats count allocations, so a search near its heartbeat limit can
# fail under tracing only.
set -euo pipefail
file=$1
out=${2:-profile.log}
shift $(( $# >= 2 ? 2 : 1 ))
opts=()
while IFS= read -r line; do
  opts+=("-D${line// /}")
done < <(awk '/^\[leanOptions\]/{f=1; next} /^\[/{f=0} f && /=/ && !/^#/' lakefile.toml)
opts+=(-DElab.async=false -Dprofiler=true -Dprofiler.threshold=100
       -Dtrace.profiler=true -Dtrace.profiler.threshold=300)
/usr/bin/time lake env lean "${opts[@]}" "$@" "$file" > "$out" 2>&1 || true
echo "wrote $out"
