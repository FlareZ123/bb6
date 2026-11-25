#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/../.." && pwd)"
if [[ $# -ge 1 ]]; then canonical77_dir="$1"; else canonical77_dir="$repo_root/canonical77"; fi
if [[ $# -ge 2 ]]; then cryptids_dir="$2"; else cryptids_dir="$repo_root/cryptids"; fi
if [[ $# -ge 3 ]]; then canonical76_dir="$3"; else canonical76_dir="$repo_root/canonical76"; fi
build_dir="$cryptids_dir/BB6Agent48"
mkdir -p "$build_dir"

if [[ ! -f "$canonical77_dir/CanonicalRaw114Accepted.olean" ]]; then
  found="$(find "$canonical77_dir" -name CanonicalRaw114Accepted.olean -print -quit)"
  [[ -n "$found" ]] || { echo "CanonicalRaw114Accepted.olean missing from canonical77 artifact" >&2; exit 2; }
  canonical77_dir="$(dirname "$found")"
fi
for module in Frontier.olean FirstHolePath.olean CanonicalRaw114Accepted.olean \
  WeightedNonhaltLeafAdapter.olean FourHoleRootFrontier.olean \
  FourHoleResidualRoster.olean CanonicalRosterRefinement.olean TNFPilot.olean; do
  [[ -f "$canonical77_dir/$module" ]] || {
    echo "Required canonical77 module missing: $canonical77_dir/$module" >&2
    exit 2
  }
done
if [[ ! -f "$canonical76_dir/CanonicalTwoParentRosterOnly.olean" ]]; then
  found="$(find "$canonical76_dir" -name CanonicalTwoParentRosterOnly.olean -print -quit)"
  [[ -n "$found" ]] || { echo "CanonicalTwoParentRosterOnly.olean missing from accepted canonical76 artifact" >&2; exit 2; }
  canonical76_dir="$(dirname "$found")"
fi

for module in RelativeTape FrontierAudit FrontierMass FrontierClose \
  CryptidsTapeAdapter CryptidsF287; do
  cp "$repo_root/im-results/agent4-coverage-smoke/$module.lean" "$build_dir/"
done

# The source bridge intentionally nests BB6.F287 under BB6.ConjectureBridge.
# Re-export only the exact table and theorem at the namespace expected by the
# existing F287HaltFreedom adapter; the proof term is unchanged.
cat >> "$build_dir/CryptidsF287.lean" <<'LEAN'
end BB6.ConjectureBridge
namespace BB6.F287
open BB6Coverage
abbrev expectedRLE : Machine := BB6.ConjectureBridge.BB6.F287.expectedRLE
theorem literal_never : NeverHalts expectedRLE :=
  BB6.ConjectureBridge.BB6.F287.literal_never
end BB6.F287
LEAN
for module in HaltSlotFreedom F287HaltFreedom; do
  cp "$repo_root/im-results/agent8-coverage-contract/$module.lean" "$build_dir/"
done
for module in HardRootCore HardRootParents HardRootLeaves; do
  cp "$repo_root/im-results/agent19-hard-root-crosswalk/$module.lean" "$build_dir/"
done
cp "$repo_root/im-results/agent48-raw139-hard-root/A6Ingestion.lean" "$build_dir/"
cp "$repo_root/im-results/agent48-raw139-hard-root/A6Canonical76Ingestion.lean" "$build_dir/"

cd "$cryptids_dir"
export LEAN_PATH="$build_dir:$canonical77_dir:$canonical76_dir"

compile() {
  local module="$1"
  echo "=== compiling $module ==="
  lake env lean -o "$build_dir/$module.olean" "$build_dir/$module.lean"
}

echo "=== Lean version ==="
lean --version
echo "=== pinned external source ==="
git rev-parse HEAD
echo "=== canonical77 dependency root ==="
echo "$canonical77_dir"

for module in RelativeTape FrontierAudit FrontierMass FrontierClose \
  CryptidsTapeAdapter CryptidsF287 HaltSlotFreedom F287HaltFreedom; do
  compile "$module"
done

for module in HardRootCore HardRootParents HardRootLeaves A6Ingestion A6Canonical76Ingestion; do
  compile "$module"
done

echo "A6 source-connected raw139 frontier compilation succeeded."
