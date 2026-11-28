#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
repo="$(git -C "$here" rev-parse --show-toplevel)"
work="$(mktemp -d)"
echo "Lean build workspace: $work"
lean --version
copy() {
  local path="$1" sha="$2"
  test "$(git hash-object "$repo/$path")" = "$sha"
  cp "$repo/$path" "$work/"
}
copy im-results/agent8-coverage-contract/Frontier.lean 115438c4f244b5416a91be4dd7a3f12103d5448d
copy im-results/agent8-coverage-contract/Symmetry.lean 84f62dcea34e7f2a97d07016cc2d9065d4ddd7ce
copy im-results/agent8-coverage-contract/RootShift.lean 80b56fb040f7db81277fcf52cd43e6127fe365ba
copy im-results/agent50-weighted-tnf-pilot/SparseZipper.lean 8081dc82ca1e892ab2f6c698d94b6dc24129f6e6
copy im-results/agent31-three-hole-tnf/SweepPumping.lean e518c288ecdf5c96890ad64b5971f5c2f18a2106
copy im-results/agent46-raw13-cut/Agent46AutoPump.lean 9fb5e24599f4037123dc87d4e722f400eccabf6b
copy im-results/agent1-ngram/NGramCertificate.lean 186254e4dd3ea22faf7008fae4fcd090b3ab1208
copy im-results/agent8-coverage-contract/RayClosed.lean ca24cf074e219c40eaca9f2f8ed57785ee6af21c
copy im-results/agent8-coverage-contract/RayEntry.lean ece99260f59ce7c70b1e061ec3ad741fc8829bbb
copy im-results/agent8-coverage-contract/RayChecker.lean 9e90ed01c997523f60a8fc7393421630411cbc07
copy im-results/agent8-coverage-contract/RayFinite.lean f4157e61fcf66e155547c71dfd3d33b1e3e3116e
copy im-results/agent50-weighted-tnf-pilot/SideCycle.lean 3b6bbbed53863b1aa802b2a38d00fe7af6941b3f
copy im-results/agent24-raw45-c1re/Raw45ReQuadratic.lean 3fa514d27feb8ee306ec24787a20119575fa2b67
copy im-results/agent24-raw45-c1re/Raw45ReAudit.lean c6171d31ec64c306703815d50e9159c4851593da
copy im-results/agent24-raw45-c1re/Raw45ReWitness.lean 76fb7e030930e3bdb4de0d4e3d6692bb13edc922
test "$(git hash-object "$here/certificates.json.xz")" = b202bf2c67a44ed6bb9dbc248231d3021d0a804c
python3 "$here/emit.py" "$here/certificates.json.xz" "$work"
cd "$work"
test "$(git hash-object Raw45ReParent.lean)" = 873b03992612250174b2a6366ca3be9e789d1aa8
test "$(sha256sum Raw45ReChild*.lean Raw45ReParent.lean | sha256sum | cut -d' ' -f1)" = c2fb630f3404fc256473af9f0d1af33eedd307dfb8220bfcd257ef3efef8d02d
export LEAN_PATH=.
for module in Frontier Symmetry RootShift SparseZipper SweepPumping Agent46AutoPump NGramCertificate RayClosed RayEntry RayChecker RayFinite SideCycle Raw45ReQuadratic Raw45ReAudit; do
  lean -o "$module.olean" "$module.lean" | tee "$module.log"
done
printf '%s\n' Raw45ReChild*.lean | xargs -P "${JOBS:-2}" -I '{}' bash -e -o pipefail -c 'm="${1%.lean}"; lean -o "$m.olean" "$1" | tee "$m.log"' _ '{}'
lean -o Raw45ReParent.olean Raw45ReParent.lean | tee Raw45ReParent.log
lean -o Raw45ReWitness.olean Raw45ReWitness.lean | tee Raw45ReWitness.log
! grep -E 'sorryAx|uses .sorry.' ./*.log
grep -F "'BB6.Agent24Raw45.ReWitness.exact_parent_max' depends on axioms: [propext, Classical.choice, Quot.sound]" Raw45ReWitness.log
echo "PASS: exact ordinary blank-step maximum 473, all 25^4 physical completions"

# Extend the preceding exact C1=1RE build with the three other E-targets.
# Current directory is the same temporary Lean workspace as above.
test "$(git hash-object "$here/Raw45Re0Grammar.lean.xz")" = 9a7e5fdec788fbfcf38b32e192aebf592a946f61
xz -dc "$here/Raw45Re0Grammar.lean.xz" > Raw45Re0Grammar.lean
test "$(git hash-object Raw45Re0Grammar.lean)" = f71aca0dae7fbf995dfbe038931b6533c22fc969
lean -o Raw45Re0Grammar.olean Raw45Re0Grammar.lean | tee Raw45Re0Grammar.log
test "$(git hash-object "$here/emit_siblings.py")" = 93985ba2a025f7b0c6f5c10f791969e5b27a110c
for spec in "0LE Raw45Le0 9863e4fdd3967ece8780a9f845c1c7ae5c7b33c6 fc4831c08200a5eea1981bd684b450f8374f05d583f5ce053799a6e7d78554d3" "0RE Raw45Re0 557f865987daad474113b8474d323acda1c87022 5666426c5b48e671b76b284222e9a9cff44f92bd1f611482de91059f53896c85" "1LE Raw45Le1 2a4610b8aa9eb51ec68eb1112b82041adf3a0be7 57ecd780af679179430ec523625750dacbeefed1d47313262bf257d095e4f26c"; do
  read -r tag pref hash sources <<< "$spec"
  test "$(git hash-object "$here/certificates-$tag.json.xz")" = "$hash"
  python3 "$here/emit_siblings.py" "$here/certificates-$tag.json.xz" "$work" "$pref"
  test "$(sha256sum "${pref}"Child*.lean "${pref}"Parent.lean | sha256sum | cut -d' ' -f1)" = "$sources"
  printf '%s\n' "${pref}"Child*.lean | xargs -P "${JOBS:-2}" -I '{}' bash -e -o pipefail -c 'm="${1%.lean}"; lean -o "$m.olean" "$1" | tee "$m.log"' _ '{}'
  lean -o "${pref}Parent.olean" "${pref}Parent.lean" | tee "${pref}Parent.log"
done
copy im-results/agent24-raw45-c1re/Raw45C1Full.lean 89fcc88ff31368c88dddf2cb1e09a27ac1b4afbf
lean -o Raw45C1Full.olean Raw45C1Full.lean | tee Raw45C1Full.log
! grep -E 'sorryAx|uses .sorry.' ./*.log
grep -F "'BB6.Agent24Raw45.C1Full.exact_parent_max' depends on axioms: [propext, Classical.choice, Quot.sound]" Raw45C1Full.log
echo "PASS: exact 473 across all 25^5 physical completions"
