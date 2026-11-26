#!/usr/bin/env bash
set -euo pipefail
base="$PWD/im-results/agent14-raw139-d0-generic"
common="$PWD/im-results/agent14-raw139-d0-zeroLF"
sibling="$1"
case "$sibling" in
  OneLA) label=LA; bound=1361; code=2; rootsha=6bc5c852ae4850ab0b121a0a082b0aa76738e619b2e905447f81cba16a983875 ;;
  *) echo "Unknown sibling $sibling" >&2; exit 2 ;;
esac
work="$PWD/.tmp/a48-d0-$sibling"
mkdir -p "$work/src/common" "$work/src/generic" "$work/imports" "$work/build"
base64 -d "$common/source.tar.xz.b64" > "$work/common.tar.xz"
base64 -d "$base/source.tar.xz.b64" > "$work/generic.tar.xz"
echo "96f3fb39a1beabc8319147f25e9a3e612fec818ae57c52c54d81fa1248e50559  $work/common.tar.xz" | sha256sum -c
echo "af3ca0f10ca181c6b37c14764fff715c8d6aee6871b759d7e2d5e944fb92b449  $work/generic.tar.xz" | sha256sum -c
tar -xJf "$work/common.tar.xz" -C "$work/src/common"
tar -xJf "$work/generic.tar.xz" -C "$work/src/generic"
PYTHONPATH="$PWD/im-results/agent48-raw139-f1-oneRA:$PWD/im-results/agent48-raw139-f1-oneLA" python3 "$work/src/generic/sibling.py" "$work/src/common" "$work/imports" "$work/src/generic/one${label}-spec.json"
root="$work/imports/Raw139D0${label}Cover.lean"
echo "$rootsha  $root" | sha256sum -c
python3 im-results/agent13-coverage/unpack.py
python3 tools/lean_compile_closure.py "$root" --workdir "$work/build" --jobs 2 --manifest "$work/manifest.json" --label "raw139-d0-$sibling" --theorem "BB6.Agent14Raw139D0${label}.all_completions_weighted" --parent-table "[7,24,11,24,14,24,$code,16,12,11,24,24]" --weighted-bound "$bound" --artifact-name "raw139-d0-$sibling-certified" --provenance-input "$base/source.tar.xz.b64" --provenance-input "$common/source.tar.xz.b64" --provenance-input "$base/reproduce.sh" --provenance-input "$PWD/im-results/agent48-raw139-f1-oneRA/blockcert.py" --provenance-input "$PWD/im-results/agent48-raw139-f1-oneLA/scan.py" | tee "$work/log"
