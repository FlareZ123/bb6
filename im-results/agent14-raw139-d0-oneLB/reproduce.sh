#!/usr/bin/env bash
set -euo pipefail
base="$PWD/im-results/agent14-raw139-d0-oneLB"
common="$PWD/im-results/agent14-raw139-d0-zeroLF"
work="$PWD/.tmp/a48-d0-OneLB"
mkdir -p "$work/src/common" "$work/src/oneLB" "$work/imports" "$work/build"
base64 -d "$common/source.tar.xz.b64" > "$work/common.tar.xz"
base64 -d "$base/source.tar.xz.b64" > "$work/oneLB.tar.xz"
echo "96f3fb39a1beabc8319147f25e9a3e612fec818ae57c52c54d81fa1248e50559  $work/common.tar.xz" | sha256sum -c
echo "d560c6e2b27fa8f0f41b38070d7446a0f9c8053c35a8501b4d7ad6844b3aa5a3  $work/oneLB.tar.xz" | sha256sum -c
tar -xJf "$work/common.tar.xz" -C "$work/src/common"
tar -xJf "$work/oneLB.tar.xz" -C "$work/src/oneLB"
PYTHONPATH="$PWD/im-results/agent48-raw139-f1-oneRA:$PWD/im-results/agent48-raw139-f1-oneLA" python3 "$work/src/oneLB/make-oneLB.py" "$work/src/common" "$work/imports" "$work/src/oneLB/oneLB-bank.json"
python3 "$work/src/oneLB/emit-long.py" "$work/imports" "$work/src/oneLB/ZipLong.lean"
python3 "$work/src/oneLB/trim-imports.py" "$work/imports"
echo "87f0a8be0bca98a4f9c329722488e7e18ead267b3460dd1631471b46031e7809  $work/imports/Raw139D0LBCover.lean" | sha256sum -c
python3 im-results/agent13-coverage/unpack.py
python3 tools/lean_compile_closure.py "$work/imports/Raw139D0LBCover.lean" --workdir "$work/build" --jobs 2 --manifest "$work/manifest.json" --label raw139-d0-oneLB --theorem BB6.Agent14Raw139D0LB.all_completions_weighted --parent-table '[7,24,11,24,14,24,6,16,12,11,24,24]' --weighted-bound 7252 --artifact-name raw139-d0-OneLB-certified --provenance-input "$base/source.tar.xz.b64" --provenance-input "$common/source.tar.xz.b64" --provenance-input "$base/reproduce.sh" --provenance-input "$PWD/im-results/agent48-raw139-f1-oneRA/blockcert.py" --provenance-input "$PWD/im-results/agent48-raw139-f1-oneLA/scan.py" | tee "$work/log"
