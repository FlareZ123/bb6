#!/usr/bin/env bash
set -euo pipefail
base="$PWD/im-results/agent14-raw139-d0-zeroLF"
work="$PWD/.tmp/a48-d0-ZeroLF"
mkdir -p "$work/src" "$work/imports" "$work/build"
base64 -d "$base/source.tar.xz.b64" > "$work/source.tar.xz"
echo "96f3fb39a1beabc8319147f25e9a3e612fec818ae57c52c54d81fa1248e50559  $work/source.tar.xz" | sha256sum -c
tar -xJf "$work/source.tar.xz" -C "$work/src"
PYTHONPATH="$PWD/im-results/agent48-raw139-f1-oneRA:$PWD/im-results/agent48-raw139-f1-oneLA" python3 "$work/src/generate.py" "$work/imports"
echo "a434fac190590c8fc24538a5f9fb7e3fb4763843875ebaffd4e7597c90fefb5f  $work/imports/certificate-spec.json" | sha256sum -c
echo "af2904ca46cfcf199c2f01f3eb500752e1da856571f7fc645bcc6462727b39eb  $work/imports/Raw139D0LFCover.lean" | sha256sum -c
python3 im-results/agent13-coverage/unpack.py
python3 tools/lean_compile_closure.py "$work/imports/Raw139D0LFCover.lean" --workdir "$work/build" --jobs 2 --manifest "$work/manifest.json" --label raw139-d0-zeroLF --theorem BB6.Agent14Raw139D0LF.all_completions_weighted --parent-table '[7,24,11,24,14,24,20,16,12,11,24,24]' --weighted-bound 352 --artifact-name raw139-d0-ZeroLF-certified --provenance-input "$base/source.tar.xz.b64" --provenance-input "$base/reproduce.sh" --provenance-input "$PWD/im-results/agent48-raw139-f1-oneRA/blockcert.py" --provenance-input "$PWD/im-results/agent48-raw139-f1-oneLA/scan.py" | tee "$work/log"
