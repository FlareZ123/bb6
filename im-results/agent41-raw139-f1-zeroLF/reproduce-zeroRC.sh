#!/usr/bin/env bash
set -euo pipefail
base="im-results/agent41-raw139-f1-zeroLF"
work="$PWD/.tmp/a41-f1-zeroRC"
mkdir -p "$work/imports" "$work/build"
base64 -d "$base/Agent41F1ZeroLFProofs.tar.xz.b64" > "$work/prior.tar.xz"
tar -xJf "$work/prior.tar.xz" -C "$work/imports" Agent41SymSweep.lean
base64 -d "$base/Agent41F1ZeroRCProofs.tar.xz.b64" > "$work/proofs.tar.xz"
echo 'e714f0772d6e7df0d64e3da63153c8450e39abead67caf8fb5b61d1241e5dbd8  '"$work/proofs.tar.xz" | sha256sum -c
tar -xJf "$work/proofs.tar.xz" -C "$work/imports"
python3 im-results/agent13-coverage/unpack.py
python3 tools/lean_compile_closure.py \
  "$work/imports/Agent41F1ZeroRCCover.lean" \
  --workdir "$work/build" --jobs 4 \
  --manifest "$work/manifest.json" --label raw139-f1-zeroRC \
  --theorem BB6.Agent41F1ZeroRC.all_completions_weighted \
  --parent-table '[7,24,11,24,14,21,3,16,12,11,24,9]' \
  --weighted-bound 3807 --artifact-name raw139-f1-zeroRC-certified \
  --provenance-input "$base/Agent41F1ZeroLFProofs.tar.xz.b64" --provenance-input "$base/Agent41F1ZeroRCProofs.tar.xz.b64" | tee "$work/log"
python3 - "$work/log" <<'PY'
import pathlib, re, sys
log = pathlib.Path(sys.argv[1]).read_text()
names = ['BB6.Agent41SymSweep.run_sound', 'BB6.Agent41F1ZeroRC.all_completions_weighted', 'BB6.Agent41F1ZeroRC.checked', 'BB6.Agent41F1ZeroRCHard.H3.core', 'BB6.Agent41F1ZeroRCHard.H7.core', 'BB6.Agent41F1ZeroRCHard.H8.octet']
names += [f'BB6.Agent41F1ZeroRCHard.H{i}.never' for i in range(20) if i not in {0,6}]
for name in names:
    match = re.search(r"'" + re.escape(name) + r"' depends on axioms: \[([^\]]*)\]", log, re.S)
    if match:
        used = {x.strip() for x in match.group(1).split(',') if x.strip()}
    elif "'" + name + "' does not depend on any axioms" in log:
        used = set()
    else:
        raise SystemExit('Missing audit: ' + name)
    assert used <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, used)
    print(name, sorted(used))
PY
