#!/usr/bin/env bash
set -euo pipefail
base="im-results/agent41-raw139-f1-zeroLF"
work="$PWD/.tmp/a41-f1-zeroRB"
mkdir -p "$work/imports" "$work/build"
base64 -d "$base/Agent41F1ZeroLFProofs.tar.xz.b64" > "$work/prior.tar.xz"
tar -xJf "$work/prior.tar.xz" -C "$work/imports" Agent41SymSweep.lean
base64 -d "$base/Agent41F1ZeroRBProofs.tar.xz.b64" > "$work/proofs.tar.xz"
echo 'dedb53f31b5493b240d1b1d89fa1c409f0ced92ef1d6486c5415e6d98fe75aba  '"$work/proofs.tar.xz" | sha256sum -c
tar -xJf "$work/proofs.tar.xz" -C "$work/imports"
python3 im-results/agent13-coverage/unpack.py
python3 tools/lean_compile_closure.py \
  "$work/imports/Agent41F1ZeroRBCover.lean" \
  --workdir "$work/build" --jobs 4 \
  --manifest "$work/manifest.json" --label raw139-f1-zeroRB \
  --theorem BB6.Agent41F1ZeroRB.all_completions_weighted \
  --parent-table '[7,24,11,24,14,21,3,16,12,11,24,5]' \
  --weighted-bound 290 --artifact-name raw139-f1-zeroRB-certified \
  --provenance-input "$base/Agent41F1ZeroLFProofs.tar.xz.b64" --provenance-input "$base/Agent41F1ZeroRBProofs.tar.xz.b64" | tee "$work/log"
python3 - "$work/log" <<'PY'
import pathlib, re, sys
log = pathlib.Path(sys.argv[1]).read_text()
names = ['BB6.Agent41SymSweep.run_sound', 'BB6.Agent41F1ZeroRB.all_completions_weighted', 'BB6.Agent41F1ZeroRB.checked', 'BB6.Agent41F1ZeroRBHard.H19.growth', 'BB6.Agent41F1ZeroRBHard.H20.drain', 'BB6.Agent41F1ZeroRBHard.H20.growth']
names += [f'BB6.Agent41F1ZeroRBHard.H{i}.never' for i in range(23)]
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
