#!/usr/bin/env bash
set -euo pipefail
base="im-results/agent41-raw139-f1-zeroLF"
work="$PWD/.tmp/a41-f1-zeroLF"
mkdir -p "$work/imports" "$work/build"
base64 -d "$base/Agent41F1ZeroLFProofs.tar.xz.b64" > "$work/proofs.tar.xz"
echo '15b951ad6c8c9b988e2a2f44a39671a938b4c2b0fbc264c72a4afe1a972b62bb  '"$work/proofs.tar.xz" | sha256sum -c
tar -xJf "$work/proofs.tar.xz" -C "$work/imports"
python3 im-results/agent13-coverage/unpack.py
python3 tools/lean_compile_closure.py \
  "$work/imports/Agent41F1ZeroLFCover.lean" \
  --workdir "$work/build" --jobs 4 \
  --manifest "$work/manifest.json" --label raw139-f1-zeroLF \
  --theorem BB6.Agent41F1ZeroLF.all_completions_weighted \
  --parent-table '[7,24,11,24,14,21,3,16,12,11,24,20]' \
  --weighted-bound 1603 --artifact-name raw139-f1-zeroLF-certified \
  --provenance-input "$base/Agent41F1ZeroLFProofs.tar.xz.b64" | tee "$work/log"
python3 - "$work/log" <<'PY'
import pathlib, re, sys
log = pathlib.Path(sys.argv[1]).read_text()
names = ['BB6.Agent41SymSweep.run_sound', 'BB6.Agent41F1ZeroLF.all_completions_weighted', 'BB6.Agent41F1ZeroLF.checked', 'BB6.Agent41F1ZeroLFHard.H9.core', 'BB6.Agent41F1ZeroLFHard.H9.stage_step']
names += [f'BB6.Agent41F1ZeroLFHard.H{i}.never' for i in range(14) if i != 2]
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
