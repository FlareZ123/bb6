#!/usr/bin/env bash
set -euo pipefail
work="$PWD/.tmp/a48-parent"
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/imports"
base64 -d im-results/agent13-coverage/BB6Coverage.lean.xz.b64 | xz -d > "$work/imports/BB6Coverage.lean"
cp im-results/agent42-champion-terminal/TerminalProofs.tar.xz.b64 "$work/imports/"
cp im-results/agent42-champion-terminal/TerminalLeftExact.lean.xz.b64 "$work/imports/"
python3 - "$work/imports" <<'PY'
import base64, io, lzma, pathlib, sys, tarfile
root = pathlib.Path(sys.argv[1])
archive = lzma.decompress(base64.b64decode((root / "TerminalProofs.tar.xz.b64").read_bytes()))
with tarfile.open(fileobj=io.BytesIO(archive), mode="r:") as tf:
    tf.extractall(root)
left = lzma.decompress(base64.b64decode((root / "TerminalLeftExact.lean.xz.b64").read_bytes()))
(root / "TerminalLeft.lean").write_bytes(left)
PY
python3 tools/lean_compile_closure.py \
  im-results/agent48-champion-root/ChampionParentCover.lean \
  im-results/agent48-counted-inc0/ChampionParentExact.lean \
  im-results/agent48-champion-root/ChampionF1OneLFCover.lean \
  im-results/agent48-champion-root/ChampionF1ZeroRD.lean \
  --override TerminalBridge=im-results/agent42-champion-terminal/TerminalBridge.lean \
  --workdir "$work/build" --jobs 4 | tee "$work/log"
for theorem in parent_cover parent_reachable parentCertificate sibling_never lc_never re_never champion_score_ge_3512 champion_parent_exact_cover championParentExactCertificate; do
  grep -E "$theorem.*depends on axioms" "$work/log"
done
python3 - "$work/log" <<'PY'
import pathlib, sys
log = pathlib.Path(sys.argv[1]).read_text()
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
names = (
    'BB6.Agent48F1OneLF.checked',
    'BB6.Agent48F1OneLF.nohalt',
    'BB6.Agent48F1OneLF.all_completions_weighted',
    'BB6.Agent48F1OneLFHard.stage',
    'BB6.Agent48F1OneLFHard.never',
    'BB6.Agent48F1ZeroRD.stage',
    'BB6.Agent48F1ZeroRD.never',
    'BB6.Agent48F1ZeroRD.cover',
)
for name in names:
    prefix = "'" + name + "' depends on axioms: ["
    start = log.find(prefix)
    if start >= 0:
        start += len(prefix)
        end = log.find(']', start)
        if end < 0: raise SystemExit('unterminated axiom list: ' + name)
        used = {x.strip() for x in log[start:end].replace('\n', ' ').split(',') if x.strip()}
    elif "'" + name + "' does not depend on any axioms" in log:
        used = set()
    else:
        raise SystemExit('missing F1 axiom audit: ' + name)
    if not used <= allowed:
        raise SystemExit(f'nonstandard axioms for {name}: {used - allowed}')
    print(f'{name}: {sorted(used)}')
PY
if grep -E 'depends on axioms.*(sorryAx|native_decide)' "$work/log"; then exit 1; fi
