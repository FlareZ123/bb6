#!/usr/bin/env bash
# Run from the checkout root with Lean 4.36.0-rc2 installed.
# Rebuilds the authoritative TM63 source imports and checks the Raw124 F1=1LB
# numeric lift without the unaccepted F412ChampionBound adapter.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$ROOT"
work="$ROOT/.tmp/a2-raw124-1lb-champion-bound"
mkdir -p "$work/imports"
export BB6_CHAMPION_WORK="$work"
python3 - <<'PY'
import base64, io, lzma, os, pathlib, tarfile
root = pathlib.Path(os.environ["BB6_CHAMPION_WORK"]) / "imports"
p = pathlib.Path("im-results/agent42-champion-terminal")
with tarfile.open(fileobj=io.BytesIO(base64.b64decode((p/"TerminalProofs.tar.xz.b64").read_text())), mode="r:xz") as a:
    member = next(m for m in a.getmembers() if pathlib.PurePosixPath(m.name).name == "TerminalFinish.lean")
    (root/"TerminalFinish.lean").write_bytes(a.extractfile(member).read())
(root/"TerminalLeft.lean").write_bytes(lzma.decompress(base64.b64decode((p/"TerminalLeftExact.lean.xz.b64").read_text())))
q = pathlib.Path("im-results/agent13-coverage/BB6Coverage.lean.xz.b64")
(root/"BB6Coverage.lean").write_bytes(lzma.decompress(base64.b64decode(q.read_text())))
PY
printf '%s  %s\n' fbe453c5c170029885ba328bfdd9262600f918a8ce2371c60ecbb843897fd6bd "$work/imports/BB6Coverage.lean" | sha256sum -c -
printf '%s  %s\n' 12329036c66c3846f9261167b8f9aebd1778d9b6ea6044309956c2fa0b3e49b7 "$work/imports/TerminalFinish.lean" | sha256sum -c -
printf '%s  %s\n' 1bce2075fc4e0cd7d740fb71b3796088b190ddb6766e04640d992dadd1b650ff "$work/imports/TerminalLeft.lean" | sha256sum -c -
lean --version
python3 tools/lean_compile_closure.py \
  im-results/agent48-counted-inc0/TM63RawUpperInterface.lean \
  im-results/agent2-tnf-raw124/Raw124OneLBChampionBound.lean \
  --override TerminalBridge=im-results/agent42-champion-terminal/TerminalBridge.lean \
  --override OuterLCIncPrelude=im-results/agent8-counted-reset/OuterLCIncPrelude.lean \
  --override M0OddResidueSeven=im-results/agent41-m0-n16r7/M0OddResidueSeven.lean \
  --override M0EvenEightValuationEncoding=im-results/agent48-counted-inc0/M0EvenEightValuationEncoding.lean \
  --override M2EvenResidueTwo=im-results/agent42-champion-terminal/M2EvenResidueTwo.lean \
  --workdir "$work/build" --jobs "${JOBS:-8}" | tee "$work/compile.log"
python3 - "$work/compile.log" <<'PY'
import json, pathlib, re, sys
log = pathlib.Path(sys.argv[1]).read_text()
allowed = {"propext", "Classical.choice", "Quot.sound"}
names = (
    "BB6.Agent2Raw124OneLBChampionBound.champion_ge_27959",
    "BB6.Agent2Raw124OneLBChampionBound.branch_bound_le_champion_1lb",
)
profiles = {}
for name in names:
    m = re.search(r"'" + re.escape(name) + r"' depends on axioms: \[([^\]]*)\]", log)
    if not m:
        raise SystemExit("missing axiom audit: " + name)
    used = {x.strip() for x in m.group(1).split(",") if x.strip()}
    if not used <= allowed:
        raise SystemExit(f"nonstandard axioms in {name}: {used-allowed}")
    profiles[name] = sorted(used)
    print(f"{name}: {profiles[name]}")
if re.search(r"sorryAx|native_decide", log):
    raise SystemExit("forbidden placeholder/native_decide in source closure")
pathlib.Path(sys.argv[1]).with_name("source-acceptance.json").write_text(
    json.dumps({"theorem_axioms": profiles, "forbidden": False}, indent=2) + "\n"
)
PY
