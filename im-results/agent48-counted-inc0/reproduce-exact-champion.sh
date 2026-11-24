#!/usr/bin/env bash
# Run from the checkout root with Lean 4.36.0-rc2 installed.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$ROOT"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
mkdir "$work/imports"
export BB6_CHAMPION_WORK="$work"
python3 - <<'PY'
import base64, io, lzma, os, pathlib, tarfile
root = pathlib.Path(os.environ["BB6_CHAMPION_WORK"]) / "imports"
# Only the two authoritative compressed imports are needed.
p = pathlib.Path("im-results/agent42-champion-terminal")
with tarfile.open(fileobj=io.BytesIO(base64.b64decode((p/"TerminalProofs.tar.xz.b64").read_text())), mode="r:xz") as a:
    member = next(m for m in a.getmembers() if pathlib.PurePosixPath(m.name).name == "TerminalFinish.lean")
    (root/"TerminalFinish.lean").write_bytes(a.extractfile(member).read())
(root/"TerminalLeft.lean").write_bytes(lzma.decompress(base64.b64decode((p/"TerminalLeftExact.lean.xz.b64").read_text())))
# Agent 13 raw coverage semantics is an authoritative compressed source.
q = pathlib.Path("im-results/agent13-coverage/BB6Coverage.lean.xz.b64")
(root/"BB6Coverage.lean").write_bytes(lzma.decompress(base64.b64decode(q.read_text())))
PY
printf '%s  %s\n' fbe453c5c170029885ba328bfdd9262600f918a8ce2371c60ecbb843897fd6bd "$work/imports/BB6Coverage.lean" | sha256sum -c -
printf '%s  %s\n' 12329036c66c3846f9261167b8f9aebd1778d9b6ea6044309956c2fa0b3e49b7 "$work/imports/TerminalFinish.lean" | sha256sum -c -
printf '%s  %s\n' 1bce2075fc4e0cd7d740fb71b3796088b190ddb6766e04640d992dadd1b650ff "$work/imports/TerminalLeft.lean" | sha256sum -c -
lean --version
python3 tools/lean_compile_closure.py \
  im-results/agent48-counted-inc0/TM63RawUpperInterface.lean \
  im-results/agent48-counted-inc0/Enumerate62Potential.lean \
  --source-root "$work/imports" \
  --override TerminalBridge=im-results/agent42-champion-terminal/TerminalBridge.lean \
  --override OuterLCIncPrelude=im-results/agent8-counted-reset/OuterLCIncPrelude.lean \
  --override M0OddResidueSeven=im-results/agent41-m0-n16r7/M0OddResidueSeven.lean \
  --override M0EvenEightValuationEncoding=im-results/agent48-counted-inc0/M0EvenEightValuationEncoding.lean \
  --override M2EvenResidueTwo=im-results/agent42-champion-terminal/M2EvenResidueTwo.lean \
  --workdir "$work/build" --jobs "${JOBS:-8}" | tee "$work/compile.log"
python3 - "$work/compile.log" <<'PY'
import pathlib, re, sys
log = pathlib.Path(sys.argv[1]).read_text()
allowed = {"propext", "Classical.choice", "Quot.sound"}
for name in ("champion_halts_exact", "champion_attained_exact", "champion_maximum_of_cover",
 "champion_raw_halts_exact", "champion_weighted_bound", "exact_BB6_from_cover",
 "exact_BB6_from_weighted_cover", "exact_BB6_from_tnf_certificate",
 "expandProjection_length", "expandProjection_length_le_24", "expandProjection_mass_lt",
 "expandProjection'_mass_lt", "update_active_mass_lt", "runUpdates_active_empty_of_bound",
 "bfsRound_total_mass_le", "fourBfsPasses_total_mass_le", "q0_total_mass_le",
 "chunk_active_mass_le", "every_chunk_drains"):
    m = re.search(r"'[^']*\."+name+r"' depends on axioms: \[([^\]]*)\]", log)
    if not m:
        raise SystemExit("missing axiom audit: "+name)
    used = {x.strip() for x in m.group(1).split(",") if x.strip()}
    if not used <= allowed:
        raise SystemExit(f"nonstandard axioms: {name}: {used-allowed}")
    print(f"{name}: {sorted(used)}")
PY
