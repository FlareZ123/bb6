#!/usr/bin/env python3
"""Run the committed Raw118 symbolic generators and emit one import root."""
from pathlib import Path
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent
IM = HERE.parent
sys.path.insert(0, str(IM / "agent31-three-hole-tnf"))
sys.path.insert(0, str(IM / "agent47-raw114-cut"))

import generate_symbolic

def main(work: Path) -> None:
    raw = (work / "open.txt").read_bytes()
    rows = raw.decode().splitlines()
    assert len(rows) == 6085
    candidates = json.loads((work / "candidates.json").read_text())
    hard = {int(i) for i in candidates["hard"]}
    modules, claims = generate_symbolic.generate(rows)
    indices = [int(i) for i, _ in claims]
    assert len(indices) == 105, len(indices)
    assert len(set(indices)) == 105
    assert set(indices) <= hard, sorted(set(indices) - hard)
    (HERE / "Raw118Symbolic.lean").write_text(
        "\n".join(f"import {name}" for name in modules) + "\n"
    )
    manifest = {
        "open_sha256": hashlib.sha256(raw).hexdigest(),
        "hard_count": len(hard),
        "certificate_count": len(indices),
        "indices": indices,
        "claims": [{"index": int(i), "namespace": str(ns)} for i, ns in claims],
        "modules": modules,
    }
    (HERE / "Raw118Symbolic.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"Raw118 symbolic source candidates: {len(indices)} in {len(modules)} modules")

if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("usage: emit_symbolic.py WORKDIR")
    main(Path(sys.argv[1]))
