#!/usr/bin/env python3
"""Generate and aggregate the 679 Raw118 sparse n-gram certificates."""
from pathlib import Path
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent
IM = HERE.parent
sys.path.insert(0, str(IM / "agent47-raw111-cut"))
from generate_sparse import generate

def main(work: Path) -> None:
    raw = (work / "open.txt").read_bytes()
    rows = raw.decode().splitlines()
    assert len(rows) == 6085
    candidates = json.loads((work / "candidates.json").read_text())
    hard = {int(i) for i in candidates["hard"]}
    ng = {int(i): (int(v[0]), int(v[1]))
          for i, v in candidates["ngram"].items()}
    assert len(ng) == 679, len(ng)
    assert not (set(ng) & hard)
    modules, claims = generate(rows, ng, work)
    indices = [int(i) for i, _ in claims]
    assert len(indices) == 679, len(indices)
    assert len(set(indices)) == 679
    assert set(indices) == set(ng)
    (HERE / "Raw118Sparse.lean").write_text(
        "\n".join(f"import {name}" for name in modules) + "\n"
    )
    manifest = {
        "open_sha256": hashlib.sha256(raw).hexdigest(),
        "ngram_count": len(ng),
        "indices": indices,
        "modules": modules,
    }
    (HERE / "Raw118Sparse.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"Raw118 sparse source candidates: {len(indices)} in {len(modules)} modules")

if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("usage: emit_sparse.py WORKDIR")
    main(Path(sys.argv[1]))
