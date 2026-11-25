#!/usr/bin/env python3
"""Emit raw13 BiDFA certificates; Lean remains the final proof checker."""
from pathlib import Path
import json
import sys

ROOT = Path(__file__).resolve().parent
IM = ROOT.parent
sys.path.insert(0, str(IM / "agent16-raw118"))
from bidfa_emit import emit

rows = {}
for line in (ROOT / "raw13-open-residuals.txt").read_text().splitlines():
    ident, table = line.split()
    rows[int(ident)] = table

spec = json.loads((ROOT / "raw13-bidfa-spec.json").read_text())
if spec["source_count"] != len(rows):
    raise SystemExit("raw13 residual source count changed")
if spec["open_sha256"] != __import__("hashlib").sha256(
    (ROOT / "raw13-open-residuals.txt").read_bytes()
).hexdigest():
    raise SystemExit("raw13 residual source digest changed")

out = [
    "import BiDFA",
    "set_option maxRecDepth 100000",
    "set_option maxHeartbeats 0",
    "namespace BB6.Agent46Raw13BiDFAAudit",
    "open BB6Coverage BB6Coverage.Agent16BiDFA",
]
for key, (dl, dr, n, e) in sorted(spec["bidfa"].items(), key=lambda kv: int(kv[0])):
    ident = int(key)
    code, actual_n, actual_e = emit(ident, rows[ident], dl, dr)
    if (actual_n, actual_e) != (n, e):
        raise SystemExit(
            f"residual {ident}: witness changed {(actual_n, actual_e)} != {(n, e)}"
        )
    out.append(code)
out.append("end BB6.Agent46Raw13BiDFAAudit")
(ROOT / "Agent46Raw13BiDFAAudit.lean").write_text("\n".join(out) + "\n")
print(f"emitted {len(spec['bidfa'])} raw13 BiDFA certificates")
