"""Recreate the checked greedy-compatible raw60 leaf proofs and full child source.

The compressed JSON stores only finite DFA transition arrays and search metrics.
Every theorem is generated using the original IndexedBiDFA checker, whose
closure obligations are decided in Lean. The search does not enter the TCB.
"""
import base64
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import zlib

import generate_compact as base

ROOT = Path(__file__).resolve().parent
PAYLOAD_SHA256 = "2806e08c57cb5b713282615f38e92a71aee2d6722e6b96b119c8036d42fae688"
EXPECTED = {"1LF": (2160, 150, 257, 503), "1RE": (3718, 101, 277, 485)}

def load():
    raw = zlib.decompress(base64.b64decode((ROOT/"greedy-compact.b64").read_text()))
    assert hashlib.sha256(raw).hexdigest() == PAYLOAD_SHA256
    return json.loads(raw)

def generate(child):
    i, table, _, _, module, _ = base.CASES[child]
    record = load()[child]
    assert record["table"] == table
    d = record["d"]
    with tempfile.TemporaryDirectory() as temp:
        tmp = Path(temp)
        states, edges = base.emit(i, table, *d, tmp)
        actual = (states, len(d[0])//2, len(d[1])//2, edges)
        assert actual == EXPECTED[child], (child, actual)
        old = f"Raw118Wide{i}"
        old_ns = f"BB6Coverage.Agent1BiDFAWide.M{i}"
        new_ns = f"BB6.Agent47SparseNGram.{module}"
        for f in tmp.glob("*.lean"):
            source = f.read_text().replace(old_ns, new_ns).replace(old, module)
            (ROOT/f.name.replace(old,module)).write_text(source)
        print(child, "greedy quotient", actual)

if __name__ == "__main__":
    child = sys.argv[1]
    if len(sys.argv) > 2 and sys.argv[2] == "--leaf-only":
        generate(child)
    else:
        base.generate = generate
        base.full_child(child)
