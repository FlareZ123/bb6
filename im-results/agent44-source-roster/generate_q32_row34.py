#!/usr/bin/env python3
"""Exact q32 row 34 audit: small FAR bank and two symbolic stack leaves."""
from collections import Counter
import generate_q32_slice as core

ROW = 34
ROOT = "1RB1RD_1RC0LE_0LA---_1LA0LB_------_------"
STACK = {
    core.parse("1RB1RD_1RC0LE_0LA0RC_1LA0LB_0LF1LE_1LB---"): "true",
    core.parse("1RB1RD_1RC0LE_0LA0RC_1LA0LB_0LF1LE_1LC---"): "false",
}
BANK = [
    (0,0,1,0,2,3,4,3,3,3,3),
    (0,0,1,2,3,2,2,0,3),
    (0,0,1,2,3,2,2,4,2,5,2,2,1),
    (0,0,1,2,3,4,1,4,4,4,4),
    (0,0,1,2,3,4,4,0,1,4,4),
    (1,0,1,0,2,1,3,4,3,0,3),
    (1,0,1,0,2,1,3,4,4,4,4),
    (1,0,1,0,2,3,1,0,4,3,4),
    (1,0,1,2,2,0,3,2,3),
    (1,0,1,2,2,0,3,2,4,2,4),
    (1,0,1,2,3,0,1,0,1),
    (1,0,1,2,3,0,1,4,4,4,4),
    (1,0,1,2,3,0,3,4,4,4,4),
    (1,0,1,2,3,0,4,2,1,2,4),
    (1,0,1,2,3,2,2,0,4,2,2),
    (1,0,1,2,3,2,2,4,5,0,1,2,2),
]

def main():
    rows, _, todo = core.source_roster()
    p = rows[ROW]
    assert p == core.parse(ROOT) and p in todo[12:]
    core.B = 129
    core.DFAS = [(rev,d) for rev,d in core.DFAS if len(d) <= 6]
    core.DFAS += [(b[0], tuple(b[1:])) for b in BANK]
    stats = Counter()
    residuals = []
    tree = core.build(p, stats, residuals)
    assert len(residuals) == 2 and set(residuals) == set(STACK), (
        stats, [core.fmt(q) for q in residuals])
    def discharge(t):
        if t[0] == "open":
            return ("proven", STACK[t[1]])
        if t[0] == "split":
            return (*t[:3], [discharge(k) for k in t[3]])
        return t
    original_audit = core.audit
    original_emit = core.emit
    ns = "BB6.Agent44Row34Stack"
    def audit(t):
        if t[0] == "proven":
            v = t[1]
            return f".proven ({ns}.p {v}) ({ns}.never {v})"
        return original_audit(t)
    def emit(name, imports, body):
        if ".proven " in body:
            imports = imports + ["Row34BinaryStack"]
        return original_emit(name, imports, body)
    core.audit = audit
    core.emit = emit
    assert core.emit_one(ROW, p, discharge(tree), []) == "Q32Slice34"
    manifest = {"queue_index": ROW, "table": ROOT, "bound": core.B,
        "discovery_counts": dict(stats), "symbolic_leaves": [core.fmt(q) for q in residuals],
        "unresolved": []}
    import json
    (core.HERE/"Q32Row34Manifest.json").write_text(json.dumps(manifest,indent=2)+"\n")
    print(json.dumps(manifest))

if __name__ == "__main__":
    main()
