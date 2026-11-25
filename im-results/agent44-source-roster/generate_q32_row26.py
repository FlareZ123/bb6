#!/usr/bin/env python3
"""Complete candidate audit of exact q32 queue row 26."""
from collections import Counter
import json
import generate_q32_slice as core

ROW = 26
TABLE = "1RB1RD_1RC0LC_0LA---_1LA0LB_------_------"
EXTRA_DFA = (0, 1, 0, 2, 3, 2, 0, 2)

def main():
    rows, _, todo = core.source_roster()
    p = rows[ROW]
    assert core.fmt(p) == TABLE and p in todo[12:]
    core.B = 46
    core.DFAS = [(rev, dfa) for rev, dfa in core.DFAS if len(dfa) <= 6]
    core.DFAS.append((0, EXTRA_DFA))
    stats, unresolved = Counter(), []
    tree = core.build(p, stats, unresolved)
    assert not unresolved, [core.fmt(x) for x in unresolved]
    assert stats == Counter(split=371, cycle=7140, last=1362, far=32, max_n=40), stats
    assert core.emit_one(ROW, p, tree, unresolved) == "Q32Slice26"
    record = {"queue_index": ROW, "table": TABLE, "bound": core.B,
              "stats": dict(stats), "unresolved": [],
              "extra_dfa": list(EXTRA_DFA)}
    (core.HERE / "Q32Row26Manifest.json").write_text(
        json.dumps(record, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(record))

if __name__ == "__main__":
    main()
