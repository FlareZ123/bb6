#!/usr/bin/env python3
"""Cross-product SAT-discovered stack automata over the remaining Raw118 hard rows.

This is a search heuristic only. Every emitted candidate is independently checked
by the original-source TreeBiDFA theorem in Lean.
"""
from pathlib import Path
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent
IM = HERE.parent
A1 = IM / "agent1-bidfa-sat"
A16 = IM / "agent16-raw118"
sys.path.insert(0, str(A16))

from bidfa_emit import witness
from tree_emit import emit

OPEN_SHA = "00b82e8ded916fb719ebfd627d29da4bbf86659039b3b7889ff60a3f9ae396f9"
MAX_STATES = 1800
MAX_EDGES = 3000
MAX_EMIT = 20
DIGITS = "0123456789abcdefghijklmnopqrstuvwxyz"


def code(xs):
    return "".join(DIGITS[int(x)] for x in xs)


def main(work: Path) -> None:
    raw = (work / "open.txt").read_bytes()
    assert hashlib.sha256(raw).hexdigest() == OPEN_SHA
    rows = raw.decode().splitlines()
    assert len(rows) == 6085

    bank_hits = json.loads((A1 / "raw118-sat-hits.json").read_text())
    sat_ids = {int(x["index"]) for x in bank_hits}
    assert len(sat_ids) == 11
    wide_ids = {int(i) for i in json.loads((A1 / "raw118-wide-widths.json").read_text())}
    assert len(wide_ids) == 47 and not (wide_ids & sat_ids)
    automata = {
        tuple(int(v) for v in x[side])
        for x in bank_hits for side in ("left", "right")
    }
    automata = sorted(automata, key=lambda d: (len(d), d))
    assert len(automata) >= 20, len(automata)

    treebank = json.loads((A16 / "Raw118TreeBank.json").read_text())
    targets = sorted(set(int(i) for i in treebank["target_indices"]) - sat_ids - wide_ids)
    assert len(treebank["target_indices"]) == 87
    assert len(targets) == 29, len(targets)

    pairs = [(dl, dr) for dl in automata for dr in automata]
    print(
        f"Raw118 SAT cross-bank: sat_hits={len(sat_ids)} "
        f"unique_automata={len(automata)} pairs={len(pairs)} "
        f"remaining_targets={len(targets)}"
    )

    found = []
    tested = 0
    for index in targets:
        table = rows[index]
        best = None
        for dl, dr in pairs:
            tested += 1
            try:
                edges, states = witness(table, list(dl), list(dr))
            except ValueError:
                continue
            state_count = len(states)
            edge_count = sum(len(e) for e in edges)
            if state_count > MAX_STATES or edge_count > MAX_EDGES:
                continue
            score = (state_count + edge_count, state_count, edge_count)
            if best is None or score < best["score"]:
                best = {
                    "index": index,
                    "table": table,
                    "left": list(dl),
                    "right": list(dr),
                    "states": state_count,
                    "edges": edge_count,
                    "score": list(score),
                }
        if best is not None:
            found.append(best)
            print(
                "HIT", index, "states", best["states"],
                "edges", best["edges"], table
            )

    found.sort(key=lambda x: (x["score"], x["index"]))
    emitted = found[:MAX_EMIT]
    header = (
        "import TreeBiDFA\n"
        "set_option maxRecDepth 100000\n"
        "set_option maxHeartbeats 0\n"
        "namespace BB6Coverage.Agent40Raw118CrossBank\n"
        "open BB6Coverage Agent16BiDFA.TreeCheck\n"
    )
    chunks = [header]
    for hit in emitted:
        source, states, edges = emit(
            hit["index"], hit["table"], hit["left"], hit["right"]
        )
        assert states == hit["states"] and edges == hit["edges"]
        chunks.append(source)
    chunks.append("end BB6Coverage.Agent40Raw118CrossBank\n")
    lean_source = "\n\n".join(chunks)
    (HERE / "Raw118SatCrossBank.lean").write_text(lean_source)
    manifest = {
        "open_sha256": OPEN_SHA,
        "sat_seed_indices": sorted(sat_ids),
        "automata_count": len(automata),
        "pair_count": len(pairs),
        "target_count": len(targets),
        "target_indices": targets,
        "pairs_tested": tested,
        "found_count": len(found),
        "emitted_count": len(emitted),
        "emitted": [
            {
                "index": x["index"],
                "table": x["table"],
                "left": code(x["left"]),
                "right": code(x["right"]),
                "states": x["states"],
                "edges": x["edges"],
                "score": x["score"],
            }
            for x in emitted
        ],
        "source_sha256": hashlib.sha256(lean_source.encode()).hexdigest(),
    }
    (HERE / "Raw118SatCrossBank.json").write_text(
        json.dumps(manifest, indent=2) + "\n"
    )
    print(
        f"cross-bank found={len(found)} emitted={len(emitted)} "
        f"source_sha256={manifest['source_sha256']}"
    )


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("usage: search_sat_crossbank.py WORKDIR")
    main(Path(sys.argv[1]))
