#!/usr/bin/env python3
"""Replay a small bank of proven two-sided stack summaries over Raw118 hard leaves.

The search is untrusted. Every emitted certificate is checked by TreeBiDFA in Lean.
"""
from pathlib import Path
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent
IM = HERE.parent
AG40 = IM / "agent40-raw118-independent"
sys.path.insert(0, str(AG40))

from bidfa_emit import EXAMPLES as OLD_EXAMPLES, witness
from tree_emit import EXAMPLES as TREE_EXAMPLES, emit
from independent import ROWS as INDEPENDENT_ROWS
from generate_recursive_counter import CASES as RECURSIVE_CASES
from generate_recursive_more import CASES as RECURSIVE_MORE_CASES
sys.path.insert(0, str(IM / "agent31-three-hole-tnf"))
sys.path.insert(0, str(IM / "agent47-raw114-cut"))
import generate_symbolic as symbolic

SHA = "00b82e8ded916fb719ebfd627d29da4bbf86659039b3b7889ff60a3f9ae396f9"
MAX_STATES = 1800
MAX_HITS = 12


def main(work: Path) -> None:
    raw = (work / "open.txt").read_bytes()
    assert hashlib.sha256(raw).hexdigest() == SHA
    rows = raw.decode().splitlines()
    assert len(rows) == 6085
    candidates = json.loads((work / "candidates.json").read_text())
    hard = [int(i) for i in candidates["hard"]]
    assert len(hard) == 274, len(hard)
    late_long = [
        {"index": int(i), "steps": int(v[0]), "slot": int(v[1])}
        for i, v in candidates["late"].items() if int(v[0]) > 10000
    ]
    print("late-long leaves:", late_long)

    phase_ids = {
        int(line.split()[0])
        for line in (AG40 / "phase_candidates.tsv").read_text().splitlines()
        if line.strip()
    }
    recursive_ids = {int(x[0]) for x in RECURSIVE_CASES + RECURSIVE_MORE_CASES}
    symbolic_ids = set(symbolic.SINGLE) | set(symbolic.MULTI)
    groups = {
        "symbolic": symbolic_ids,
        "independent": set(INDEPENDENT_ROWS),
        "phasegraph": phase_ids,
        "recursive": recursive_ids,
        "bidfa": {int(x[0]) for x in OLD_EXAMPLES},
        "tree": {int(x[0]) for x in TREE_EXAMPLES},
    }
    names = list(groups)
    for i, left_name in enumerate(names):
        for right_name in names[i + 1:]:
            overlap = groups[left_name] & groups[right_name]
            assert not overlap, (left_name, right_name, sorted(overlap))
    known = set().union(*groups.values())
    assert len(known) == 187, len(known)
    assert known <= set(hard), sorted(known - set(hard))
    targets = [i for i in hard if i not in known]
    assert len(targets) == 87, len(targets)
    assert all(rows[i].count("---") == 1 for i in targets)

    pairs = []
    seen_pairs = set()
    for i, _table, left, right, *_ in OLD_EXAMPLES + TREE_EXAMPLES:
        dl = tuple(int(c, 36) for c in left)
        dr = tuple(int(c, 36) for c in right)
        key = (dl, dr)
        if key not in seen_pairs:
            seen_pairs.add(key)
            pairs.append((f"pair-{i}", dl, dr))

    # The four phase-aware witnesses contributed genuinely different left and
    # right summaries. Cross their summaries to test a small product bank.
    lefts = {int(i): tuple(int(c, 36) for c in left)
             for i, _t, left, _right, *_ in TREE_EXAMPLES}
    rights = {int(i): tuple(int(c, 36) for c in right)
              for i, _t, _left, right, *_ in TREE_EXAMPLES}
    for li, dl in lefts.items():
        for ri, dr in rights.items():
            key = (dl, dr)
            if key not in seen_pairs:
                seen_pairs.add(key)
                pairs.append((f"L{li}-R{ri}", dl, dr))

    print(f"Raw118 tree-bank search: hard={len(hard)} known={len(known)} "
          f"targets={len(targets)} automata_pairs={len(pairs)}")

    hits = []
    for index in targets:
        table = rows[index]
        best = None
        for label, dl, dr in pairs:
            try:
                edges, states = witness(table, list(dl), list(dr))
            except ValueError:
                continue
            edge_count = sum(len(e) for e in edges)
            if len(states) > MAX_STATES:
                continue
            score = (len(states) + edge_count, len(states), edge_count)
            if best is None or score < best[0]:
                best = (score, label, dl, dr, len(states), edge_count)
        if best is not None:
            score, label, dl, dr, state_count, edge_count = best
            hits.append({
                "index": index,
                "table": table,
                "pair": label,
                "left": "".join("0123456789abcdefghijklmnopqrstuvwxyz"[x] for x in dl),
                "right": "".join("0123456789abcdefghijklmnopqrstuvwxyz"[x] for x in dr),
                "states": state_count,
                "edges": edge_count,
                "holes": table.count("---"),
                "score": list(score),
            })

    hits.sort(key=lambda x: (x["score"], x["index"]))
    emitted = hits[:MAX_HITS]
    header = (
        "import TreeBiDFA\n"
        "set_option maxRecDepth 100000\n"
        "set_option maxHeartbeats 0\n"
        "namespace BB6Coverage.Agent16BiDFA.Raw118TreeBank\n"
        "open BB6Coverage Agent16BiDFA.TreeCheck\n"
    )
    chunks = [header]
    for hit in emitted:
        pair = next((p for p in pairs if p[0] == hit["pair"]), None)
        if pair is None:
            # Cross-pair labels are recovered from their exact encoded strings.
            dl = tuple(int(c, 36) for c in hit["left"])
            dr = tuple(int(c, 36) for c in hit["right"])
        else:
            _, dl, dr = pair
        code, states, edges = emit(hit["index"], hit["table"], list(dl), list(dr))
        assert states == hit["states"] and edges == hit["edges"]
        chunks.append(code)
    chunks.append("end BB6Coverage.Agent16BiDFA.Raw118TreeBank\n")
    source = "\n\n".join(chunks)
    (HERE / "Raw118TreeBank.lean").write_text(source)
    manifest = {
        "open_sha256": SHA,
        "hard_count": len(hard),
        "known_index_count": len(known),
        "target_count": len(targets),
        "target_indices": targets,
        "late_long": late_long,
        "automata_pair_count": len(pairs),
        "found_count": len(hits),
        "emitted_count": len(emitted),
        "emitted": emitted,
        "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
    }
    (HERE / "Raw118TreeBank.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"tree-bank hits={len(hits)} emitted={len(emitted)} "
          f"source_sha256={manifest['source_sha256']}")
    for hit in emitted:
        print("HIT", hit["index"], hit["pair"], "states", hit["states"],
              "edges", hit["edges"], "holes", hit["holes"], hit["table"])


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("usage: search_tree_bank.py WORKDIR")
    main(Path(sys.argv[1]))
