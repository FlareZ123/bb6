#!/usr/bin/env python3
"""Derive the *minimal* two-exception spine of the Raw139 D0=1LF TNF tree.

The original finite query-tree simulator is used only to propose certificates.
Every proposed ordinary region still requires original-source Lean checking.
In particular, this does not assume either extraordinary child's Cover.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
CENSUS = HERE / "census-d0lf1.json"
REPLAY = ROOT / "im-results/agent48-raw139-e0-0re/replay.cpp"
TARGETS = (2265, 3506)
ORDER = tuple(4 * q + 2 * w + r
              for w in range(2) for r in range(2) for q in range(6))


def replay(source):
    with tempfile.TemporaryDirectory(prefix="raw139-twobound-") as temp:
        exe = Path(temp) / "replay"
        output = Path(temp) / "part.json"
        subprocess.run(["g++", "-std=c++17", "-O3", str(REPLAY),
                        "-o", str(exe)], check=True)
        args = [str(exe), str(source["limit"]), str(source["maxd"])]
        args += [str(v) for v in source["parent"]]
        with output.open("wb") as out:
            run = subprocess.run(args, stdout=out, stderr=subprocess.PIPE,
                                 check=True)
        print(run.stderr.decode(errors="replace").strip())
        blob = output.read_bytes()
        return json.loads(blob), hashlib.sha256(blob).hexdigest()


def target_path(node, table):
    """Follow the target's assigned instructions, NOT an exhaustive search."""
    indexes = []
    while node[0] == "split":
        _, step, slot, children = node
        code = table[slot]
        if code not in ORDER:
            raise AssertionError(
                f"target has unassigned slot {slot} at query step {step}")
        k = ORDER.index(code)
        indexes.append(k)
        node = children[k]
    if node != ["open", table]:
        raise AssertionError("target table is not at the projected open leaf")
    return indexes


def stats(node, cache):
    identity = id(node)
    if identity in cache:
        return cache[identity]
    kind = node[0]
    counts = Counter({kind: 1})
    if kind == "split":
        for child in node[3]:
            counts.update(stats(child, cache))
    cache[identity] = counts
    return counts


def build_plan(part, census, tree_hash):
    assert part["counts"] == census["counts"]
    assert part["open"] == census["open"], (
        "the exact simulation opening order differs from saved recipe indexes")
    assert len(census["open"]) == 4875
    assert len(census["recipes"]) == 4873
    assert set(TARGETS) == (set(range(len(census["open"]))) -
                            set(map(int, census["recipes"])))
    assert sum(v[0] == "split" for v in census["recipes"].values()) == 8

    paths = {str(i): target_path(part["tree"], census["open"][i])
             for i in TARGETS}
    exception_path_set = {tuple(path[:depth])
                          for path in paths.values()
                          for depth in range(len(path))}
    terminal_set = {tuple(path) for path in paths.values()}
    cache = {}
    regions = []
    spine = []

    def visit(node, table, prefix):
        if tuple(prefix) not in exception_path_set:
            c = stats(node, cache)
            regions.append({
                "path": list(prefix), "table": list(table),
                "nodes": sum(c.values()), "open": c["open"],
                "split": c["split"], "cycle": c["cycle"],
                "last": c["last"], "far": c["far"]})
            return
        if node[0] != "split":
            raise AssertionError("exception path does not end at split")
        _, step, slot, children = node
        assert table[slot] == 24
        special = [i for i in range(24)
                   if tuple(prefix + [i]) in exception_path_set |
                   terminal_set]
        assert special
        spine.append({"path": list(prefix), "query_step": step,
                      "query_slot": slot, "exception_children": special,
                      "table": list(table)})
        for i, child in enumerate(children):
            next_table = list(table)
            next_table[slot] = ORDER[i]
            if tuple(prefix + [i]) in terminal_set:
                expected = TARGETS[[paths[str(k)] for k in TARGETS]
                                   .index(prefix + [i])]
                if child != ["open", census["open"][expected]]:
                    raise AssertionError("exceptional leaf table mismatch")
            else:
                visit(child, next_table, prefix + [i])

    visit(part["tree"], census["parent"], [])
    regions.sort(key=lambda d: tuple(d["path"]))
    assert sum(d["open"] for d in regions) == 4873
    assert sum(d["split"] for d in regions) + len(spine) == 31277
    assert sum(d["cycle"] for d in regions) == 542177
    assert sum(d["last"] for d in regions) == 146564
    assert sum(d["far"] for d in regions) == 25756
    assert len(regions) + len(spine) * 24 - (len(spine) - 1) >= 1
    # The two exceptional leaves and all ordinary subtrees partition the
    # complete source finite tree, with no omitted or duplicate leaf.
    return {
        "parent": census["parent"], "limit": census["limit"],
        "maxd": census["maxd"], "replay_sha256": tree_hash,
        "counts": census["counts"], "exception_indexes": TARGETS,
        "exception_tables": {str(i): census["open"][i] for i in TARGETS},
        "exception_paths": paths, "spine": spine,
        "ordinary_regions": regions, "ordinary_regions_count": len(regions),
        "ordinary_region_node_sum": sum(d["nodes"] for d in regions)
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    census = json.loads(CENSUS.read_text())
    part, sha = replay(census)
    plan = build_plan(part, census, sha)
    print("Exception paths:", plan["exception_paths"])
    print("Unique exceptional spine nodes:", len(plan["spine"]))
    print("Disjoint ordinary regions:", len(plan["ordinary_regions"]))
    print("Ordinary open leaves:", sum(x["open"]
                                       for x in plan["ordinary_regions"]))
    if args.out:
        args.out.write_text(json.dumps(plan, indent=2) + "\n")
        print("Wrote reproducible source-generator plan to", args.out)


if __name__ == "__main__":
    main()
