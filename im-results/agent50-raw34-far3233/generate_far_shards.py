#!/usr/bin/env python3
"""Generate Lean source proofs for the size<=4 FAR certificates on the exact
Raw34 D1=0LF,F0=0LD 3,233-machine frontier.

Inputs are deliberately independent:
* hard3233.txt is emitted by census_f0ld.cpp;
* far.jsonl is emitted by far.cpp.

Every FAR hit is rechecked by Lean's FastFAR theorem against the literal source
table. The generator also records ordered/canonical SHA256 hashes of the census
rows so downstream source-cover generators can bind to the exact same set.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def compact_json(x) -> str:
    return json.dumps(x, separators=(",", ":"))


def sha_rows(rows: list[list[int]]) -> str:
    return hashlib.sha256((compact_json(rows) + "\n").encode()).hexdigest()


def lean_list(xs) -> str:
    return "[" + ",".join(str(x) for x in xs) + "]"


def parse_hard(path: Path) -> list[list[int]]:
    rows: list[list[int]] = []
    for line_no, line in enumerate(path.read_text().splitlines(), 1):
        if not line.strip():
            continue
        xs = [int(x) for x in line.split()]
        if len(xs) != 13:
            raise ValueError(f"{path}:{line_no}: expected id + 12 codes")
        ident, row = xs[0], xs[1:]
        if ident != len(rows):
            raise ValueError(f"{path}:{line_no}: expected id {len(rows)}, got {ident}")
        if any(x <= 0 for x in row):
            raise ValueError(f"{path}:{line_no}: frontier row is not complete: {row}")
        rows.append(row)
    if len(rows) != 3233:
        raise ValueError(f"expected 3233 rows, got {len(rows)}")
    if len({tuple(r) for r in rows}) != len(rows):
        raise ValueError("hard frontier contains duplicate complete machines")
    return rows


def parse_far(path: Path, rows: list[list[int]]) -> tuple[list[dict], list[int]]:
    data = [json.loads(x) for x in path.read_text().splitlines() if x.strip()]
    if len(data) != len(rows):
        raise ValueError(f"expected {len(rows)} FAR rows, got {len(data)}")
    hits: list[dict] = []
    misses: list[int] = []
    for i, x in enumerate(data):
        if x.get("id") != i:
            raise ValueError(f"FAR id mismatch at {i}: {x.get('id')}")
        if "d" not in x:
            misses.append(i)
            continue
        d = int(x["d"])
        if d < 1 or d > 4:
            raise ValueError(f"unexpected FAR size {d} at {i}")
        if len(x["dfa"]) != 2 * d:
            raise ValueError(f"bad DFA length at {i}")
        n = 6 * d + 1
        if len(x["m0"]) != n or len(x["m1"]) != n:
            raise ValueError(f"bad mask vector length at {i}")
        y = dict(x)
        y["codes"] = rows[i]
        hits.append(y)
    if len(hits) != 3065 or len(misses) != 168:
        raise ValueError(f"expected 3065 hits/168 misses, got {len(hits)}/{len(misses)}")
    return hits, misses


def proposition(name: str) -> str:
    return f"(∀ m : Machine, compatible {name} m → NeverHalts m)"


def nested_and(names: list[str]) -> str:
    assert names
    if len(names) == 1:
        return proposition(names[0])
    return " ∧\n    ".join(proposition(n) for n in names)


def nested_constructor(theorems: list[str]) -> str:
    assert theorems
    if len(theorems) == 1:
        return theorems[0]
    # Lean parses ⟨a,b,c⟩ for nested constructor chains poorly when the target is
    # right-associated And, so emit explicit right nesting.
    acc = theorems[-1]
    for thm in reversed(theorems[:-1]):
        acc = f"⟨{thm}, {acc}⟩"
    return acc


def emit_shard(out: Path, shard: int, xs: list[dict]) -> dict:
    module = f"Raw34FAR3233Shard{shard:03d}"
    ns = f"BB6.Agent50Raw34FAR3233.{module}"
    body = [
        "import FastFAR",
        "import Raw34Plan",
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 0",
        f"namespace {ns}",
        "open BB6Coverage BB6Coverage.FAR BB6.Agent50Raw34Plan",
        "",
    ]
    pnames: list[str] = []
    thms: list[str] = []
    ids: list[int] = []
    for x in xs:
        ident = int(x["id"])
        ids.append(ident)
        p = f"p{ident}"
        c = f"c{ident}"
        ok = f"ok{ident}"
        never = f"never{ident}"
        pnames.append(p)
        thms.append(never)
        d = int(x["d"])
        reflected = bool(x["reflect"])
        pp = f"(reflectPartial {p})" if reflected else p
        body += [
            f"def {p} : PartialMachine := table {lean_list(x['codes'])}",
            f"def {c} : Data {d} := ⟨0,{lean_list(x['dfa'])},{lean_list(x['m0'])},{lean_list(x['m1'])},{int(x['z'])}⟩",
            f"theorem {ok} : ({c}).fastValid {pp} = true := by decide +kernel",
        ]
        sound = f"({c}).sound {pp} (({c}).fastValid_sound {pp} {ok})"
        if reflected:
            proof = f"reflectNever m ({sound} (reflectTable m) (reflectCompatible {p} m hm))"
        else:
            proof = f"{sound} m hm"
        body += [
            f"theorem {never} (m : Machine) (hm : compatible {p} m) : NeverHalts m := {proof}",
            "",
        ]
    body += [
        f"theorem hit_count : {len(xs)} = {len(xs)} := by rfl",
        "theorem all_never :",
        "    " + nested_and(pnames) + " :=",
        "  " + nested_constructor(thms),
        "#print axioms all_never",
        f"end {ns}",
        "",
    ]
    (out / f"{module}.lean").write_text("\n".join(body))
    return {"module": module, "namespace": ns, "size": len(xs), "ids": ids}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--hard", required=True)
    ap.add_argument("--far", required=True)
    ap.add_argument("--output", required=True)
    ap.add_argument("--shard-size", type=int, default=40)
    args = ap.parse_args()
    if args.shard_size <= 0:
        raise ValueError("shard size must be positive")

    hard = Path(args.hard)
    far = Path(args.far)
    out = Path(args.output)
    out.mkdir(parents=True, exist_ok=True)

    rows = parse_hard(hard)
    hits, misses = parse_far(far, rows)
    canonical = sorted(rows)

    modules = []
    for start in range(0, len(hits), args.shard_size):
        modules.append(emit_shard(out, len(modules), hits[start:start + args.shard_size]))

    hit_ids = [int(x["id"]) for x in hits]
    miss_rows = [rows[i] for i in misses]
    manifest = {
        "status": "source-generated FAR certificate bank; Lean acceptance required",
        "parent": "1RB---_1RC---_0RD0LF_1LC---_------_0LD---",
        "frontierMachines": len(rows),
        "orderedFrontierSha256": sha_rows(rows),
        "canonicalFrontierSha256": sha_rows(canonical),
        "farHits": len(hits),
        "misses": len(misses),
        "hitIdsSha256": hashlib.sha256((compact_json(hit_ids) + "\n").encode()).hexdigest(),
        "missIds": misses,
        "missRows": miss_rows,
        "canonicalMissSha256": sha_rows(sorted(miss_rows)),
        "shardSize": args.shard_size,
        "modules": modules,
    }
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    (out / "missRows.json").write_text(compact_json(miss_rows) + "\n")
    print(json.dumps({k: v for k, v in manifest.items() if k not in ("missRows", "modules")}, indent=2))


if __name__ == "__main__":
    main()
