#!/usr/bin/env python3
"""Compose the exact Raw34 3,233-residual Cover with source-proved FAR hits.

The generated theorem reduces the D1=0LF,F0=0LD pair parent to
DecidedBelow 128 or one of exactly 168 explicit complete residual machines.
It requires the generated Raw34PairFinal3233Cover and Raw34FAR3233Shard*
modules to be present in the same Lean source root.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


OLD_DATA = "BB6.Agent40Raw34Final3233.Data"
OLD_COVER = "BB6.Agent40Raw34Final3233.cover"
PARENT = "BB6.Agent40Raw34PairD1LF_F0LDDepth6Data.parent"


def compact_json(x) -> str:
    return json.dumps(x, separators=(",", ":"))


def sha_rows(rows: list[list[int]]) -> str:
    return hashlib.sha256((compact_json(rows) + "\n").encode()).hexdigest()


def lean_list(xs) -> str:
    return "[" + ",".join(str(x) for x in xs) + "]"


def parse_hard(path: Path) -> list[list[int]]:
    rows = []
    for line in path.read_text().splitlines():
        if not line.strip():
            continue
        xs = [int(x) for x in line.split()]
        ident, row = xs[0], xs[1:]
        if ident != len(rows) or len(row) != 12:
            raise ValueError("malformed hard frontier")
        rows.append(row)
    if len(rows) != 3233:
        raise ValueError(f"expected 3233 hard rows, got {len(rows)}")
    return rows


def parse_far(path: Path, n: int) -> list[dict]:
    xs = [json.loads(x) for x in path.read_text().splitlines() if x.strip()]
    if len(xs) != n:
        raise ValueError(f"expected {n} FAR rows, got {len(xs)}")
    for i, x in enumerate(xs):
        if x.get("id") != i:
            raise ValueError(f"FAR id mismatch at {i}")
    return xs


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--hard", required=True)
    ap.add_argument("--far", required=True)
    ap.add_argument("--far-manifest", required=True)
    ap.add_argument("--final-rows", required=True)
    ap.add_argument("--output", required=True)
    ap.add_argument("--shard-size", type=int, default=40)
    args = ap.parse_args()
    if args.shard_size <= 0:
        raise ValueError("shard size must be positive")

    hard = parse_hard(Path(args.hard))
    far = parse_far(Path(args.far), len(hard))
    far_manifest = json.loads(Path(args.far_manifest).read_text())
    final_rows = json.loads(Path(args.final_rows).read_text())
    out = Path(args.output)
    out.mkdir(parents=True, exist_ok=True)

    if len(final_rows) != 3233:
        raise ValueError(f"expected 3233 final rows, got {len(final_rows)}")
    hard_map = {tuple(r): i for i, r in enumerate(hard)}
    if len(hard_map) != 3233:
        raise ValueError("independent hard frontier contains duplicates")
    if len({tuple(r) for r in final_rows}) != 3233:
        raise ValueError("source-cover final rows contain duplicates")
    if set(hard_map) != {tuple(r) for r in final_rows}:
        only_hard = set(hard_map) - {tuple(r) for r in final_rows}
        only_final = {tuple(r) for r in final_rows} - set(hard_map)
        raise ValueError(f"frontier set mismatch: onlyHard={len(only_hard)} onlyFinal={len(only_final)}")

    id_to_ns: dict[int, str] = {}
    for mod in far_manifest["modules"]:
        for ident in mod["ids"]:
            if ident in id_to_ns:
                raise ValueError(f"duplicate FAR id {ident}")
            id_to_ns[int(ident)] = mod["namespace"]
    hit_ids = {i for i, x in enumerate(far) if "d" in x}
    miss_ids = [i for i, x in enumerate(far) if "d" not in x]
    if set(id_to_ns) != hit_ids:
        raise ValueError("FAR manifest hit roster mismatch")
    if len(hit_ids) != 3065 or len(miss_ids) != 168:
        raise ValueError("unexpected FAR hit/miss count")

    miss_rows = [hard[i] for i in miss_ids]
    miss_index = {tuple(r): j for j, r in enumerate(miss_rows)}

    data_module = "Raw34FAR168Data"
    data_ns = "BB6.Agent50Raw34FAR168.Data"
    data_source = [
        "import Raw34PairFinal3233Cover",
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 0",
        f"namespace {data_ns}",
        "open BB6Coverage BB6.Agent50Raw34Plan",
        "def missRows : List (List Nat) := [",
        ",\n".join("  " + lean_list(r) for r in miss_rows),
        "]",
        "abbrev Good168 (m : Machine) : Prop :=",
        "  DecidedBelow 128 m ∨ ExplicitResidual missRows m",
        "theorem miss_count : missRows.length = 168 := by decide",
        "#print axioms miss_count",
        f"end {data_ns}",
        "",
    ]
    (out / f"{data_module}.lean").write_text("\n".join(data_source))

    shards = []
    for start in range(0, len(final_rows), args.shard_size):
        xs = final_rows[start:start + args.shard_size]
        shard = len(shards)
        module = f"Raw34FAR168Rows{shard:03d}"
        ns = f"BB6.Agent50Raw34FAR168.{module}"
        needed = sorted({
            id_to_ns[hard_map[tuple(row)]]
            for row in xs
            if hard_map[tuple(row)] in hit_ids
        })
        imports = [f"import {data_module}"]
        imports += [f"import {x.rsplit('.',1)[-1]}" for x in needed]
        body = [
            *imports,
            "set_option maxRecDepth 100000",
            "set_option maxHeartbeats 0",
            f"namespace {ns}",
            f"open BB6Coverage BB6.Agent50Raw34Plan {data_ns}",
            "def rows : List (List Nat) := [",
            ",\n".join("  " + lean_list(r) for r in xs),
            "]",
            "",
        ]
        theorem_names = []
        for k, row in enumerate(xs):
            idx = start + k
            ident = hard_map[tuple(row)]
            thm = f"cover{idx}"
            theorem_names.append(thm)
            body += [f"theorem {thm} : Cover Good168 (table {lean_list(row)}) := by"]
            if ident in hit_ids:
                far_ns = id_to_ns[ident]
                body += [
                    "  apply Cover.leaf",
                    "  intro m hm",
                    f"  exact Or.inl (Or.inl ({far_ns}.never{ident} m hm))",
                ]
            else:
                j = miss_index[tuple(row)]
                body += [
                    "  apply Cover.leaf",
                    "  intro m hm",
                    f"  exact Or.inr ⟨{j}, {lean_list(row)}, by decide, hm⟩",
                ]
            body.append("")
        body += [
            f"theorem row_count : rows.length = {len(xs)} := by decide",
            "theorem cover_mem (row : List Nat) (h : row ∈ rows) :",
            "    Cover Good168 (table row) := by",
            "  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at h",
            "  rcases h with " + " | ".join("rfl" for _ in xs),
        ]
        for thm in theorem_names:
            body.append(f"  · exact {thm}")
        body += [
            "#print axioms cover_mem",
            f"end {ns}",
            "",
        ]
        (out / f"{module}.lean").write_text("\n".join(body))
        shards.append({"module": module, "namespace": ns, "start": start,
                       "end": start + len(xs), "size": len(xs)})

    index_module = "Raw34FAR168Index"
    index_ns = "BB6.Agent50Raw34FAR168.Index"
    all_expr = " ++\n  ".join(x["namespace"] + ".rows" for x in shards)
    dispatch = [
        "theorem cover_mem_all (row : List Nat) (h : row ∈ allRows) :",
        "    Cover Good168 (table row) := by",
        "  simp only [allRows, List.mem_append] at h",
    ]
    depth = 0
    for x in shards[:-1]:
        pad = "  " * (depth + 1)
        dispatch += [
            pad + "rcases h with h | h",
            pad + "· exact " + x["namespace"] + ".cover_mem row h",
            pad + "·",
        ]
        depth += 1
    dispatch.append("  " * (depth + 1) + "exact " + shards[-1]["namespace"] + ".cover_mem row h")
    index_source = [
        *(f"import {x['module']}" for x in shards),
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 0",
        f"namespace {index_ns}",
        f"open BB6Coverage BB6.Agent50Raw34Plan {data_ns}",
        "def allRows : List (List Nat) :=",
        "  " + all_expr,
        f"theorem allRows_eq_old : allRows = {OLD_DATA}.finalRows := by decide +kernel",
        *dispatch,
        f"theorem old_row_cover (j : Nat) (row : List Nat)",
        f"    (hj : {OLD_DATA}.finalRows[j]? = some row) :",
        "    Cover Good168 (table row) := by",
        f"  have hm : row ∈ {OLD_DATA}.finalRows := by",
        "    rcases List.getElem?_eq_some_iff.mp hj with ⟨hidx, hget⟩",
        "    exact List.mem_of_getElem hget",
        "  have hm' : row ∈ allRows := by",
        "    rw [allRows_eq_old]",
        "    exact hm",
        "  exact cover_mem_all row hm'",
        "#print axioms allRows_eq_old",
        "#print axioms old_row_cover",
        f"end {index_ns}",
        "",
    ]
    (out / f"{index_module}.lean").write_text("\n".join(index_source))

    cover_module = "Raw34FAR168Cover"
    cover_ns = "BB6.Agent50Raw34FAR168"
    cover_source = [
        f"import {index_module}",
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 0",
        f"namespace {cover_ns}",
        f"open BB6Coverage BB6.Agent50Raw34Plan {data_ns}",
        f"theorem cover : Cover Good168 {PARENT} := by",
        "  apply Cover.leaf",
        "  intro m hm",
        f"  rcases {OLD_COVER}.sound m hm with hd | hr",
        "  · exact Or.inl hd",
        "  · rcases hr with ⟨j, row, hj, hrow⟩",
        f"    exact ({index_ns}.old_row_cover j row hj).sound m hrow",
        "#print axioms cover",
        f"end {cover_ns}",
        "",
    ]
    (out / f"{cover_module}.lean").write_text("\n".join(cover_source))

    manifest = {
        "status": "source-generated exact FAR shrink; Lean acceptance required",
        "parent": "1RB---_1RC---_0RD0LF_1LC---_------_0LD---",
        "oldResidualRows": len(final_rows),
        "oldCanonicalSha256": sha_rows(sorted(final_rows)),
        "farHits": len(hit_ids),
        "newResidualRows": len(miss_rows),
        "newCanonicalSha256": sha_rows(sorted(miss_rows)),
        "newResidualsComplete": all(all(x > 0 for x in r) for r in miss_rows),
        "newResidualsUnique": len({tuple(r) for r in miss_rows}) == len(miss_rows),
        "shardSize": args.shard_size,
        "shards": shards,
        "theorem": cover_ns + ".cover",
        "interpretation": "Every completion of the exact 244,140,625-table pair parent is DecidedBelow 128 or equals one of 168 explicit complete residual machines.",
    }
    (out / "far168-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps({k: v for k, v in manifest.items() if k != "shards"}, indent=2))


if __name__ == "__main__":
    main()
