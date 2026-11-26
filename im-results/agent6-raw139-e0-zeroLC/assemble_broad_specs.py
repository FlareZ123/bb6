"""Assemble broad E0=0LC D0-sibling search recipes into the chunk-emitter spec.

The C++ census enumerates the open leaves; broad_search.py attaches independently
reproducible cycle/FAR/block/late recipes.  This script checks the two leaf sets
exactly, reconstructs the Python audit trees, and expands the two multi-hole
late cases into explicit 24-way split recipes.
"""
from __future__ import annotations

from collections import Counter
from pathlib import Path
import json
import sys

ROOT = Path(__file__).resolve().parent
for path in (
    ROOT.parent / "agent48-raw139-f1-oneLA",
    ROOT.parent / "agent48-raw139-f1-oneRA",
):
    sys.path.insert(0, str(path))
sys.path.insert(0, str(ROOT))

from scan import ORDER, tree
from emit_family import code_name

BROAD_CODES = [0, 1, 2, 3, 5, 6, 7, 11, 20, 21, 22, 23]
BASE_PARENT = [7, 24, 11, 24, 14, 24, 24, 16, 8, 11, 24, 24]


def table_name(code: int) -> str:
    return f"{(code >> 1) & 1}{'R' if code & 1 else 'L'}{chr(65 + code // 4)}"


def max_late(recipe) -> int:
    if recipe[0] == "late":
        return int(recipe[1])
    if recipe[0] == "split":
        return max([int(recipe[1])] + [max_late(child) for child in recipe[3]])
    return 0


def build_specs(workdir: str | Path):
    work = Path(workdir)
    recipe_by_table = {}
    for line in (work / "broad_recipes.jsonl").read_text().splitlines():
        name, index, table, recipe = json.loads(line)
        key = (name, tuple(table))
        if key in recipe_by_table:
            raise ValueError(f"duplicate broad recipe for {key}")
        recipe_by_table[key] = (int(index), recipe)

    late_by_key = {}
    late_path = work / "late_branch_recipes.jsonl"
    for line in late_path.read_text().splitlines():
        key, code, table, recipe = json.loads(line)
        pair = (key, int(code))
        if pair in late_by_key:
            raise ValueError(f"duplicate late recipe for {pair}")
        late_by_key[pair] = (tuple(table), recipe)

    if len(ORDER) != 24:
        raise AssertionError(f"unexpected move order length: {len(ORDER)}")
    if len(recipe_by_table) != 13323:
        raise AssertionError(f"expected 13323 broad recipes, got {len(recipe_by_table)}")
    if len(late_by_key) != 48:
        raise AssertionError(f"expected 48 late-child recipes, got {len(late_by_key)}")

    specs = {}
    trees = {}
    summary = []
    total_open = 0
    total_multi_late = 0

    for code in BROAD_CODES:
        name = table_name(code)
        parent = BASE_PARENT.copy()
        parent[6] = code

        counts = Counter()
        opens = []
        audit_tree = tree(parent, counts, opens, 250, 2)

        census_path = work / f"raw139_e0_0LC_{name}_leaves.txt"
        census_tables = []
        for line in census_path.read_text().splitlines():
            fields = line.split()
            if len(fields) != 4:
                raise ValueError(f"malformed census row in {census_path}: {line}")
            census_tables.append(tuple(map(int, fields[3].split(","))))

        python_tables = [tuple(table) for table in opens]
        if len(census_tables) != len(python_tables) or set(census_tables) != set(python_tables):
            raise AssertionError(
                f"{name}: C++/Python open-leaf mismatch "
                f"(C++={len(census_tables)}, Python={len(python_tables)}, "
                f"missing={len(set(census_tables)-set(python_tables))}, "
                f"extra={len(set(python_tables)-set(census_tables))})"
            )

        recipes = {}
        multi_late = 0
        for leaf_index, table in enumerate(opens):
            key = (name, tuple(table))
            if key not in recipe_by_table:
                raise KeyError(f"{name}: no witness recipe for open leaf {table}")
            census_index, recipe = recipe_by_table[key]

            if recipe[0] == "late" and table.count(24) > 1:
                multi_late += 1
                late_key = f"{name}_{census_index}"
                children = []
                for move_code in ORDER:
                    late_key_pair = (late_key, int(move_code))
                    if late_key_pair not in late_by_key:
                        raise KeyError(f"missing late expansion {late_key_pair}")
                    child_table, child_recipe = late_by_key[late_key_pair]
                    expected = table.copy()
                    expected[recipe[2]] = int(move_code)
                    if tuple(expected) != child_table:
                        raise AssertionError(
                            f"{late_key_pair}: child table does not match split"
                        )
                    children.append(child_recipe)
                recipe = ["split", int(recipe[1]), int(recipe[2]), children]

            if recipe[0] == "late" and table.count(24) != 1:
                raise AssertionError(f"{name}: unresolved multi-hole late leaf {table}")
            if recipe[0] == "open":
                raise AssertionError(f"{name}: unresolved open leaf {table}")

            recipes[str(leaf_index)] = recipe

        total_open += len(opens)
        total_multi_late += multi_late
        branch_namespace = "BB6.Agent6E0ZeroLC.D0" + code_name(code)
        branch_prefix = "A6E0LCD0" + code_name(code)
        spec = {
            "parent": parent,
            "counts": dict(counts),
            "open": opens,
            "recipes": recipes,
            "namespace": branch_namespace,
            "prefix": branch_prefix,
            "manifest_name": f"chunk_manifest_d0_{name}.json",
        }
        specs[str(code)] = spec
        trees[code] = audit_tree
        summary.append({
            "code": code,
            "name": name,
            "open_leaves": len(opens),
            "counts": dict(counts),
            "multi_hole_late_expansions": multi_late,
            "max_late_step": max((max_late(r) for r in recipes.values()), default=0),
            "weighted_bound": max(
                counts["maxquery"],
                max((max_late(r) for r in recipes.values()), default=0),
            ) + 6,
        })

    if total_open != 13323:
        raise AssertionError(f"expected 13323 open leaves, got {total_open}")
    if total_multi_late != 2:
        raise AssertionError(f"expected exactly two multi-hole late expansions, got {total_multi_late}")

    (work / "broad_specs.json").write_text(json.dumps(specs, separators=(",", ":")))
    (work / "broad_specs_summary.json").write_text(json.dumps({
        "total_open_leaves": total_open,
        "total_multi_hole_late_expansions": total_multi_late,
        "branches": summary,
    }, indent=2))
    return specs, trees, summary


if __name__ == "__main__":
    workdir = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(".")
    _, _, summary = build_specs(workdir)
    for row in summary:
        print(
            row["name"],
            "open=", row["open_leaves"],
            "bound=", row["weighted_bound"],
            "multi-late=", row["multi_hole_late_expansions"],
            flush=True,
        )
