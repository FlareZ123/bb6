#!/usr/bin/env python3
"""Exact scan of SideWitnessCore cylinders against selected first-one parents.

Run from the repository root:
    python im-results/agent2-sidewitness-multiparent/scan.py

The SideWitnessCore row code is 0 = wildcard and 1..24 = an ordinary move.
Completed transition domains have 25 values: 0 = halt and 1..24 = ordinary
moves. The distinction is intentional.
"""
from __future__ import annotations

import json
import re
from functools import lru_cache
from pathlib import Path

SOURCE = Path("im-results/agent47-rooted-tnf/SideWitnessCore.lean")
MANIFEST = Path("im-results/agent13-roster-convergence/canonical-124.json")
BDD_FILE = Path("im-results/agent2-sidewitness-multiparent/bdds.json")
ROW_RE = re.compile(
    r"⟨\[([0-9,\s]+)\],\s*(\d+),\s*(\d+),\s*(true|false),\s*\((-?\d+)\)⟩"
)
PARENTS = (8, 9, 10, 23)
EXPECTED_MATCHES = {8: 68, 9: 108, 10: 65, 23: 96}
EXPECTED_UNIONS = {
    8: 15_943_636_947_500,
    9: 31_473_123_262_500,
    10: 4_477_340_035_625,
    23: 771_676_095_000,
}
EXPECTED_REMAINDER_BOXES = {8: 208, 9: 108, 10: 34, 23: 12_584}
EXPECTED_LARGEST_REMAINDERS = {
    8: {
        "mass": 76_293_945_312_500,
        "domains": {
            "C1": [0, 3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 23, 24],
        },
    },
    9: {
        "mass": 44_097_900_390_625,
        "domains": {
            "B1": [0, 1, 3, 7, 9, 11, 12, 14, 15, 16, 18, 19, 20, 21, 22, 23, 24],
            "C0": [0, 3, 7, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24],
        },
    },
    10: {
        "mass": 84_228_515_625_000,
        "domains": {
            "A1": [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24],
            "C1": [0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24],
        },
    },
    23: {
        "mass": 2_899_169_921_875,
        "domains": {
            "D1": [0, 1, 3, 5, 7, 9, 10, 11, 13, 14, 15, 16, 17, 18, 20, 21, 22, 23, 24],
        },
    },
}
HELD_QI2800 = (8, 14, 11, 7, 17, 4, 9, 2, 23, 15, 16, 0)
FULL_BRANCHES = {
    8: ((5, 1), (5, 2), (5, 4), (5, 8)),
    9: ((4, 1), (4, 2), (4, 4), (4, 5), (4, 6), (4, 8), (4, 10), (4, 12)),
    10: ((5, 1),),
    23: ((7, 2), (7, 4), (7, 6), (7, 8), (7, 12)),
}
SLOT_NAMES = ("A0", "A1", "B0", "B1", "C0", "C1",
              "D0", "D1", "E0", "E1", "F0", "F1")
STATES = "ABCDEF"


def code_to_move(code: int) -> str | None:
    if code == 0:
        return None
    k = code - 1
    return f"{(k // 2) % 2}{'L' if k % 2 == 0 else 'R'}{STATES[k // 4]}"


def move_to_code(move: str) -> int:
    write = int(move[0])
    direction = 0 if move[1] == "L" else 1
    state = STATES.index(move[2])
    return 1 + 4 * state + 2 * write + direction


def parse_rows(source: str) -> list[tuple[int, ...]]:
    rows = []
    for match in ROW_RE.finditer(source):
        row = tuple(int(x.strip()) for x in match.group(1).split(","))
        if len(row) == 12:
            rows.append(row)
    return rows


def simplify(cubes: tuple[tuple[int, ...], ...]) -> tuple[tuple[int, ...], ...]:
    unique = tuple(dict.fromkeys(cubes))
    return tuple(
        cube for i, cube in enumerate(unique)
        if not any(
            i != j and all(a == 0 or a == b for a, b in zip(other, cube))
            for j, other in enumerate(unique)
        )
    )


def count_union(cubes: list[tuple[int, ...]]) -> int:
    """Count a union of wildcard cubes over 25 values per free slot."""
    @lru_cache(maxsize=None)
    def visit(current: tuple[tuple[int, ...], ...],
              variables: tuple[int, ...]) -> int:
        current = tuple(sorted(simplify(current)))
        if any(all(value == 0 for value in cube) for cube in current):
            return 25 ** len(variables)
        if not current or not variables:
            return 0

        def score(variable: int) -> tuple[int, int]:
            fixed = [cube[variable] for cube in current if cube[variable] != 0]
            return len(set(fixed)), len(fixed)

        variable = max(variables, key=score)
        rest = tuple(v for v in variables if v != variable)
        if all(cube[variable] == 0 for cube in current):
            return 25 * visit(current, rest)

        total = 0
        for value in range(25):
            next_cubes = tuple(
                tuple(0 if i == variable else x for i, x in enumerate(cube))
                for cube in current
                if cube[variable] == 0 or cube[variable] == value
            )
            total += visit(next_cubes, rest)
        return total

    nvars = len(cubes[0]) if cubes else 0
    return visit(tuple(cubes), tuple(range(nvars)))


def build_bdd(cubes: list[tuple[int, ...]],
              free_slots: list[int]) -> dict:
    """Build a reduced 25-way decision DAG; 0=open, 1=covered."""
    memo = {}
    unique_nodes = {}
    nodes = []
    next_id = 2

    def visit(input_cubes: tuple[tuple[int, ...], ...],
              variables: tuple[int, ...]) -> int:
        nonlocal next_id
        current = tuple(sorted(
            simplify(input_cubes),
            key=lambda cube: ",".join(map(str, cube))
        ))
        if any(all(value == 0 for value in cube) for cube in current):
            return 1
        if not current or not variables:
            return 0

        key = (variables, current)
        if key in memo:
            return memo[key]

        def score(variable: int) -> tuple[int, int]:
            fixed = [cube[variable] for cube in current if cube[variable] != 0]
            return len(set(fixed)), len(fixed)

        variable = max(variables, key=lambda v: (score(v)[0], score(v)[1], -v))
        rest = tuple(v for v in variables if v != variable)
        children = []
        for value in range(25):
            next_cubes = tuple(
                tuple(0 if i == variable else x for i, x in enumerate(cube))
                for cube in current
                if cube[variable] == 0 or cube[variable] == value
            )
            children.append(visit(next_cubes, rest))

        if all(child == children[0] for child in children):
            memo[key] = children[0]
            return children[0]

        signature = (variable, tuple(children))
        node_id = unique_nodes.get(signature)
        if node_id is None:
            node_id = next_id
            next_id += 1
            unique_nodes[signature] = node_id
            nodes.append({
                "id": node_id,
                "slot": free_slots[variable],
                "children": children,
            })
        memo[key] = node_id
        return node_id

    root = visit(tuple(cubes), tuple(range(len(free_slots))))
    return {
        "root": root,
        "states": len(memo),
        "node_count": len(nodes),
        "free_slots": free_slots,
        "nodes": nodes,
    }


def box_mass(box: tuple[frozenset[int], ...]) -> int:
    result = 1
    for domain in box:
        result *= len(domain)
    return result


def subtract_box(box: tuple[frozenset[int], ...],
                 cube: tuple[tuple[int, int], ...]
                 ) -> list[tuple[frozenset[int], ...]]:
    """Return the disjoint first-mismatch rectangles for box minus cube."""
    if any(value not in box[slot] for slot, value in cube):
        return [box]

    prefix = list(box)
    out = []
    for slot, value in cube:
        rejected = list(prefix)
        rejected[slot] = frozenset(v for v in rejected[slot] if v != value)
        if all(rejected):
            out.append(tuple(rejected))
        prefix[slot] = frozenset((value,))
    return out


def largest_remainder_box(
    boxes: list[tuple[frozenset[int], ...]],
    free_slots: list[int],
) -> dict:
    largest = max(boxes, key=box_mass)
    return {
        "mass": box_mass(largest),
        "domains": {
            SLOT_NAMES[slot]: sorted(largest[slot])
            for slot in free_slots
            if len(largest[slot]) < 25
        },
    }


def parent_box(table: list[str | None]) -> tuple[frozenset[int], ...]:
    return tuple(
        frozenset(range(25)) if move is None else frozenset((move_to_code(move),))
        for move in table
    )


def main() -> None:
    source = SOURCE.read_text(encoding="utf-8")
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    rows = parse_rows(source)
    assert len(rows) == 388, len(rows)

    # Exhaust the complete 124-entry manifest before focusing on the four hits.
    all_matches = {}
    for entry in manifest["entries"]:
        raw = entry["raw_residual_index"]
        table = entry["table"]
        selected = [
            row for row in rows
            if all(move is None or code_to_move(row[i]) == move
                   for i, move in enumerate(table))
        ]
        if selected:
            all_matches[raw] = selected
    matched_parents = tuple(sorted(all_matches))
    assert matched_parents == PARENTS, matched_parents

    bdd_manifest = json.loads(BDD_FILE.read_text(encoding="utf-8"))
    assert bdd_manifest["schema"] == "bb6-mdd-v1"

    reports = {}
    aggregate_closed = 0
    aggregate_parent = 0

    for raw in PARENTS:
        entry = next(e for e in manifest["entries"]
                     if e["raw_residual_index"] == raw)
        table = entry["table"]
        selected = all_matches[raw]
        assert len(selected) == EXPECTED_MATCHES[raw], (raw, len(selected))

        free_slots = [i for i, move in enumerate(table) if move is None]
        cubes = [tuple(row[i] for i in free_slots) for row in selected]
        union = count_union(cubes)
        parent_mass = 25 ** len(free_slots)
        assert union == EXPECTED_UNIONS[raw], (raw, union)

        bdd_cubes = list(cubes)
        if raw == 10:
            bdd_cubes.append(tuple(HELD_QI2800[i] for i in free_slots))
        bdd = build_bdd(bdd_cubes, free_slots)
        expected_bdd = bdd_manifest["parents"][str(raw)]
        for field in ("root", "states", "node_count", "free_slots", "nodes"):
            assert bdd[field] == expected_bdd[field], (raw, field)
        expected_covered = union + (25 if raw == 10 else 0)
        assert expected_bdd["covered_completions"] == expected_covered

        full = []
        for row in selected:
            extra = tuple((i, row[i]) for i, move in enumerate(table)
                          if move is None and row[i] != 0)
            if len(extra) == 1:
                full.append(extra[0])
        full = tuple(sorted(set(full)))
        assert full == FULL_BRANCHES[raw], (raw, full)

        cert_rows = list(selected)
        if raw == 10:
            cert_rows.append(HELD_QI2800)

        cubes_for_subtraction = [
            tuple((i, value) for i, value in enumerate(row) if value != 0)
            for row in cert_rows
        ]
        boxes = [parent_box(table)]
        for cube in cubes_for_subtraction:
            boxes = [piece for box in boxes
                     for piece in subtract_box(box, cube)]

        residual_mass = sum(box_mass(box) for box in boxes)
        closed_mass = parent_mass - residual_mass
        largest = largest_remainder_box(boxes, free_slots)
        assert largest == EXPECTED_LARGEST_REMAINDERS[raw], (raw, largest)
        assert len(boxes) == EXPECTED_REMAINDER_BOXES[raw], (
            raw, len(boxes), EXPECTED_REMAINDER_BOXES[raw]
        )
        assert closed_mass == (
            union + (25 if raw == 10 else 0)
        ), (raw, closed_mass, union)

        aggregate_closed += closed_mass
        aggregate_parent += parent_mass
        reports[raw] = {
            "canonical_index": entry["canonical_index"],
            "address": entry["address"],
            "holes": entry["holes"],
            "side_witnesses": len(selected),
            "side_witness_union": union,
            "parent_completions": parent_mass,
            "side_witness_percent": round(100 * union / parent_mass, 9),
            "reduced_bdd_root": bdd["root"],
            "reduced_bdd_states": bdd["states"],
            "reduced_bdd_nodes": bdd["node_count"],
            "whole_child_branches": [
                {"slot": SLOT_NAMES[slot], "move": code_to_move(code)}
                for slot, code in full
            ],
            "subtraction_certificates": len(cert_rows),
            "disjoint_remainder_boxes": len(boxes),
            "remainder_completions": residual_mass,
            "largest_first_mismatch_box": largest,
            "closed_completions_including_held_leaf": closed_mass,
        }

    print(json.dumps({
        "side_witnesses_parsed": len(rows),
        "parents_with_any_refinement_in_full_124_manifest": list(matched_parents),
        "parents": reports,
        "aggregate_disjoint_parent_mass": aggregate_parent,
        "aggregate_closed_mass": aggregate_closed,
        "aggregate_closed_percent": round(
            100 * aggregate_closed / aggregate_parent, 9
        ),
        "notes": [
            "Each side-witness row is separately kernel-checked by SideWitnessCore.witnesses_checked.",
            "The union and rectangle counts are exact integer computations, not Lean kernel theorems.",
            "Raw10 includes the q_i(2800,100) held leaf in its subtraction count; raw8/raw9/raw23 do not.",
            "The residual boxes are obligations, not proofs that their completions are safe.",
            "Largest first-mismatch boxes depend on source witness order; total complement and mass do not.",
        ],
    }, indent=2))


if __name__ == "__main__":
    main()
