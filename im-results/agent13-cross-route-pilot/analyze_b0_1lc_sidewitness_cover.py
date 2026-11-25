#!/usr/bin/env python3
"""Exact finite cover count for SideWitnessCore cylinders below raw residual 10.

Run from the repository root:
    python im-results/agent13-cross-route-pilot/analyze_b0_1lc_sidewitness_cover.py

SideWitnessCore stores each transition as 0 for wildcard or 1..24 for an
ordinary move. The parent fixes A0=1RB (code 8) and B0=1LC (code 11), leaving
ten slots with 25 possible completions each (halt plus 24 ordinary moves).
This script counts the union of the 65 SideWitness cylinders exactly by a
memoized Shannon/decision-diagram recursion; it does not enumerate 25**10
machines individually.
"""

from __future__ import annotations

import re
from functools import lru_cache
from pathlib import Path

SOURCE = Path("im-results/agent47-rooted-tnf/SideWitnessCore.lean")
ROW_RE = re.compile(
    r"⟨\[([0-9,\s]+)\],\s*(\d+),\s*(\d+),\s*(true|false),\s*\((-?\d+)\)⟩"
)
PARENT_A0 = 8   # 1RB
PARENT_B0 = 11  # 1LC
FREE_SLOTS = (1, 3, 4, 5, 6, 7, 8, 9, 10, 11)
DOMAIN = tuple(range(25))  # 0 = halt; 1..24 = ordinary transitions
HELD_QI2800 = (8, 14, 11, 7, 17, 4, 9, 2, 23, 15, 16, 0)


def parse_rows(source: str) -> list[tuple[int, ...]]:
    rows = []
    for match in ROW_RE.finditer(source):
        row = tuple(int(x.strip()) for x in match.group(1).split(","))
        if len(row) == 12:
            rows.append(row)
    return rows


def cube_covers(general: tuple[int, ...], specific: tuple[int, ...]) -> bool:
    return all(a == 0 or a == b for a, b in zip(general, specific))


def compatible(a: tuple[int, ...], b: tuple[int, ...]) -> bool:
    return all(x == 0 or y == 0 or x == y for x, y in zip(a, b))


def simplify(cubes: tuple[tuple[int, ...], ...]) -> tuple[tuple[int, ...], ...]:
    unique = tuple(dict.fromkeys(cubes))
    return tuple(
        cube
        for i, cube in enumerate(unique)
        if not any(i != j and cube_covers(other, cube)
                   for j, other in enumerate(unique))
    )


def count_covered(cubes: list[tuple[int, ...]]) -> int:
    """Count the union over the ten free slots, each with 25 values."""
    @lru_cache(maxsize=None)
    def visit(
        current: tuple[tuple[int, ...], ...],
        variables: tuple[int, ...],
    ) -> int:
        current = simplify(current)
        if any(all(value == 0 for value in cube) for cube in current):
            return 25 ** len(variables)
        if not current:
            return 0
        if not variables:
            return 0

        # Branch on the most discriminating remaining variable.
        def score(variable: int) -> tuple[int, int]:
            fixed = [cube[variable] for cube in current if cube[variable] != 0]
            return (len(set(fixed)), len(fixed))

        variable = max(variables, key=score)
        rest = tuple(v for v in variables if v != variable)
        if all(cube[variable] == 0 for cube in current):
            return 25 * visit(current, rest)

        total = 0
        for value in DOMAIN:
            next_cubes = tuple(
                cube[:variable] + (0,) + cube[variable + 1:]
                for cube in current
                if cube[variable] == 0 or cube[variable] == value
            )
            total += visit(next_cubes, rest)
        return total

    initial = tuple(tuple(cube) for cube in cubes)
    nvars = len(initial[0]) if initial else len(FREE_SLOTS)
    return visit(initial, tuple(range(nvars)))


def main() -> None:
    rows = parse_rows(SOURCE.read_text(encoding="utf-8"))
    selected = [row for row in rows
                if row[0] == PARENT_A0 and row[2] == PARENT_B0]
    cubes = [tuple(row[slot] for slot in FREE_SLOTS) for row in selected]
    held = tuple(HELD_QI2800[slot] for slot in FREE_SLOTS)

    parent_space = 25 ** len(FREE_SLOTS)
    side_union = count_covered(cubes)
    combined_union = count_covered(cubes + [held])
    c1_variable = FREE_SLOTS.index(5)
    c1_0la = [cube[:c1_variable] + cube[c1_variable + 1:]
              for row, cube in zip(selected, cubes) if row[5] == 1]
    c1_0ld = [cube[:c1_variable] + cube[c1_variable + 1:]
              for row, cube in zip(selected, cubes) if row[5] == 13]
    c1_0la_union = count_covered(c1_0la)
    c1_0ld_union = count_covered(c1_0ld)
    holes = {}
    for row in selected:
        n = row.count(0)
        holes[n] = holes.get(n, 0) + 1

    compatible_count = sum(
        compatible(row, HELD_QI2800) for row in selected
    )
    added = combined_union - side_union

    assert len(rows) == 388
    assert len(selected) == 65
    assert dict(sorted(holes.items())) == {
        2: 7, 3: 12, 4: 15, 5: 4, 6: 14, 7: 8, 8: 4, 9: 1
    }
    assert compatible_count == 0
    assert len(c1_0la) == 1
    assert len(c1_0ld) == 64
    assert c1_0la_union == 3814697265625
    assert c1_0ld_union == 662642770000
    assert parent_space == 95367431640625
    assert side_union == c1_0la_union + c1_0ld_union == 4477340035625
    assert added == 25
    assert combined_union == 4477340035650

    print(f"parsed_side_witnesses={len(rows)}")
    print(f"b0_1lc_side_witnesses={len(selected)}")
    print(f"holes_distribution={dict(sorted(holes.items()))}")
    print(f"parent_completions={parent_space}")
    print(f"side_witness_union={side_union}")
    print(f"side_witness_union_percent={100 * side_union / parent_space:.9f}")
    print(f"c1_0la_witnesses={len(c1_0la)}")
    print(f"c1_0la_union={c1_0la_union}")
    print(f"c1_0ld_witnesses={len(c1_0ld)}")
    print(f"c1_0ld_union={c1_0ld_union}")
    print(f"c1_0ld_percent_of_branch={100 * c1_0ld_union / (25 ** 9):.9f}")
    print(f"q_i_2800_compatible_side_witnesses={compatible_count}")
    print(f"side_witness_plus_q_i_2800_union={combined_union}")
    print(f"additional_completions_from_q_i_2800={added}")
    print(f"uncovered_completions={parent_space - combined_union}")
    print(f"combined_union_percent={100 * combined_union / parent_space:.9f}")


if __name__ == "__main__":
    main()
