"""Conservative quantitative comparison of certified finite-ray leaf predicates.

The root is A/0=1RB, every unassigned branch has all 25 ordinary-or-halt
choices, and the search is bounded to five assigned entries (75 trace steps).
Counts are Python-checked enumeration, not Lean-certified totals. Marker and
fresh-ray leaf soundness are separately Lean-verified in source.
"""
from collections import Counter

from macro_benchmark import (
    ROOT, ACTIONS, finite_trace, first_unassigned,
    initial_macro, entered_macro,
)

DEPTH = 5
ENTRY_LIMIT = 6
MACRO_LIMIT = 6
TRACE_LIMIT = 75


def finite_marked_trace(table, steps, state):
    head = 0
    marked = {0}
    heads = []
    for _ in range(steps):
        heads.append(head)
        slot = (state, int(head in marked))
        if slot not in table or table[slot] is None:
            return None
        write, direction, state = table[slot]
        if write:
            marked.add(head)
        else:
            marked.discard(head)
        head += 1 if direction else -1
    return state, head, marked, heads


def marker_entry(table):
    for k in range(ENTRY_LIMIT):
        entry = finite_trace(table, k)
        if entry is None:
            break
        state, head, marked, _ = entry
        if head not in marked or any(x > head for x in marked):
            continue
        for n in range(1, MACRO_LIMIT+1):
            out = finite_marked_trace(table, n, state)
            if out is None:
                break
            next_state, next_head, next_marks, visited = out
            if (next_state == state and next_head > 0
                    and next_head in next_marks
                    and all(x <= next_head for x in next_marks)
                    and all(x >= 0 for x in visited)):
                return (k, n, state)
    return None


def baseline_subtree_mass(table):
    """Mass the original fresh-ray search would certify below this node."""
    weight = 25 ** (12-len(table))
    if initial_macro(table, MACRO_LIMIT):
        return weight
    if entered_macro(table, ENTRY_LIMIT, MACRO_LIMIT):
        return weight
    kind, slot = first_unassigned(table, TRACE_LIMIT)
    if kind != "hole" or len(table) >= DEPTH:
        return 0
    total = 0
    for a in ACTIONS:
        table[slot] = a
        total += baseline_subtree_mass(table)
    del table[slot]
    return total


def census():
    counts = Counter()
    example = {}
    table = dict(ROOT)

    def dfs():
        counts["visited"] += 1
        weight = 25 ** (12-len(table))
        if initial_macro(table, MACRO_LIMIT):
            counts["fresh_mass"] += weight
            counts["all_mass"] += weight
            counts["fresh_nodes"] += 1
            return
        if entered_macro(table, ENTRY_LIMIT, MACRO_LIMIT):
            counts["fresh_mass"] += weight
            counts["all_mass"] += weight
            counts["fresh_nodes"] += 1
            return
        marker = marker_entry(table)
        if marker is not None:
            previous = baseline_subtree_mass(table)
            counts["marker_nodes"] += 1
            counts["marker_mass"] += weight
            counts["marker_strict_extra"] += weight-previous
            counts["fresh_mass"] += previous
            counts["all_mass"] += weight
            if not example:
                example["transitions"] = sorted(table.items())
                example["witness"] = marker
            return
        kind, slot = first_unassigned(table, TRACE_LIMIT)
        counts[kind+"_nodes"] += 1
        if kind == "hole" and len(table) < DEPTH:
            for a in ACTIONS:
                table[slot] = a
                dfs()
            del table[slot]

    dfs()
    counts["fresh_mass"] += 0
    assert counts["all_mass"] == counts["fresh_mass"] + counts["marker_strict_extra"]
    assert counts["marker_strict_extra"] > 0
    baseline = 1_133_001_708_984_375
    assert counts["fresh_mass"] == baseline, counts
    assert counts["all_mass"] <= 25**11
    return counts, example


def main():
    counts, sample = census()
    for k in sorted(counts):
        print(k, counts[k])
    print("additional marker fraction global raw tables:",
          100*counts["marker_strict_extra"] / 25**12)
    print("extra marker fraction rooted A/0=1RB:",
          100*counts["marker_strict_extra"] / 25**11)
    print("sample marker transitions", sample["transitions"])
    print("sample marker witness (entry, macro, state)", sample["witness"])


if __name__ == "__main__":
    main()
