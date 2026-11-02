"""Deterministic sparse-prefix census for translated fresh-ray macro leaves.

Computational evidence only. Soundness of each accepted Boolean *when checked
in Lean* is given by EntryMacroLeft.lean and MacroOracle.lean. This Python
enumerator and its aggregate counts have not been imported into Lean.
"""
from collections import Counter
from itertools import product

ACTIONS = (None,) + tuple((w, d, q)
                         for q, w, d in product(range(6), range(2), range(2)))
ROOT = {(0, 0): (1, 1, 1)}
assert len(ACTIONS) == 25


def finite_trace(table, steps, state=0):
    """Returns (state, head, marked_positions, consulted_heads) or None."""
    head = 0
    marked = set()
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


def macro(table, steps, state, right):
    trace = finite_trace(table, steps, state)
    if trace is None:
        return False
    final_state, head, marked, heads = trace
    if final_state != state:
        return False
    if right:
        return (head > 0 and all(x < head for x in marked)
                and all(x >= 0 for x in heads))
    return (head < 0 and all(x > head for x in marked)
            and all(x <= 0 for x in heads))


def initial_macro(table, macro_limit):
    return any(macro(table, n, 0, direction)
               for n in range(1, macro_limit+1)
               for direction in (False, True))


def entered_macro(table, entry_limit, macro_limit):
    for entry_steps in range(entry_limit):
        prefix = finite_trace(table, entry_steps)
        if prefix is None:
            break
        state, head, marked, _ = prefix
        for right in (False, True):
            pristine = (all(x < head for x in marked) if right
                        else all(x > head for x in marked))
            if pristine:
                for n in range(1, macro_limit+1):
                    if macro(table, n, state, right):
                        return entry_steps, n, state, right
    return None


def first_unassigned(table, time_limit):
    state = head = 0
    marked = set()
    for step in range(time_limit):
        slot = (state, int(head in marked))
        if slot not in table:
            return "hole", slot
        action = table[slot]
        if action is None:
            return "halt", step+1
        write, direction, state = action
        if write:
            marked.add(head)
        else:
            marked.discard(head)
        head += 1 if direction else -1
    return "timeout", time_limit


def census(max_assigned=5, entry_limit=6, macro_limit=6, time_limit=75):
    """First-unknown-slot tree under the exact fixed root A/0=1RB."""
    counts = Counter()
    example = {}
    table = dict(ROOT)

    def visit():
        counts["visited"] += 1
        weight = 25 ** (12-len(table))
        if initial_macro(table, macro_limit):
            counts["old_nodes"] += 1
            counts["old_tables"] += weight
            counts["combined_tables"] += weight
            return
        found = entered_macro(table, entry_limit, macro_limit)
        if found is not None:
            counts["new_nodes"] += 1
            counts["combined_tables"] += weight
            if not example:
                example["table"] = dict(table)
                example["witness"] = found
            return
        kind, value = first_unassigned(table, time_limit)
        counts[kind+"_nodes"] += 1
        if kind == "hole" and len(table) < max_assigned:
            for action in ACTIONS:
                table[value] = action
                visit()
            del table[value]

    visit()
    counts["additional_tables"] = counts["combined_tables"]-counts["old_tables"]
    return counts, example


def main():
    counts4, _ = census(4)
    assert counts4["visited"] == 10076
    assert counts4["old_tables"] == 395202636718750
    assert counts4["combined_tables"] == 939178466796875
    counts, example = census(5)
    assert counts["visited"] == 179376, counts
    assert counts["old_tables"] == 438171386718750, counts
    assert counts["combined_tables"] == 1133001708984375, counts
    assert counts["new_nodes"] == 26073, counts
    assert counts["old_nodes"] == 7566, counts
    global_tables = 25**12
    root_tables = 25**11
    assert 0 <= counts["old_tables"] <= counts["combined_tables"] <= root_tables
    for key in sorted(counts):
        print(f"{key}: {counts[key]}")
    print("global percentage under A/0=1RB: ",
          100*counts["combined_tables"]/global_tables)
    print("strict extra percentage of all canonical tables: ",
          100*counts["additional_tables"]/global_tables)
    print("strict extra percentage of the A/0=1RB cylinder: ",
          100*counts["additional_tables"]/root_tables)
    print("sample extra sparse table:", sorted(example["table"].items()))
    print("sample finite-entry witness:", example["witness"])


if __name__ == "__main__":
    main()
