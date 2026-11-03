"""Deterministic bilateral marker/word sparse-prefix benchmark.

Counts measure certificates accepted by a bounded DFS of 25-way transitions,
not an exhaustive Busy Beaver classification. Lean source-level oracle soundness
must be established separately; this Python run independently tests its
finite-support witness predicates. The search root is A/0=1RB.
"""
from collections import Counter

from macro_benchmark import (
    ROOT, ACTIONS, finite_trace, first_unassigned,
    initial_macro, entered_macro,
)
from marker_benchmark import marker_entry as marker_right

ENTRY_LIMIT = 6
MACRO_LIMIT = 6
TRACE_LIMIT = 75
MAX_ASSIGNED = 5


def marker_left(table):
    for k in range(ENTRY_LIMIT):
        entry = finite_trace(table, k)
        if entry is None:
            break
        state, head, marked, _ = entry
        if head not in marked or any(x < head for x in marked):
            continue
        for n in range(1, MACRO_LIMIT + 1):
            trial = finite_trace_with_marks(table, n, state, {0})
            if trial is None:
                break
            next_state, next_head, marks, heads = trial
            if (next_state == state and next_head < 0 and
                    next_head in marks and
                    all(x >= next_head for x in marks) and
                    all(x <= 0 for x in heads)):
                return k, n, state
    return None


def finite_trace_with_marks(table, steps, state, initial_marks):
    head = 0
    marked = set(initial_marks)
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


def word_entry(table, right):
    for k in range(ENTRY_LIMIT):
        entry = finite_trace(table, k)
        if entry is None:
            break
        state, head, marked, _ = entry
        word = {x - head for x in marked if x >= head} if right else {
            x - head for x in marked if x <= head
        }
        for n in range(1, MACRO_LIMIT + 1):
            trial = finite_trace_with_marks(table, n, state, word)
            if trial is None:
                break
            next_state, next_head, marks, heads = trial
            if next_state != state:
                continue
            if right:
                good = (next_head > 0 and
                    {x-next_head for x in marks if x >= next_head} == word and
                    all(x >= 0 for x in heads))
            else:
                good = (next_head < 0 and
                    {x-next_head for x in marks if x <= next_head} == word and
                    all(x <= 0 for x in heads))
            if good:
                return k, n, state, tuple(sorted(word))
    return None


def census(include_words=True):
    counts = Counter()
    examples = {}
    table = dict(ROOT)

    def visit():
        counts["visited"] += 1
        weight = 25 ** (12-len(table))
        if initial_macro(table) or entered_macro(table, ENTRY_LIMIT, MACRO_LIMIT):
            counts["fresh_nodes"] += 1
            counts["certified_tables"] += weight
            return
        if marker_right(table) is not None or marker_left(table) is not None:
            counts["marker_nodes"] += 1
            counts["certified_tables"] += weight
            return
        if include_words:
            for right in (True, False):
                witness = word_entry(table, right)
                if witness is not None:
                    counts["word_nodes"] += 1
                    counts["certified_tables"] += weight
                    examples.setdefault("right" if right else "left",
                                        (tuple(sorted(table.items())), witness))
                    return
        kind, item = first_unassigned(table, TRACE_LIMIT)
        counts[kind+"_nodes"] += 1
        if kind == "hole" and len(table) < MAX_ASSIGNED:
            for action in ACTIONS:
                table[item] = action
                visit()
            del table[item]

    visit()
    return counts, examples


if __name__ == "__main__":
    old, _ = census(False)
    now, examples = census(True)
    assert old["certified_tables"] == 1244360351562500, old
    assert now["certified_tables"] >= old["certified_tables"], (old, now)
    print("old bilateral-marker mass", old["certified_tables"])
    print("new bilateral-word mass", now["certified_tables"])
    print("strict additional certified tables", now["certified_tables"] - old["certified_tables"])
    print("new certified fraction of rooted A/0=1RB cylinder",
          now["certified_tables"] / (25**11))
    print("old counts", sorted(old.items()))
    print("new counts", sorted(now.items()))
    print("word-only example", examples)
