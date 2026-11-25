#!/usr/bin/env python3
"""Compress an accepted two-sided DFA witness by relational partition refinement.

Input/output JSON: table, L/R (two transition targets per state).
The discovered-edge closure is recomputed before and after each quotient.
This is certificate construction, not a replacement for the source checker.
"""
import argparse
import json
from collections import defaultdict, deque
from pathlib import Path


def closure(table, left, right):
    """Least primitive configuration/edge saturation, with implicit blank."""
    dfa = [left, right]
    t = table.replace("_", "")
    moves = [t[i:i+3] for i in range(0, 36, 3)]
    edges = [defaultdict(set), defaultdict(set)]
    waiting = [defaultdict(list), defaultdict(list)]
    seen = {(0, 0, 0, 0)}
    todo = deque(seen)
    if left[0][0] != 0 or right[0][0] != 0:
        raise ValueError("blank zero transition must self-loop")
    for e in edges:
        e[0].add((0, 0))

    def add(c):
        if c not in seen:
            seen.add(c)
            todo.append(c)

    def pop(c, bit, src):
        q, a, l, r = c
        w, direction, n = moves[2*q+a]
        w, n = int(w), ord(n)-65
        if direction == "R":
            add((n, bit, left[l][w], src))
        else:
            add((n, bit, src, right[r][w]))

    while todo:
        c = todo.popleft()
        q, a, l, r = c
        move = moves[2*q+a]
        if move == "---":
            raise ValueError("reachable undefined transition")
        w, direction, n = move
        w = int(w)
        side = int(direction == "R")
        old = l if side else r
        dst = dfa[1-side][old][w]
        e = (w, old)
        if e not in edges[1-side][dst]:
            edges[1-side][dst].add(e)
            for st in waiting[1-side][dst]:
                pop(st, *e)
        x = r if side else l
        waiting[side][x].append(c)
        for b, y in edges[side][x]:
            pop(c, b, y)
    return seen, edges


def classes(keys):
    ids = {}
    return [ids.setdefault(k, len(ids)) for k in keys]


def refine(dfa, labels):
    """Coarsest transition congruence refining the supplied row labels."""
    cls = classes(labels)
    while True:
        new = classes((cls[i], cls[row[0]], cls[row[1]])
                      for i, row in enumerate(dfa))
        if new == cls:
            break
        cls = new
    out = [None] * (max(cls)+1)
    for i, row in enumerate(dfa):
        out[cls[i]] = [cls[row[0]], cls[row[1]]]
    assert cls[0] == 0
    return out, cls


def quotient(table, left, right):
    relation, edges = closure(table, left, right)
    # Unused push entries never occur in the certificate relation. Changing
    # them to blank preserves the old inductive relation and can expose
    # additional equivalent states.
    pruned = []
    for dfa, es in zip((left, right), edges):
        used = {(src, bit): dst for dst, incoming in es.items()
                for bit, src in incoming}
        pruned.append([[used.get((i, b), 0) for b in (0, 1)]
                       for i in range(len(dfa))])
    left, right = pruned
    rows = [set() for _ in left]
    for q, a, l, r in relation:
        rows[l].add((q, a, r))
    new_left, lc = refine(left, map(frozenset, rows))
    rows = [set() for _ in right]
    for q, a, l, r in relation:
        rows[r].add((q, a, lc[l]))
    new_right, rc = refine(right, map(frozenset, rows))
    new_relation, _ = closure(table, new_left, new_right)
    return new_left, new_right, len(relation), len(new_relation)


def compress(table, left, right):
    while True:
        l, r, n, m = quotient(table, left, right)
        if (len(l), len(r)) == (len(left), len(right)):
            return l, r, m
        left, right = l, r


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    obj = json.loads(args.input.read_text())
    left, right, count = compress(obj["table"], obj["L"], obj["R"])
    print(f"{len(obj['L'])}x{len(obj['R'])} -> {len(left)}x{len(right)}, {count} configurations")
    obj.update(L=left, R=right, reachable=count)
    args.output.write_text(json.dumps(obj, separators=(",", ":"))+"\n")


if __name__ == "__main__":
    main()
