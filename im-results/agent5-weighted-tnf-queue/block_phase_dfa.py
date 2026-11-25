#!/usr/bin/env python3
"""Synthesize binary MITM DFAs from the existing block-FAR certificate.

The output is an untrusted witness for the original BusyCoq MITMDFA decider.
Only an original-source Coq success establishes a source certificate.
"""
from collections import defaultdict, deque
from pathlib import Path
from tempfile import TemporaryDirectory
import argparse
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "agent13-block-far"))
from generate_multi import generate

CASES = {
    "0": ("1RB1RD_1RC0LD_0LA0RE_1LA1LB_0RF---_0LA1RA", 3, 2, 2, 5, False),
    "300": ("1RB0LC_1RC1RE_1LA0LD_0RA0LB_0RF---_0RB1RA", 3, 2, 4, 7, False),
    "400a": ("1RB---_1RC1RD_0LB0RF_0LE1LD_0LC1LB_0RA0RF", 3, 2, 4, 8, False),
    "400b": ("1RB1LA_1RC1RD_0LB0RE_0LE0RF_---1LA_1RA1RC", 2, 2, 4, 2, True),
    "600": ("1RB1LE_1RC0RD_1LB0RE_1RF0LE_0LA0LB_---0RA", 2, 2, 4, 2, True),
    "700": ("1RB0RA_1RC1LB_1LB0LD_0LE0LD_1RE1LF_---1RA", 3, 2, 4, 4, False),
    "2700": ("1RB0LD_1LC1RA_1LE1LA_---0RB_1RE0RF_1RF0LC", 3, 2, 4, 5, False),
    "2800": ("1RB0RD_1LC1LB_0LE1RA_0LC0RA_1LF1LD_1RD---", 3, 2, 4, 2, False),
}


def phase_dfa(width, initial, step, reverse=False, limit=100000):
    # Entry p holds the block-DFA state and the pending p-bit word.
    # Appending a bit advances every possible alignment at once.
    start = tuple((initial, 0) for _ in range(width))
    def push(st, b):
        result = [None] * width
        for p, (q, v) in enumerate(st):
            v = (v << 1 | b) if reverse else (v | b << p)
            if p == width - 1:
                result[0] = (step(q, v), 0)
            else:
                result[p + 1] = (q, v)
        return tuple(result)

    states = [start]
    ids = {start: 0}
    tr = []
    for st in states:
        row = []
        for bit in (0, 1):
            nxt = push(st, bit)
            if nxt not in ids:
                if len(states) >= limit:
                    raise RuntimeError("phase DFA limit")
                ids[nxt] = len(states)
                states.append(nxt)
            row.append(ids[nxt])
        tr.append(row)
    assert tr[0][0] == 0, "blank extension must preserve the initial state"
    return tr


def lift_certificate(cert):
    width = cert["width"]
    alphabet = 1 << width
    d, n = cert["left_states"], cert["right_nodes"]
    # Totalize the original partial left DFA by adding a rejecting sink.
    def left_step(q, a):
        if q == d:
            return d
        nxt = cert["push"][q * alphabet + a]
        return nxt - 1 if nxt else d

    # Reverse the right NFA, using the set of blank-accepting nodes as
    # its start set. This recognizes the original near-to-far language
    # when scanning the right tape from infinity towards the head.
    inverse = [[0] * n for _ in range(alphabet)]
    for v in range(n):
        for a in range(alphabet):
            for t in cert["edges"][v * alphabet + a]:
                inverse[a][t] |= 1 << v
    def right_step(s, a):
        result = 0
        while s:
            bit = s & -s
            result |= inverse[a][bit.bit_length() - 1]
            s ^= bit
        return result

    zero = sum(1 << v for v in cert["zero_states"])
    assert left_step(0, 0) == 0 and right_step(zero, 0) == zero
    return (phase_dfa(width, 0, left_step),
            phase_dfa(width, zero, right_step, reverse=True))


def inverse_edges(tr):
    inv = [[] for _ in tr]
    for q, row in enumerate(tr):
        for b, r in enumerate(row):
            inv[r].append((q, b))
    return inv


def primitive_closure(table, left, right, limit=2000000):
    code = table.replace("_", "")
    assert len(code) == 36
    moves = [None if t == "---" else (int(t[0]), t[1] == "R", ord(t[2]) - 65)
             for t in (code[i:i+3] for i in range(0, 36, 3))]
    lpre, rpre = inverse_edges(left), inverse_edges(right)
    start = (0, 0, 0, 0)
    seen, pending = {start}, deque([start])
    while pending:
        q, l, b, r = pending.popleft()
        mv = moves[2*q + b]
        if mv is None:
            raise RuntimeError("primitive abstract halt")
        w, direction, q2 = mv
        if direction:
            successors = ((q2, left[l][w], b2, r2) for r2, b2 in rpre[r])
        else:
            successors = ((q2, l2, b2, right[r][w]) for l2, b2 in lpre[l])
        for nxt in successors:
            if nxt not in seen:
                if len(seen) >= limit:
                    raise RuntimeError("primitive closure limit")
                seen.add(nxt)
                pending.append(nxt)
    return len(seen)


def discovered_closure(table, push, limit=2000000):
    """The source CTL-style closure discovers only actually pushed edges."""
    code = table.replace("_", "")
    moves = [None if t == "---" else (int(t[0]), t[1] == "R", ord(t[2]) - 65)
             for t in (code[i:i+3] for i in range(0, 36, 3))]
    edges = [defaultdict(set), defaultdict(set)]
    waiting = [defaultdict(list), defaultdict(list)]
    seen = {(0, 0, 0, 0)}
    pending = deque(seen)
    for side in (0, 1):
        assert push(side, 0, 0) == 0
        edges[side][0].add((0, 0))

    def add(st):
        if st not in seen:
            if len(seen) >= limit:
                raise RuntimeError("discovered closure limit")
            seen.add(st)
            pending.append(st)

    def pop(st, b, pred):
        q, a, l, r = st
        w, d, q2 = moves[2*q + a]
        if d:
            add((q2, b, push(0, l, w), pred))
        else:
            add((q2, b, pred, push(1, r, w)))

    while pending:
        st = pending.popleft()
        q, a, l, r = st
        mv = moves[2*q + a]
        if mv is None:
            raise RuntimeError("discovered abstract halt")
        w, d, q2 = mv
        side = int(d)
        old = l if d else r
        dest = push(1-side, old, w)
        edge = w, old
        if edge not in edges[1-side][dest]:
            edges[1-side][dest].add(edge)
            for waiter in waiting[1-side][dest]:
                pop(waiter, *edge)
        target = r if d else l
        waiting[side][target].append(st)
        for b, pred in edges[side][target]:
            pop(st, b, pred)
    return len(seen), edges


def run_residue_3500():
    table = "1RB0RC_1LC1RD_---1RB_0LD0RE_1LE0LF_1RA1LF"
    # Four nearest runs, each length modulo 9. A zero-only stack is
    # the empty summary. Retain the run even when its residue is zero.
    states = [[()], [()]]
    ids = [{(): 0}, {(): 0}]
    delta = [{}, {}]

    def push(side, q, b):
        key = q, b
        if key in delta[side]:
            return delta[side][key]
        st = states[side][q]
        if not st and b == 0:
            nxt = ()
        elif st and st[0][0] == b:
            nxt = ((b, (st[0][1] + 1) % 9),) + st[1:]
        else:
            nxt = ((b, 1),) + st[:3]
        if nxt not in ids[side]:
            ids[side][nxt] = len(states[side])
            states[side].append(nxt)
        dest = ids[side][nxt]
        delta[side][key] = dest
        return dest

    count, _ = discovered_closure(table, push)
    left, right = [
        [[d.get((q, b), 0) for b in (0, 1)] for q in range(len(s))]
        for d, s in zip(delta, states)
    ]
    # Recompute against the actual finite tables, independent of the
    # interned run summaries. Unused push rows do not enter the invariant.
    check_count, _ = discovered_closure(table, lambda side, q, b: (left, right)[side][q][b])
    assert count == check_count
    print(f"3500: binary DFAs {len(left)} x {len(right)}, closure {count}", flush=True)
    return dict(label="3500", table=table, L=left, R=right, reachable=count)


def synthesize(label):
    if label == "3500":
        return run_residue_3500()
    table, width, cap, mod, runs, flip = CASES[label]
    with TemporaryDirectory() as folder:
        cert = generate(table, Path(folder), width=width, cap=cap, mod=mod,
                        runs=runs, flip=flip, name="Phase", minimize_left=(label == "0"))
    left, right = lift_certificate(cert)
    if flip:
        left, right = right, left
    count = primitive_closure(table, left, right)
    print(f"{label}: binary DFAs {len(left)} x {len(right)}, closure {count}", flush=True)
    return dict(label=label, table=table, L=left, R=right, reachable=count)


def coq_list(dfa):
    flat = [str(x) for row in dfa for x in row]
    return "[" + ";\n  ".join(";".join(flat[i:i+40]) for i in range(0, len(flat), 40)) + "]%list"


def emit_coq(rows, path):
    # Primitive MITMDFA accepts two binary DFA transition tables. The original
    # source solver proves nonhalting independently of the block witness.
    lines = ["From BusyCoq Require Import CTL62 Individual62.",
             "From Coq Require Import List NArith.", "Import ListNotations.",
             "Open Scope N_scope.", "Open Scope string_scope.",
             "Definition phase_symbol_id (s : Sym) := match s with S0 => int0 | S1 => int1 end."]
    for row in rows:
        label = row["label"]
        n = row["reachable"]
        lines += [
            f"Definition phase_left_{label} : list N := {coq_list(row['L'])}.",
            f"Definition phase_right_{label} : list N := {coq_list(row['R'])}.",
            f"Definition phase_param_{label} := MITMDFA {max(100, n)} {max(1000, 2*n)} phase_left_{label} phase_right_{label} phase_symbol_id (N_to_int 2).",
            f"Lemma phase_nonhalt_{label} : ~ halts (TM_from_str \"{row['table']}\") c0.",
            f"Proof. solve_cert phase_param_{label}. Qed.",
            f"Print Assumptions phase_nonhalt_{label}."
        ]
    path.write_text("\n\n".join(lines) + "\n")


def main():
    p = argparse.ArgumentParser()
    p.add_argument("labels", nargs="+", choices=[*CASES, '3500'])
    p.add_argument("--output", required=True, type=Path)
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    rows = []
    for label in args.labels:
        row = synthesize(label)
        rows.append(row)
        (args.output / f"phase-{label}.json").write_text(json.dumps(row))
    emit_coq(rows, args.output / "Agent5PhaseMITM.v")


if __name__ == "__main__":
    main()
