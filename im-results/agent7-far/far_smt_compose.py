#!/usr/bin/env python3
"""Composed-bitset SMT synthesis for finite-automata nonhalting certificates.

The candidate generator is untrusted. Every emitted model is checked by
Lean's Data.fastValid_sound in agent7-far-hard-root.yml.
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

from z3 import (
    And, BitVec, BitVecVal, Bool, Extract, If, Implies, Or,
    SolverFor, ULT, is_true, sat, unsat,
)


def parse_table(code: str):
    raw = code.replace("_", "").strip()
    if len(raw) != 36:
        raise ValueError(f"expected 36 transition characters, got {len(raw)}: {code}")
    out = []
    for i in range(0, 36, 3):
        token = raw[i:i + 3]
        if token in ("---", "HHH"):
            out.append(None)
            continue
        if token[0] not in "01" or token[1] not in "LR" or token[2] not in "ABCDEF":
            raise ValueError(f"bad transition token {token!r} in {code}")
        out.append((int(token[0]), token[1] == "R", ord(token[2]) - ord("A")))
    return out


def solve_one(table, d: int, reflected: bool, timeout_ms: int):
    """Find any Data d satisfying the exact finite certificate constraints."""
    n = 6 * d + 1
    halt = n - 1
    width = max(1, d.bit_length())
    solver = SolverFor("QF_BV")
    solver.set(timeout=timeout_ms)

    delta = [
        [BitVec(f"delta_{d}_{reflected}_{l}_{b}", width) for b in range(2)]
        for l in range(d)
    ]
    for l in range(d):
        for b in range(2):
            solver.add(ULT(delta[l][b], BitVecVal(d, width)))
    solver.add(delta[0][0] == BitVecVal(0, width))

    # Remove unreachable-state symmetries: every nonzero DFA state has a
    # predecessor of lower index. All transition variables are bit-vectors.
    for state in range(1, d):
        predecessors = [
            delta[j][b] == BitVecVal(state, width)
            for j in range(state) for b in range(2)
        ]
        solver.add(Or(*predecessors))

    # E[a][s] is the N-bit set of NFA successors from node s on symbol a.
    # Nodes 0..6d-1 are (left-DFA state, control state); node 6d is halt.
    edges = [
        [BitVec(f"edge_{d}_{reflected}_{a}_{s}", n) for s in range(n)]
        for a in range(2)
    ]
    zero = [Bool(f"zero_{d}_{reflected}_{s}") for s in range(n)]

    def has_edge(mask, target: int):
        return Extract(target, target, mask) == BitVecVal(1, 1)

    halt_mask = BitVecVal(1 << halt, n)
    solver.add(edges[0][halt] == halt_mask, edges[1][halt] == halt_mask)
    solver.add(zero[halt])

    # Exact zero-suffix fixed point and blank-start safety.
    for s in range(n):
        successors = [
            And(has_edge(edges[0][s], t), zero[t])
            for t in range(n)
        ]
        solver.add(zero[s] == Or(*successors))
    solver.add(zero[0] == False)

    # Compose NFA edge masks before imposing the left-move inclusion. The
    # old encoding emitted one implication per intermediate NFA state v.
    # This is exactly the same union, but represented by one bit-vector.
    compose_cache = {}

    def composed_mask(write: int, old_left_bit: int, next_control: int, j: int):
        key = (write, old_left_bit, next_control, j)
        if key not in compose_cache:
            intermediate = 6 * j + next_control
            source_mask = edges[old_left_bit][intermediate]
            out = BitVecVal(0, n)
            for v in range(n):
                out = out | If(
                    has_edge(source_mask, v),
                    edges[write][v],
                    BitVecVal(0, n),
                )
            compose_cache[key] = out
        return compose_cache[key]

    for left_state in range(d):
        for control in range(6):
            for symbol in range(2):
                src = 6 * left_state + control
                transition = table[2 * control + symbol]
                if transition is None:
                    # An undefined row is a possible halt for every completion.
                    solver.add(has_edge(edges[symbol][src], halt))
                    continue

                write, right, next_control = transition
                if reflected:
                    right = not right

                if right:
                    for dst_left_state in range(d):
                        solver.add(Implies(
                            delta[left_state][write] == BitVecVal(dst_left_state, width),
                            has_edge(
                                edges[symbol][src],
                                6 * dst_left_state + next_control,
                            ),
                        ))
                else:
                    for j in range(d):
                        for old_left_bit in range(2):
                            dfa_match = (
                                delta[j][old_left_bit] == BitVecVal(left_state, width)
                            )
                            comp = composed_mask(write, old_left_bit, next_control, j)
                            solver.add(Implies(
                                dfa_match,
                                (comp & edges[symbol][src]) == comp,
                            ))

    result = solver.check()
    if result != sat:
        return result, None, solver.reason_unknown()

    model = solver.model()
    dfa = [
        model.eval(delta[l][b], model_completion=True).as_long()
        for l in range(d) for b in range(2)
    ]
    masks0 = [
        model.eval(edges[0][s], model_completion=True).as_long()
        for s in range(n)
    ]
    masks1 = [
        model.eval(edges[1][s], model_completion=True).as_long()
        for s in range(n)
    ]
    zmask = sum(
        1 << s for s in range(n)
        if is_true(model.eval(zero[s], model_completion=True))
    )
    return result, (dfa, masks0, masks1, zmask), ""


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("roster", type=Path)
    parser.add_argument("--line", type=int, required=True, help="1-based roster line")
    parser.add_argument("--max-dfa", type=int, default=10)
    parser.add_argument("--timeout-ms", type=int, default=120000)
    args = parser.parse_args()

    if args.line < 1:
        parser.error("--line must be positive")
    if not 6 <= args.max_dfa <= 10:
        parser.error("--max-dfa must be in [6,10]")
    if args.timeout_ms <= 0:
        parser.error("--timeout-ms must be positive")

    lines = [
        line.strip() for line in args.roster.read_text().splitlines()
        if line.strip()
    ]
    if args.line > len(lines):
        parser.error(f"roster has only {len(lines)} nonempty lines")
    code = lines[args.line - 1]
    table = parse_table(code)
    print(
        f"SMT target line={args.line} code={code} encoding=compose",
        file=sys.stderr,
        flush=True,
    )

    for d in range(6, args.max_dfa + 1):
        for reflected in (False, True):
            print(
                f"trying dfa={d} reflected={int(reflected)} timeout_ms={args.timeout_ms}",
                file=sys.stderr,
                flush=True,
            )
            result, cert, reason = solve_one(table, d, reflected, args.timeout_ms)
            if result == sat:
                dfa, masks0, masks1, zmask = cert
                print(
                    "HIT", args.line, code, d, int(reflected), "DFA", *dfa,
                    "MASK", *masks0, *masks1, "Z", zmask,
                    flush=True,
                )
                return 0
            if result == unsat:
                print(
                    f"UNSAT dfa={d} reflected={int(reflected)}",
                    file=sys.stderr,
                    flush=True,
                )
            else:
                print(
                    f"UNKNOWN dfa={d} reflected={int(reflected)} reason={reason}",
                    file=sys.stderr,
                    flush=True,
                )
    print("NO_SMT_CERTIFICATE", file=sys.stderr, flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
