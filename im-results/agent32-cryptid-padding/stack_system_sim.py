#!/usr/bin/env python3
"""Executable prototype of the DeepMind #85/#490 closed-stack macro system.

The rules below are a direct transcription of:
  google-deepmind/cryptids/BusyBeaver/BB6/Accelerations/
    M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.lean

It works with the first coordinates of the pair stacks (all second coordinates
in this reduction are zero).  It compresses finite raw TM runs into one
closed-stack successor.  This is an experimental interpreter, not a Lean
proof and not yet an independently validated implementation of every branch.

Run:
    python stack_system_sim.py --steps 30

The regression prefix checks the exact first successor and six following
mode transitions extracted from the Lean proof.  The initial state is DeepMind's seven-step `init_reaches_nontrivial` stack
entry, not the original initial configuration. Its initial blank/head convention
still needs to be compared with this repository's D0 root adapter.
"""
from __future__ import annotations

from dataclasses import dataclass
import argparse
import json
import sys
from typing import Optional

sys.setrecursionlimit(100_000)


@dataclass(frozen=True)
class StackConfig:
    mode: str
    left: tuple[int, ...]
    right: tuple[int, ...]


@dataclass(frozen=True)
class TokenHalt:
    reason: str


def bump(xs: tuple[int, ...]) -> tuple[int, ...]:
    return (xs[0] + 1,) + xs[1:] if xs else (1,)


def bump_n(xs: tuple[int, ...], n: int) -> tuple[int, ...]:
    for _ in range(n):
        xs = bump(xs)
    return xs


def bounce_cr(r3: tuple[int, ...], k0: int, k_acc: tuple[int, ...],
              right: tuple[int, ...]) -> tuple[tuple[int, ...], tuple[int, ...]] | TokenHalt:
    """Transcription of bounce_len / bounce_CR."""
    if not right:
        if k0 == 0:
            return k_acc, (1,)
        if k0 == 1:
            return (0,) + k_acc, (0, 1)
        if k0 == 2:
            return (1,) + k_acc, (0, 1)
        return (k0 - 1,) + k_acc, (0, 1)

    a, *tail = right
    tail = tuple(tail)
    if a == 0:
        return bounce_cr(r3, k0 + 2, k_acc, tail)
    if a == 1:
        if not tail:
            return (k0 + 1,) + k_acc, (0, 0, 1)
        b, *rest = tail
        rest = tuple(rest)
        if b == 0:
            return bounce_cr(r3, 0, (k0 + 4,) + k_acc, rest)
        if b == 1:
            if not rest:
                return (k0 + 1,) + k_acc, (0, 0, 2)
            return (k0 + 1,) + k_acc, (0, 0, rest[0] + 2) + rest[1:]
        # tok_CR_1_add2, followed by bounce_DR.
        return bounce_dr(r3, (1, k0 + 1) + k_acc, (b - 2,) + rest)
    # tok_CR_add2_halts.
    return TokenHalt("tok_CR_add2_halts")


def bounce_dr(r3: tuple[int, ...], k_acc: tuple[int, ...],
              right: tuple[int, ...]) -> tuple[tuple[int, ...], tuple[int, ...]] | TokenHalt:
    """Transcription of bounce_DR."""
    if not right:
        return k_acc, (1,)

    a, *tail = right
    tail = tuple(tail)
    if a == 0:
        return bounce_dr(r3, (1,) + k_acc, tail)
    if a == 1 and not tail:
        return (1,) + k_acc, (0, 0, 1)
    # tok_DR_succ, followed by bounce_CR.
    return bounce_cr(r3, 0, (1,) + k_acc, (a - 1,) + tail)


def normalize_el(k: tuple[int, ...], r3: tuple[int, ...],
                 right_tail: tuple[int, ...]) -> StackConfig | TokenHalt:
    """Normalize tok_EL K R3 (0 :: right_tail) via bl_step_macro_len."""
    if not k:
        return StackConfig("EL", (0,) + right_tail, r3)

    a, *tail = k
    tail = tuple(tail)
    if a == 0:
        if not tail:
            return StackConfig("CR", (0,) + right_tail, bump(r3))
        k2, *k2_tail = tail
        result = bounce_cr(r3, k2 + 2, tuple(k2_tail), right_tail)
        if isinstance(result, TokenHalt):
            return result
        k_out, l_out = result
        return normalize_el(k_out, r3, l_out)
    if a == 1:
        return normalize_el(tail, r3, right_tail)
    if a == 2:
        return normalize_el(tail, r3, (1, 0) + right_tail)

    # tok_EL_add3, tok_DR_zero, then bounce_DR.
    result = bounce_dr(r3, (1, a - 3) + tail, right_tail)
    if isinstance(result, TokenHalt):
        return result
    k_out, l_out = result
    return normalize_el(k_out, r3, l_out)


def close_tok_cr(r3: tuple[int, ...], right: tuple[int, ...]) -> StackConfig | TokenHalt:
    # tok_CR_1_0_closed starts with K=[1,0].
    result = bounce_cr(r3, 0, (0,), right)
    if isinstance(result, TokenHalt):
        return result
    k_out, l_out = result
    return normalize_el(k_out, r3, l_out)


def close_tok_dr(r3: tuple[int, ...], right: tuple[int, ...]) -> StackConfig | TokenHalt:
    # tok_DR_2_0_closed starts with K=[2,0].
    result = bounce_dr(r3, (0,), right)
    if isinstance(result, TokenHalt):
        return result
    k_out, l_out = result
    return normalize_el(k_out, r3, l_out)


def successor(c: StackConfig) -> StackConfig | TokenHalt:
    """One outer closed-stack successor, following the four mode lemmas."""
    mode, left, right = c.mode, c.left, c.right

    if mode == "CR":
        if not left:
            return StackConfig("EL", (0,), bump(right))
        a, *tail = left
        tail = tuple(tail)
        if a == 0:
            return StackConfig("CR", tail, bump_n(right, 2))
        if a == 1:
            if not tail:
                return StackConfig("EL", (0,), (0,) + bump_n(right, 3))
            b, *rest = tail
            rest = tuple(rest)
            if b == 0:
                return StackConfig("CR", (1,) + rest, (0, 0) + bump(right))
            if b == 1:
                if not rest:
                    return StackConfig("EL", (0, 0, 0, 0), (1, 0) + right)
                return StackConfig("EL", (0, 0, 0, 0) + rest, (0, 0) + bump(right))
            return StackConfig("DR", (0,) + rest, (1, b - 2) + right)
        return TokenHalt("mode_CR_head_ge_2")

    if mode == "EL":
        if not right:
            return StackConfig("CR", left, (0,))
        a, *tail = right
        tail = tuple(tail)
        if a == 0:
            return StackConfig("EL", (0,) + left, tail)
        return StackConfig("DL", left, (a - 1,) + tail)

    if mode == "DL":
        if not right:
            return StackConfig("CR", left, (2,))
        a, *tail = right
        tail = tuple(tail)
        if a == 0:
            return StackConfig("EL", (0,) + bump(left), tail)
        if a == 1:
            return close_tok_dr(tail, left)
        return StackConfig("DR", left, (1, a - 2) + tail)

    if mode == "DR":
        if not left:
            return StackConfig("EL", (0,), right)
        a, *left_tail = left
        left_tail = tuple(left_tail)
        if not right:
            if a == 0:
                return StackConfig("EL", bump(left_tail), (0,))
            return StackConfig("DR", (a - 1,) + left_tail, (0,))
        b, *right_tail = right
        right_tail = tuple(right_tail)
        if b == 0:
            if a == 0:
                return close_tok_dr(right_tail, left_tail)
            return close_tok_cr(right_tail, (a - 1,) + left_tail)
        if a == 0:
            return StackConfig("DR", left_tail, (1, b - 1) + right_tail)
        return StackConfig("CR", (a - 1,) + left_tail, (0, b - 1) + right_tail)

    raise ValueError(f"unknown stack mode {mode!r}")


def root_prefix() -> list[StackConfig]:
    """Exact prefix from the seven-step root stack entry."""
    c = StackConfig("DR", (1,), (0, 0))
    out = [c]
    for _ in range(7):
        nxt = successor(c)
        if isinstance(nxt, TokenHalt):
            raise AssertionError(nxt)
        c = nxt
        out.append(c)
    expected = [
        StackConfig("CR", (0, 0, 1), (1,)),
        StackConfig("CR", (0, 1), (3,)),
        StackConfig("CR", (1,), (5,)),
        StackConfig("EL", (0,), (0, 8)),
        StackConfig("EL", (0, 0), (8,)),
        StackConfig("DL", (0, 0), (7,)),
        StackConfig("DR", (0, 0), (1, 5)),
    ]
    assert out[1:] == expected, (out[1:], expected)
    return out


def cylinder_token_state(c: int) -> dict[str, object]:
    """Return a compressed description; never materialize the huge K list."""
    if c % 3 != 1:
        raise ValueError("the recorded cylinder requires C ≡ 1 (mod 3)")
    m = 4 * (c // 3) - 1
    return {"mode": "tok_CR", "K_prefix": [0], "K_run": {"value": 1, "count": m},
            "R3": [1], "L": []}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--steps", type=int, default=30)
    args = parser.parse_args()
    seq = root_prefix()
    c = seq[-1]
    for _ in range(max(0, args.steps - (len(seq) - 1))):
        nxt = successor(c)
        if isinstance(nxt, TokenHalt):
            print(json.dumps({"halt": nxt.reason, "at": len(seq) - 1}))
            return
        c = nxt
        seq.append(c)
    print(json.dumps([{"mode": x.mode, "L": x.left, "R": x.right} for x in seq], indent=2))


if __name__ == "__main__":
    main()
