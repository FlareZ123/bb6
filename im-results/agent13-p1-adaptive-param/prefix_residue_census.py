#!/usr/bin/env python3
"""Finite endpoint-integrality census for the two P1 feeder roots.

This is a diagnostic cross-check, not a source-path proof. It enumerates all
depth words of feeder-0 cost 12 (first depth >= 1) and feeder-1 cost 11,
computes the necessary q-residue from PeriodWord.block_affine, and compares
the resulting residue sets with the existing 700/1024 source-gateway census.
"""
from __future__ import annotations

from functools import lru_cache


def cost(word: tuple[int, ...]) -> int:
    return sum(t + 1 for t in word)


@lru_cache(maxsize=None)
def weight(word: tuple[int, ...]) -> int:
    if not word:
        return 0
    t, *tail = word
    return (1 << t) + (1 << (t + 1)) * weight(tuple(tail))


@lru_cache(maxsize=None)
def offset(word: tuple[int, ...]) -> int:
    if not word:
        return 0
    t, *tail_list = word
    tail = tuple(tail_list)
    return (1 << t) * (t - 1) + (1 << (t + 1)) * (
        (t + 1) * weight(tail) + offset(tail)
    )


def words_of_cost(total: int, first_min: int = 0):
    if total == 0:
        yield ()
        return
    for first in range(first_min, total):
        rest = total - first - 1
        if rest == 0:
            yield (first,)
        else:
            for tail in words_of_cost(rest):
                yield (first,) + tail


def q_residue(word: tuple[int, ...], feeder: int) -> int:
    m = cost(word)
    w = weight(word)
    o = offset(word)
    if feeder == 0:
        assert word and word[0] >= 1 and m >= 2
        numerator = 4 + 8 * w + o
        assert numerator % 4 == 0
        modulus = 1 << (m - 2)
        coefficient = 3 + 4 * w
        constant = numerator // 4
    else:
        assert word and m >= 1
        numerator = 4 + 9 * w + o
        assert numerator % 2 == 0
        modulus = 1 << (m - 1)
        coefficient = 5 + 8 * w
        constant = numerator // 2
    assert coefficient & 1
    return (-constant * pow(coefficient, -1, modulus)) % modulus


PREVIOUS_256 = [14, 30, 57, 61, 73, 77, 106, 138, 173, 217, 218, 221, 233, 238, 250, 254]
PREVIOUS_COST_11 = [
    121, 125, 137, 141, 153, 154, 169, 170, 285, 298, 537, 553, 570, 590,
    606, 621, 698, 714, 718, 734, 761, 765, 777, 781, 814, 830, 842, 925,
    942, 958, 1005,
]
NEW_COST_10 = [
    34, 42, 50, 185, 201, 281, 289, 314, 334, 350, 365, 369, 442, 458, 462,
    478, 505, 509, 517, 521, 525, 530, 557, 558, 574, 578, 586, 601, 617,
    641, 669, 677, 686, 701, 702, 717, 749, 794, 837, 861, 889, 893, 902,
    905, 909, 921, 922, 937, 938,
]
NEW_COST_11 = [
    69, 93, 114, 134, 161, 181, 226, 257, 290, 293, 306, 337, 401, 441, 453,
    457, 514, 545, 613, 625, 705, 773, 785, 786, 813, 834, 850, 857, 873,
    885, 897, 933, 957, 973,
]
LOW_TAIL = [1, 6, 26]
K10_NEW = [213, 661, 917, 977, 998]


def certified_700(q: int) -> bool:
    return (
        q % 4 in (0, 3)
        or q % 256 in PREVIOUS_256
        or q % 1024 in (29, 297)
        or q % 1024 in PREVIOUS_COST_11
        or q % 1024 in NEW_COST_10
        or q % 1024 in NEW_COST_11
        or q % 1024 in LOW_TAIL
        or q % 1024 in K10_NEW
    )


def main() -> None:
    feeder0 = {
        q_residue(w, 0)
        for w in words_of_cost(12, first_min=1)
    }
    feeder1 = {
        q_residue(w, 1)
        for w in words_of_cost(11, first_min=0)
    }
    remaining = {q for q in range(1024) if not certified_700(q)}

    assert len(feeder0) == 323
    assert len(feeder1) == 323
    assert feeder0 == feeder1
    assert remaining == feeder0 | {853}
    assert 853 not in feeder0

    print("feeder-0 cost-12 endpoint residues:", len(feeder0))
    print("feeder-1 cost-11 endpoint residues:", len(feeder1))
    print("existing source-certified residues:", sum(certified_700(q) for q in range(1024)))
    print("remaining residues:", len(remaining))
    print("remaining residue not admitting either endpoint-integrality prefix:", 853)
    print("exact set identity verified: remaining = common_prefix_residues ∪ {853}")


if __name__ == "__main__":
    main()
