"""Exact full-period comparison of two independent P1 cost-14 sieves.

Reads the source-verified 695/700/701/79 residue lists directly from Lean
files, computes the 4096 binary-marker cost-14 support residues, and compares
the sets. Also independently executes the scalar inverse grammar for all q.

This script is an integer-only comparison, not an original-source Lean proof.
Run from any directory; repository paths are resolved relative to this file.
"""
from functools import lru_cache
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
D695 = ROOT / "im-results/agent9-p1-q1024-cost11/DensityCount695.lean"
D700 = ROOT / "im-results/agent9-p1-k10-budget12/DensityCount700.lean"
QFINAL = ROOT / "im-results/agent28-p1-affine4096/QFinal.lean"
P = 4096


def lean_list(path: Path, name: str) -> set[int]:
    match = re.search(
        rf"def\s+{name}\s*:\s*List Nat\s*:=\s*\[([^]]*)\]",
        path.read_text(encoding="utf-8"),
        re.DOTALL,
    )
    if match is None:
        raise ValueError(f"Missing {name} in {path}")
    return {int(x.strip()) for x in match.group(1).split(",") if x.strip()}


def source_certified_residues() -> set[int]:
    a = {name: lean_list(D695, name) for name in
         ("previous256", "previousCost11", "newCost10", "newCost11", "lowTail")}
    k10 = lean_list(D700, "k10New")
    expanded_q = lean_list(QFINAL, "newQ") | {5}  # original q=4101+4096*r

    def certified(q: int) -> bool:
        r = q % 1024
        return (
            q % 4 in (0, 3)
            or q % 256 in a["previous256"]
            or r in {29, 297, 853}
            or r in a["previousCost11"] | a["newCost10"] | a["newCost11"]
            or r in a["lowTail"] | k10
            or q in expanded_q
        )

    return {q for q in range(P) if certified(q)}


def marker_support() -> set[int]:
    """One legal q residue for each of the 4096 positive cost-14 compositions."""
    support: set[int] = set()
    final_bit = 1 << 12
    final_weight = (1 << 11) * (12 + 8)
    for bits in range(P):
        marker = final_bit + bits
        score = final_weight
        for i in range(12):
            if (bits >> i) & 1:
                score += 4 if i == 0 else (1 << (i - 1)) * (i + 8)

        coefficient = 3 + 8 * marker
        residue = (-(1 + score) * pow(coefficient, -1, P)) % P
        support.add(residue)

    return support


def grammar_cost14_support() -> set[int]:
    def count(q: int) -> int:
        L = 16 * q + 8
        z0 = 12 * q + 4

        @lru_cache(maxsize=None)
        def go(m: int, z: int) -> int:
            if m == 14:
                return 1
            total = 0
            for cost in range(1, 15 - m):
                t = cost - 1
                if z % (1 << t):
                    continue
                numerator = L + m + t + z // (1 << t)
                if numerator % 2 == 1:
                    total += go(m + cost, (numerator - 1) // 2)
            return total

        return go(0, z0)

    return {q for q in range(P) if count(q) > 0}


def main() -> None:
    certified = source_certified_residues()
    unresolved = set(range(P)) - certified
    via_markers = marker_support()
    via_grammar = grammar_cost14_support()

    assert len(certified) == 2883
    assert len(unresolved) == 1213
    assert unresolved == via_markers == via_grammar, (
        sorted(unresolved ^ via_markers)[:20],
        sorted(via_markers ^ via_grammar)[:20],
    )
    print("Source-certified q residues modulo 4096:", len(certified))
    print("Remaining q residues:", len(unresolved))
    print("Exact cost-14 marker support:", len(via_markers))
    print("Independent scalar-grammar cost-14 support:", len(via_grammar))
    print("All three 4096-residue sets coincide exactly.")


if __name__ == "__main__":
    main()
