#!/usr/bin/env python3
"""Full-lift overlap audit of six Sheep E families against prior F depth five.

Reuses the independently implemented F-sieve arithmetic from the separate
Agent16 audit and re-verifies its entire SHA256 before comparing all residues.
Requires Python 3.10+ and SymPy 1.14.
"""
from fractions import Fraction
from hashlib import sha256
from math import gcd
from pathlib import Path
import sys

SOURCE = Path(__file__).resolve().parents[1] / "agent16-sheep-new-even-cones"
sys.path.insert(0, str(SOURCE))
from prior_f5_overlap import closes, OLD_MOD  # noqa: E402
from certificate import CASES, PRIOR  # noqa: E402

OLD_SHA = "dc77776f9a51938d6c6e1fdb57be681477dae9b93d54fa351d4d4f9ae4b6555b"


def main():
    excluded = {r for r in range(OLD_MOD) if closes((0, 0, 1), r, 5)}
    digest = sha256(",".join(map(str, sorted(excluded))).encode()).hexdigest()
    assert len(excluded) == 3596 and digest == OLD_SHA
    print("PASS old 3596/5400 F classes, exact digest", digest)

    newly = Fraction(0)
    for i, (j, period) in enumerate(CASES):
        lifted = {(j + period * k) % OLD_MOD
                  for k in range(OLD_MOD // gcd(OLD_MOD, period))}
        assert not (lifted & excluded), (j, period, lifted & excluded)
        assert all((j-r) % gcd(period, p) != 0 for r, p in PRIOR)
        assert all((j-r) % gcd(period, p) != 0 for r, p in CASES[:i])
        newly += Fraction(1, period)
        print(f"PASS new {j}+{period}k: {len(lifted)} "
              f"F-quotient survivors {sorted(lifted)}")

    assert newly == Fraction(22, 54675)
    older = Fraction(3596, 5400) + sum(
        (Fraction(1, p) for _, p in PRIOR), Fraction(0))
    combined = older + newly
    assert combined == Fraction(1022023, 1530900)
    print("PASS incremental exponent density", newly, float(newly * 100), "%")
    print("PASS combined nonoverlap density", combined,
          float(combined * 100), "%")


if __name__ == "__main__":
    main()
