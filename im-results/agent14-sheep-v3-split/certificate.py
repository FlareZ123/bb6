"""Complete-period arithmetic certificate for Sheep root powers with v3(j/17496)=0.

Run with Python 3.10+; standard library only. The period and all exceptional
inequalities are checked exactly, with no heuristic cutoffs.
"""
from math import gcd

SCALE = 17496
PERIOD_N = 63
PERIOD_J = SCALE * PERIOD_N


def gap_threshold(h: int) -> int:
    d = 3 ** h
    for a in range(1, 100):
        k = d * (2 * a - 3) + 2 ** (h + 1)
        if 1 < k < 2 ** a and 2 ** a >= 2 * d:
            return a
    raise AssertionError(("no gap threshold", h))


def check_special_gap():
    """Bases imply no odd-cofactor-3 source for j>=17496."""
    for h in range(9):
        d = 3 ** h
        r30 = d * 32 + 2 ** h
        assert 0 < r30 < 2 ** 30
        high_a29 = 3 * d * 2 ** 29 + d * 31 + 2 ** h
        assert high_a29 < 2 ** 44


def periodic_rows():
    """For each h,a, certify the complete k period q<=17."""
    rows = []
    for h in range(9):
        d = 3 ** h
        threshold = gap_threshold(h)
        for a in range(1, threshold):
            modulus = d * (2 ** (a + 1) + 1)
            k = d * (2 * a - 3) + 2 ** (h + 1)
            q = next((q for q in range(1, 18)
                      if pow(2, PERIOD_J * q, modulus) == 1), None)
            assert q is not None
            rows.append((h, a, modulus, k % modulus, q))
    assert len(rows) == 87
    return rows


def root_parents_by_residue(rows):
    census = {}
    for r in range(1, 64):
        if r % 3 == 0:
            continue  # v3(n) is fixed at zero for n=r+63*k
        j = SCALE * r
        candidates = []
        for h, a, modulus, residue, q in rows:
            if any(pow(2, j + h + 1 + PERIOD_J * t, modulus) == residue
                   for t in range(q)):
                candidates.append((h, a))
        census[r] = candidates
    return census


def main():
    check_special_gap()
    rows = periodic_rows()
    census = root_parents_by_residue(rows)
    free = tuple(r for r, candidates in census.items() if not candidates)
    assert len(census) == 42
    assert len(free) == 30
    assert max(row[4] for row in rows) <= 17
    assert all((not candidates) == ((r % 7 != 1) and (r % 9 != 8))
               for r, candidates in census.items())
    assert all(set(candidates).issubset({(3, 6), (8, 2)})
               for candidates in census.values())
    assert all(((3, 6) in candidates) == (r % 7 == 1)
               for r, candidates in census.items())
    assert all(((8, 2) in candidates) == (r % 9 == 8)
               for r, candidates in census.items())
    print("Generic low-a rows:", len(rows))
    print("Maximum full-period q:", max(x[4] for x in rows))
    print("Full-period checks per root class:", sum(x[4] for x in rows))
    print("Eligible coprime-to-three residues:", len(census))
    print("Predecessor-free residues:", len(free))
    print("r mod 63:", ",".join(map(str, free)))
    print("Only generic congruence survivors: (3,6) if r%7=1, "
          "(8,2) if r%9=8")
    print("PASS: all 30 residue classes are predecessor-free at every k")


if __name__ == "__main__":
    main()
