"""Exact Catalan subclass of all-first-counter neutral #623 drain prefixes.

The transition table is algebraically obtained from the complete original-source
one-level drain identities proved in Agent49FlatDrainSource.lean. This program
checks finite cases only; the all-length argument is in CatalanNeutral.md.
"""

from collections import defaultdict
from math import comb


# Per ternary digit: (change in reference height + carry, next carry).
# Carries -1,0,1 correspond to the original source's q-1,q,q+1 branches.
EDGES = {
    -1: ((0, 0), (1, -1), (0, 0)),
    0: ((0, -1), (-1, 0), (0, 1)),
    1: ((-2, 0), (-1, 1), (0, 0)),
}


def neutral_charge(n: int, r: int):
    """Return universal digit charge if r has a certified neutral path."""
    height = 0
    carry = 0
    charge = 0
    for _ in range(2 * n):
        r, digit = divmod(r, 3)
        adjusted = digit + carry
        quotient, residue = divmod(adjusted, 3)
        if residue == 0:
            height += 1
            next_carry = quotient - 1
        elif residue == 1:
            height -= 1
            next_carry = quotient
            charge += 4
        else:
            height -= 1
            next_carry = quotient + 1
            charge += 2
        carry = next_carry
        if height + carry < 0:
            return None
    if height != 0 or carry != 0:
        return None
    return charge


def flat_drain(a: int, b: int, d: int):
    """Complete exact B-drain, via the source-certified one-level recursion."""
    while b:
        q, r = divmod(b, 3)
        if r == 0:
            a, b, d = a + 1, q - 1, d + 6 * q + 3
        elif r == 1:
            if a == 0:
                return None
            a, b, d = a - 1, q, d + 6 * q + 7
        elif a == 0:
            a, b, d = 0, q, d + 6 * q + 7
        else:
            a, b, d = a - 1, q + 1, d + 6 * q + 5
    return a, d


def walk_counts(max_n: int):
    """Exact infinite-state-walk DP; each finite depth has finite support."""
    dp = {(0, 0): 1}
    yield 0, 1
    for steps in range(1, 2 * max_n + 1):
        new = defaultdict(int)
        for (height, carry), count in dp.items():
            for change, next_carry in EDGES[carry]:
                level = height + change
                if level >= 0:
                    new[(level, next_carry)] += count
        dp = new
        if steps % 2 == 0:
            yield steps // 2, dp.get((0, 0), 0)


def catalan(n: int):
    return comb(2 * n, n) // (n + 1)


def main():
    for n, count in walk_counts(12):
        expected = sum(2**j * catalan(j) for j in range(n + 1))
        assert count == expected, (n, count, expected)
        print(f"n={n:2} neutral_count={count} Catalan_sum={expected}")

    for n in range(1, 5):
        modulus = 9**n
        certified = []
        for r in range(modulus):
            charge = neutral_charge(n, r)
            if charge is not None:
                certified.append((r, charge))
                for a in range(2 * n + 3):
                    for b in (1, 2, 5):
                        d = 17
                        left = flat_drain(a, modulus * b + r, d)
                        shift = 3 * ((modulus - 1) * b + r) + charge
                        right = flat_drain(a, b, d + shift)
                        assert left == right, (n, r, a, b, left, right)
        expected = sum(2**j * catalan(j) for j in range(n + 1))
        assert len(certified) == expected
        print(f"PASS: all certified residues n={n}, {len(certified)}; first counters 0..{2*n+2}")

    print("PASS: Catalan DP to n=12 and exact source-shaped prefix transports to n=4.")


if __name__ == "__main__":
    main()
