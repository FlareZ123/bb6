"""Fast modular Hensel residues for #746's canonical even inverse ray.

Uses pow(2, exponent, modulus) without constructing 2**n.
At depth zero, the unique residue theorem is Lean-source-certified.
At general even depths, uniqueness has a mathematical proof documented in
AlternatingRayValuation.md and is awaiting a separate Lean formalization.
"""

def numerator_mod(n: int, depth: int, modulus: int) -> int:
    """Compute the signed ray inverse numerator Z_depth(n) modulo modulus."""
    a = (1 << (depth + 1)) - 1
    b = 3 * (1 << depth) + 1
    return (8 * pow(2, n, modulus) - 2 * a * n - 2 * b + 5) % modulus


def lift_index(sector: int, depth: int, precision: int) -> int:
    """Return the unique index modulo 3**precision with 3**(precision+1) | Z.

    Preconditions: sector is 4 or 5, depth is nonnegative and even,
    and precision is nonnegative. The return value is canonical.
    """
    if sector not in (4, 5) or depth < 0 or depth % 2 or precision < 0:
        raise ValueError("sector must be 4 or 5, depth nonnegative even, precision >= 0")
    residue = 0
    period = 1
    divisor = 3
    for _ in range(precision):
        numerator = numerator_mod(sector + 6 * residue, depth, 3 * divisor)
        if numerator % divisor:
            raise ArithmeticError("Hensel invariant violated")
        digit = numerator // divisor
        residue += period * digit
        period *= 3
        divisor *= 3
    return residue


def test_small() -> None:
    expected = {
        4: {0: 48, 2: 74, 4: 64, 6: 9},
        5: {0: 0, 2: 13, 4: 17, 6: 48},
    }
    for sector, outcomes in expected.items():
        for depth, residue in outcomes.items():
            assert lift_index(sector, depth, 4) == residue
            for k in range(5):
                modulus = 3 ** (k + 1)
                chosen = lift_index(sector, depth, k)
                hits = [h for h in range(3**k)
                        if numerator_mod(sector + 6*h, depth, modulus) == 0]
                assert hits == [chosen]
        for depth in (1, 3, 5, 7):
            assert all(numerator_mod(sector + 6*h, depth, 3) != 0
                       for h in range(40))


def test_high_precision() -> None:
    for sector in (4, 5):
        for depth in (0, 2, 6):
            precision = 256
            residue = lift_index(sector, depth, precision)
            modulus = 3 ** (precision + 1)
            assert residue < 3**precision
            assert numerator_mod(sector + 6*residue, depth, modulus) == 0


if __name__ == "__main__":
    test_small()
    test_high_precision()
    print("PASS: complete small residue periods and 256-digit modular lifting")
