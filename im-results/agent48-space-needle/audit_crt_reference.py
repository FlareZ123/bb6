#!/usr/bin/env python3
"""Independently audit the external Space Needle CRT list for 1 <= a <= 40.

Requires SymPy. It factors q_a=2^(a+1)+3, computes exact multiplicative
orders and discrete logarithms modulo each prime power, then combines the
required exponent congruences with generalized CRT. For q_a <= 2^26 it also
checks subgroup membership by direct enumeration of powers of two.
"""

from __future__ import annotations

from math import gcd

from sympy import factorint, isprime
from sympy.ntheory.residue_ntheory import discrete_log, n_order

REFERENCE_OBSTRUCTIONS = [1, 4, 9, 10, 13, 19, 21, 22, 23, 24, 25, 26, 31, 32, 33, 39, 40]


def crt_pair(a: int, m: int, b: int, n: int) -> tuple[int, int] | None:
    """Solve x=a (mod m), x=b (mod n), or return None if inconsistent."""
    g = gcd(m, n)
    if (b - a) % g:
        return None
    n_reduced = n // g
    multiplier = (
        ((b - a) // g) * pow(m // g, -1, n_reduced)
    ) % n_reduced if n_reduced > 1 else 0
    modulus = m * n_reduced
    return (a + m * multiplier) % modulus, modulus


def direct_power_membership(q: int, residue: int) -> tuple[bool, int]:
    """Return whether residue is a power of 2 modulo q and the order of 2."""
    value = 1
    order = 0
    while True:
        if value == residue:
            return True, order
        value = (2 * value) % q
        order += 1
        if value == 1:
            return False, order


def classify(a: int) -> dict[str, object]:
    q = 2 ** (a + 1) + 3
    residue = ((2 * a - 3) * pow(2, -1, q)) % q
    factors = factorint(q)
    parts: list[tuple[int, int, int]] = []

    for prime, exponent in sorted(factors.items()):
        prime = int(prime)
        exponent = int(exponent)
        prime_power = prime**exponent
        assert isprime(prime)
        local_residue = residue % prime_power
        if local_residue % prime == 0:
            return {"a": a, "q": q, "residue": residue, "factors": factors,
                    "obstructed": True, "reason": f"{prime} divides residue", "parts": parts}
        order = int(n_order(2, prime_power))
        if pow(local_residue, order, prime_power) != 1:
            return {"a": a, "q": q, "residue": residue, "factors": factors,
                    "obstructed": True, "reason": f"residue^order != 1 mod {prime_power}", "parts": parts}
        logarithm = int(discrete_log(prime_power, local_residue, 2))
        assert 0 <= logarithm < order
        assert pow(2, logarithm, prime_power) == local_residue
        parts.append((prime_power, order, logarithm))

    combined_residue, combined_modulus = parts[0][2], parts[0][1]
    for prime_power, order, logarithm in parts[1:]:
        combined = crt_pair(combined_residue, combined_modulus, logarithm, order)
        if combined is None:
            return {"a": a, "q": q, "residue": residue, "factors": factors,
                    "obstructed": True,
                    "reason": f"CRT conflict with {logarithm} mod {order}", "parts": parts}
        combined_residue, combined_modulus = combined

    return {"a": a, "q": q, "residue": residue, "factors": factors,
            "obstructed": False,
            "exponent_class": (combined_residue, combined_modulus), "parts": parts}


def main() -> None:
    records = [classify(a) for a in range(1, 41)]
    obstructed = [int(row["a"]) for row in records if row["obstructed"]]
    admissible = [int(row["a"]) for row in records if not row["obstructed"]]
    extras = sorted(set(obstructed) - set(REFERENCE_OBSTRUCTIONS))
    missing = sorted(set(REFERENCE_OBSTRUCTIONS) - set(obstructed))

    for row in records:
        q = int(row["q"])
        if q <= 2**26:
            found, order = direct_power_membership(q, int(row["residue"]))
            assert found == (not bool(row["obstructed"])), (row["a"], row, found, order)

    print(f"obstructed ({len(obstructed)}): {obstructed}")
    print(f"admissible ({len(admissible)}): {admissible}")
    print(f"extra vs external 17-value reference: {extras}")
    print(f"reference entries missing from recomputation: {missing}")
    print("direct subgroup enumeration agrees for every q <= 2^26")
    for a in extras:
        row = records[a - 1]
        print(f"a={a}: q={row['q']}, factors={row['factors']}, "
              f"reason={row['reason']}, parts={row['parts']}")

    assert len(obstructed) == 23
    assert extras == [7, 12, 18, 28, 35, 36]
    assert not missing


if __name__ == "__main__":
    main()
