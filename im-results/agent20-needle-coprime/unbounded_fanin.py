"""Reproducible Space Needle inverse fan-in witness; no blank-root claim.

Uses the exact one-counter affine successor from the source-certified
Space Needle reduction. Runs with stock Python 3.11+.
"""

from math import gcd


def successor(d: int) -> int | None:
    """The published macro counter successor, None at a power of two."""
    x = d + 2
    v = (x & -x).bit_length() - 1
    u = x >> v
    if u == 1:
        return None
    return d + v + 3 * ((u - 1) // 2)


def coprime_valuations(count: int) -> list[int]:
    """Select count pairwise-coprime denominator parameters, greedily."""
    vals: list[int] = []
    product = 1
    v = 0
    while len(vals) < count:
        denominator = (1 << (v + 1)) + 3
        if gcd(product, denominator) == 1:
            vals.append(v)
            product *= denominator
        v += 1
    return vals


def common_successor(vals: list[int]) -> tuple[int, list[tuple[int, int]]]:
    """Construct one destination with a distinct predecessor for each v."""
    target_x = 0
    modulus = 1
    biases: list[int] = []

    for v in vals:
        denominator = (1 << (v + 1)) + 3
        bias = 3 * (1 << v) + v + 3
        assert gcd(modulus, denominator) == 1
        offset = ((bias - target_x) * pow(modulus, -1, denominator)) % denominator
        target_x += modulus * offset
        modulus *= denominator
        biases.append(bias)

    largest_bias = max(biases)
    if target_x < largest_bias:
        target_x += ((largest_bias - target_x + modulus - 1) // modulus) * modulus

    target_d = target_x - 2
    sources: list[tuple[int, int]] = []
    for v in vals:
        denominator = (1 << (v + 1)) + 3
        bias = 3 * (1 << v) + v + 3
        q, rem = divmod(target_x - bias, denominator)
        assert rem == 0 and q >= 0
        source_d = (1 << v) * (2 * q + 3) - 2
        assert source_d >= 1
        assert ((source_d + 2) & -(source_d + 2)).bit_length() - 1 == v
        assert successor(source_d) == target_d
        sources.append((v, source_d))

    assert len({source_d for _, source_d in sources}) == len(vals)
    return target_d, sources


def main() -> None:
    valuations = coprime_valuations(10)
    target, sources = common_successor(valuations)
    assert valuations == [0, 1, 2, 3, 5, 6, 9, 11, 14, 15]
    assert target == 479268809023655509957344

    print(f"Destination counter: {target}")
    print(f"Distinct predecessors: {len(sources)}")
    for v, predecessor in sources:
        print(f"valuation {v:2d}: predecessor counter {predecessor}")
    print("Every source transition and distinctness check passed.")


if __name__ == "__main__":
    main()
