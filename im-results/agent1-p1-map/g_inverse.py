"""Exact complete inverse of positive-first-output P1 G drain; Lean: GInverse.lean."""


def g(k: int, c: int) -> tuple[int, int]:
    while c < 2 * k:
        k, c = k - (c // 2 + 1), 2 * c + 3
    if c <= 2 * k + 1:
        return 0, 2 * c + 3
    return 4 * k + 4, c - (2 * k + 2)


def inverse_g(b: int, d: int) -> list[tuple[int, int]]:
    """All (k,c) with G(k,c)=(b,d), for b>0 and d>=0."""
    if b < 4 or b % 4 or d < 0:
        return []
    k = b // 4 - 1
    c = d + 2 * k + 2
    out = [(k, c)]
    while c >= 3 and c % 2:
        c = (c - 3) // 2
        k += c // 2 + 1
        out.append((k, c))
    return out


def test() -> None:
    tested = 0
    for k in range(300):
        for c in range(300):
            b, d = g(k, c)
            if b == 0:
                continue
            inv = inverse_g(b, d)
            assert (k, c) in inv, (k, c, b, d, inv)
            for kp, cp in inv:
                assert g(kp, cp) == (b, d), (k, c, b, d, kp, cp)
            tested += 1
    print(f"verified {tested:,} positive-output G inputs, all generated inverse edges valid")
    for n in (2, 6, 10, 14, 18, 22):
        d = 14 * (2**n) - 2 * n - 10
        gate = d - 6
        print(f"n={n}: gateway=({gate},3), G-input preimages={inverse_g(gate, 3)}")


if __name__ == "__main__":
    test()
