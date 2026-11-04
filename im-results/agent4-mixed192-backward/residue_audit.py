"""Independent finite-residue audit of the two source-certified mixed-192 gates.

This verifies the arithmetic classification only. Source-wide reachability
nonexistence is proved separately by Lean and is not inferred from this scan.
"""
from fractions import Fraction

A48 = {(7, 26), (8, 27), (17, 33), (31, 38), (32, 39),
       (43, 47), (45, 46), (55, 2), (56, 3), (65, 9),
       (79, 14), (80, 15), (86, 21), (93, 22)}
B48 = {(7, 2), (8, 3), (17, 9), (21, 10), (31, 14),
       (32, 15), (38, 21), (43, 23), (55, 26), (56, 27),
       (65, 33), (69, 34), (79, 38), (80, 39)}
A_DIRECT = {(16, 58), (112, 26), (64, 10), (160, 42)}
B_DIRECT = {(40, 2), (136, 34), (88, 18), (184, 50)}


def high_a(a: int, k: int, c: int) -> bool:
    d = (a - c) % 96
    t = (a + k) % 192
    return ((d, t % 48) in A48 or (d == 32 and t == 93)
            or (d == 35 and t % 96 == 45))


def high_b(a: int, k: int, c: int) -> bool:
    d = (a - c) % 96
    t = (a + k) % 192
    return ((d, t % 48) in B48 or (d == 80 and t == 93)
            or (d == 83 and t % 96 == 45))


def category(j: int, m: int) -> str | None:
    if j % 12 == 4 and m % 8 == 4:
        return "wide"
    if j % 48 == 43 and m % 16 == 11:
        return "side_A"
    if j % 48 == 19 and m % 16 == 3:
        return "side_B"
    if (j % 192, m % 64) in A_DIRECT:
        return "direct_A"
    if (j % 192, m % 64) in B_DIRECT:
        return "direct_B"
    return None


def main() -> None:
    counts = {"wide": 0, "side_A": 0, "side_B": 0,
              "direct_A": 0, "direct_B": 0}
    for j in range(192):
        for m in range(192):
            # For every actual m>=2, 2^(2*m+2) = 64 (mod 192).
            k = (64 * (j + 3) - j - 3 * m - 5) % 192
            a = (2 * j + 3) % 192
            from_core = high_a(a, (k - 3) % 192, 3) or high_b(
                a, (k - 3) % 192, 3
            )
            which = category(j, m)
            assert from_core == (which is not None), (j, m, k, which)
            if which is not None:
                counts[which] += 1

    assert counts == {"wide": 384, "side_A": 48, "side_B": 48,
                      "direct_A": 12, "direct_B": 12}, counts
    total = sum(counts.values())
    assert total == 504
    print(f"Source-predicate arithmetic agreement: PASS, {192 ** 2} cells")
    print(f"Counts by disjoint category: {counts}")
    print(f"Excluded residue cells: {total}/{192 ** 2} = "
          f"{Fraction(total, 192 ** 2)}")


if __name__ == "__main__":
    main()
