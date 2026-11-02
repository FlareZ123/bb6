"""Finite exploratory scan of Agent 15's affine quotient filter.

This script is deliberately empirical. It samples lifts of residue pairs and
does not prove that the filter is periodic modulo 16 or that any sampled
class is excluded for all parameters. The Lean theorems remain the only
proof authority.
"""

from itertools import product


def affine_normalize(a: int, k: int) -> tuple[int, int, int]:
    """Mirror BB6.Agent15.affineNormalize; return pair and step count."""
    steps = 0
    while k >= 4 and k % 2 == 0 and (a + k) % 4 == 1:
        old_k = k
        a, k = a + k - 2, (k - 2) // 2
        assert k < old_k
        steps += 1
    return a, k, steps


def affine_quotient_excluded(a: int, k: int) -> tuple[bool, tuple[int, int], int]:
    x, y, steps = affine_normalize(a, k)
    basic = (
        y == 0
        or y == 2
        or (y % 2 == 1 and (x + y) % 4 == 2 and (x, y) != (5, 1))
    )
    quotient = (
        (x % 8 == 7 and y % 8 == 4)
        or (x % 8 == 1 and y % 16 == 2)
        or (x % 16 == 9 and y % 16 == 15)
        or (x % 16 == 1 and y % 16 == 7 and (x, y) != (1, 7))
    )
    return basic or quotient, (x, y), steps


def second_family_k(j: int, m: int) -> int:
    return 2 ** (2 * m + 2) * (j + 3) - j - 3 * m - 5


def sample_second_family(lifts: int = 16) -> tuple[list, list, list]:
    all_excluded, mixed, all_survive = [], [], []
    for rj, rm in product(range(16), repeat=2):
        flags = []
        for aj, am in product(range(lifts), repeat=2):
            j = rj + 16 * aj
            m = rm + 16 * am
            if m == 0:
                m = 16
            k = second_family_k(j, m)
            flags.append(affine_quotient_excluded(2 * j + 3, k)[0])
        if all(flags):
            all_excluded.append((rj, rm))
        elif any(flags):
            mixed.append((rj, rm))
        else:
            all_survive.append((rj, rm))
    return all_excluded, mixed, all_survive


def sample_first_family(lifts: int = 16) -> tuple[list, list, list]:
    all_excluded, mixed, all_survive = [], [], []
    for rm in range(16):
        flags = []
        for am in range(lifts):
            m = rm + 16 * am
            if m == 0:
                m = 16
            k = 2 ** (2 * m + 3) - 3 * m - 4
            flags.append(affine_quotient_excluded(1, k)[0])
        if all(flags):
            all_excluded.append(rm)
        elif any(flags):
            mixed.append(rm)
        else:
            all_survive.append(rm)
    return all_excluded, mixed, all_survive


def main() -> None:
    first = sample_first_family()
    second = sample_second_family()
    print("sample lifts per residue pair:", 16 * 16)
    print("first family: all-excluded residues:", len(first[0]), first[0])
    print("first family: mixed residues:", first[1])
    print("first family: all-survive residues:", first[2])
    print("second family: all-excluded pairs:", len(second[0]), second[0])
    print("second family: mixed pairs:", len(second[1]), second[1])
    print("second family: all-survive pairs:", len(second[2]))
    print("WARNING: these are finite observations, not universal residue theorems.")


if __name__ == "__main__":
    main()
