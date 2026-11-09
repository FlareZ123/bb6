"""Compare the new source-forbidden high parameter lattice with the named
historical modular predicate BB6.Agent3ValSix.highAllowedValSixFull.

This is independent arithmetic regression of the predicate definitions,
not a replacement for the original secNext or its Lean proofs.
"""

def affine_normalize(a: int, k: int) -> tuple[int, int]:
    while k >= 4 and k % 2 == 0 and (a + k) % 4 == 1:
        a, k = a + k - 2, (k - 2) // 2
    return a, k


def previous_high_predicate(j: int, m: int) -> tuple[bool, dict[str, bool]]:
    k = (2 ** (2 * m + 2)) * (j + 3) - (j + 3 * m + 5)
    checks = {
        "joint_h1": not (m >= 2 and j % 4 == 3 and (j + 3*m + 7) % 16 == 0),
        "joint_h2": not (m >= 2 and j % 4 == 1 and (j + 3*m + 11) % 32 == 0),
        "joint_h3": not (m >= 4 and ((m % 4 == 0 and (j + m) % 32 == 26) or
                                  (m % 4 == 1 and (j + m) % 32 == 2))),
        "joint_h4": not (m == 1 and j % 32 == 1),
        "joint_h5": not (m >= 2 and j % 2 == 1 and (j + 3*m + 5) % 8 == 0),
        "rect_m5_j12": not (m % 32 == 5 and j % 32 == 12),
        "dyadic_tower": all(not (n + 4 <= 2*m + 2 and
                                (j + 3*m + 3) % (2 ** (n+4)) == 2 ** (n+2) and
                                (2*j + 3) % 8 == (7 if n % 2 == 0 else 3))
                            for n in range(2*m)),
        "19_odd1": not (m >= 2 and j % 8 == 7 and (j + 3*m + 15) % 64 == 0),
        "19_odd2": not (m >= 2 and j % 8 == 3 and (j + 3*m + 47) % 64 == 0),
        "19_odd3": not (m >= 3 and j % 8 == 5 and (j + 3*m + 27) % 128 == 0),
        "19_odd4": not (m >= 3 and j % 8 == 1 and (j + 3*m + 91) % 128 == 0),
        "29_a": not (m >= 4 and j % 8 == 5 and (j + 31) % 128 == (3*m) % 128),
        "29_b": not (m >= 4 and j % 32 == 17 and (j + 31) % 128 == (3*m) % 128),
        "29_c": not (m >= 4 and j % 64 == 57 and (j + 31) % 128 == (3*m) % 128),
        "29_d": not (m % 32 == 6 and (j + 51) % 256 == (9*m) % 256),
        "val6_a": not (m >= 4 and m % 8 == 4 and (j + 191) % 256 == (3*m) % 256),
        "val6_b": not (m >= 4 and j % 128 == 81 and (j + 63) % 256 == (3*m) % 256),
        "val6_c": not (m >= 4 and j % 32 == 1 and (j + 63) % 256 == (3*m) % 256),
        "11_h1": (j + m) % 4 != 0,
        "11_h2": not (m >= 2 and (j + m) % 16 == 6 and m % 4 != 1),
        "19_five": not (m % 16 == 10 and (j + 3*m + 19) % 64 == 0),
        "final_124": not (j % 32 == 31 and m >= 3 and (j + 3*m) % 128 == 127),
        "final_7": not (j % 8 == 5 and m % 8 == 4 and
                        (9*j + 39) % 128 == (3*m) % 128),
        "final_27": not (m % 32 == 21 and j % 32 == 28),
        "final_affine": affine_normalize(2*j + 3, k)[1] != 4,
    }
    return all(checks.values()), checks


def test() -> None:
    for m in range(7, 135, 8):
        j = (-m - 14) % 128
        accepted, parts = previous_high_predicate(j, m)
        assert accepted, (j, m, [name for name, ok in parts.items() if not ok])
        print(f"PASS m%128={m:3}, j%128={j:3}, {len(parts)} filters")
    accepted, _ = previous_high_predicate(107, 7)
    assert accepted
    k = (2 ** 16) * 110 - 133
    assert k == 7_208_827
    print("Concrete previously admitted high stop: (j,m)=(107,7), target=(217,7208827)")


if __name__ == "__main__":
    test()
