"""A 703-carry finite-state attractor for the tenth S4 prefix digit.

Pure exact-integer evaluation of the total hp/gp/pp prefix projection.  The
underlying all-depth source correspondence is proved separately in the S4
prefix-causality dossier.  This checker does not certify S4 nonhalting.
"""
from ninth_digit_candidate import gp
from ninth_gate_census import CYCLE_NINE, OFFSETS, PERIOD, weight

def carry_at_tenth(c: int, p: tuple[int, ...]) -> tuple[bool, int]:
    """Exact action on the appended tenth digit: addition or half-drain."""
    assert len(p) == 9
    a = p[0] + c
    for i in range(9):
        if a % 2 == 0:
            return (False, a // 2 if i == 8 else 0)
        if i < 8:
            a = p[i + 1] + a // 2 + 1
    return (True, a // 2 + 1)

def half(z: int) -> int:
    return z // 2 + 2 if z % 2 == 0 else z // 2

def apply_stage(v: int, stage: tuple[bool, int]) -> int:
    divide, d = stage
    return half(v + d) if divide else v + d

def transition_list() -> tuple[tuple[tuple[bool, int], ...], int, int, int]:
    p = CYCLE_NINE
    trans: list[tuple[bool, int]] = []
    lo = hi = n_halves = 0
    for t in range(PERIOD):
        for c in OFFSETS:
            stage = carry_at_tenth(c, p)
            divide, d = stage
            # The all-odd scan is precisely the mod-512 power-gate candidate.
            assert divide == ((weight(p) + c) % 512 == 0)
            if divide:
                lo = (lo + d) // 2
                hi = (hi + d + 1) // 2 + 2
                n_halves += 1
            else:
                lo += d
                hi += d
            if divide or (t % 10007 == 0):
                q = gp(c, p)
                for v in (0, 1, 366446):
                    actual = gp(c, p + (v,))
                    assert actual[:9] == q
                    assert actual[9] == apply_stage(v, stage)
            trans.append(stage)
            p = gp(c, p)
    assert p == CYCLE_NINE
    assert len(trans) == 3 * PERIOD
    assert (n_halves, lo, hi) == (703, 366445, 366450)
    return tuple(trans), n_halves, lo, hi

def evaluate(v: int, trans: tuple[tuple[bool, int], ...]) -> int:
    for stage in trans:
        v = apply_stage(v, stage)
    return v

def main() -> None:
    trans, r, lo, hi = transition_list()
    B = 1 << r
    for v in (0, 1, 2, 3, 5, 100, 366446, 10**50, 1 << 800):
        y = evaluate(v, trans)
        assert v // B + lo <= y <= v // B + hi
    table = {v: evaluate(v, trans) for v in range(366445, 366451)}
    assert table == {
        366445: 366447, 366446: 366449, 366447: 366446,
        366448: 366448, 366449: 366445, 366450: 366447,
    }
    print("Total nine-prefix cycle:", PERIOD, "reduced returns")
    print("One-block tenth-digit half-drains:", r)
    print("Rigorous envelope: floor(v/2^703) +", lo, "<= F(v) <= floor(v/2^703) +", hi)
    print("Small trapping interval transitions:", table)
    print("Global eventual attractor: fixed 366448 or 4-cycle 366445->366447->366446->366449->366445")
    print("Authentic return-5457 tenth digit 366446 lies on the four-cycle.")
    print("All assertions concern total prefixes; physical-root conclusions require survival.")

if __name__ == "__main__":
    main()
