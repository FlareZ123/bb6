"""Five-phase strengthening of the 17-layer Sheep 3-adic root certificate.

Run in the same directory as stratum_certificate.py. Uses exact complete
period tests there; proves that every remaining row has period 1 or 5 in k.
"""
from fractions import Fraction
from stratum_certificate import SCALE, MAX_STRATUM, certify_stratum


def layer(s):
    rows, zero, active = certify_stratum(s)
    table = {(h, a): (modulus, residue, q)
             for h, a, modulus, residue, q in rows}
    assert all(table[p][2] in (1, 5) for pairs in active.values() for p in pairs)
    free = []
    for r in range(1, 64):
        if r % 3 == 0:
            continue
        for phase in range(5):
            if r in zero:
                free.append((r, phase))
                continue
            j = SCALE * 3 ** s * (r + 63 * phase)
            if all(pow(2, j + h + 1, table[(h, a)][0])
                   != table[(h, a)][1] for h, a in active[r]):
                free.append((r, phase))
    return free


def main():
    counts = []
    for s in range(MAX_STRATUM + 1):
        result = layer(s)
        counts.append(len(result))
        print(f"s={s:2d}, predecessor-free n=3^{s}*(r+63*(phase+5*k)): "
              f"{len(result)}/210 residue-phase pairs")
    assert counts == [150, 150, 132, 150, 150, 150, 132, 132,
                      150, 132, 125, 125, 110, 100, 100, 100, 88]
    density = sum((Fraction(v, 315 * 3 ** s)
                   for s, v in enumerate(counts)), Fraction())
    assert density == Fraction(9597932614, 13559717115)
    print(f"PROVED lower density: {density} = {float(density):.11%}")
    print("The omitted higher valuations have natural density", Fraction(1, 3**17))


if __name__ == "__main__":
    main()
