"""No-SymPy all-exponent inverse-tree certificate for six new Sheep classes.

Source-model assumptions: published F(2^a*u), its special u=3 branch,
generic u>=5 branch; section starts at 5 and strictly increases.
All checks use exact Python integers.
"""
from dataclasses import dataclass

MOD = 2700
RESIDUES = (426, 2046, 2586)
START = 426


@dataclass(frozen=True)
class Family:
    shift: int
    bias: int
    denominator: int

    def parent(self, a: int):
        p = 1 << a
        return Family(
            self.shift + a + 1,
            2*p*self.bias + p*self.denominator*(1-2*a),
            self.denominator*(2*p+1),
        )


FAMILIES = (
    Family(0, 0, 1),
    Family(1, 1, 3),
    Family(2, 5, 9),
    Family(3, -2, 15),
    Family(4, 11, 45),
    Family(5, 67, 135),
    Family(6, -46, 225),
    Family(7, 133, 675),
)
TAILS = (2, 5, 7, 8, 10, 12, 13, 15)
PERIODS = (
    (1, 1),
    (1, 1, 1, 2, 1),
    (1, 1, 1, 2, 1, 1, 7),
    (1, 1, 1, 2, 1, 1, 7, 4),
    (1, 1, 1, 2, 1, 1, 7, 4, 3, 1),
    (1, 1, 3, 2, 1, 1, 7, 4, 9, 1, 11, 2),
    (1, 1, 1, 2, 1, 1, 7, 4, 3, 5, 11, 2, 13),
    (1, 1, 3, 2, 1, 1, 7, 4, 9, 5, 11, 2, 13, 7, 3),
)
CHILDREN = (
    {0: 1},
    {0: 2, 1: 3},
    {},
    {0: 4},
    {0: 5, 1: 6},
    {},
    {0: 7},
    {},
)


def verify() -> None:
    assert len(FAMILIES) == len(TAILS) == len(PERIODS) == len(CHILDREN) == 8
    periods_checked = 0
    excluded_cases = 0

    for i, (f, tail, qs, children) in enumerate(zip(FAMILIES, TAILS, PERIODS, CHILDREN)):
        d, s, b = f.denominator, f.shift, f.bias
        assert d > 0 and d % 2 == 1 and s >= 0 and len(qs) == tail
        h = (3*d).bit_length()-1-s
        assert h >= 0 and h+1 <= START
        lo = 3*d-(1 << (s+h))
        hi = (1 << (s+h+1))-3*d
        assert lo > 0 and hi > 0
        assert lo*(1 << START) > (1 << h)*b
        assert hi*(1 << START) > (1 << (h+1))*(d*(START+3)-b)
        assert hi*(1 << START) > (1 << (h+1))*d
        assert (1 << (START+s))+b > 5*d

        K = d*(2*tail-1)-2*b
        assert K % 2 == 1 and 1 < K < (1 << tail)
        assert (1 << tail) >= 2*d

        # The tail inequalities persist for all a>=tail by induction.
        for a, q in enumerate(qs):
            m = d*((1 << (a+1))+1)
            assert q > 0 and m % 2 == 1
            assert pow(2, MOD*q, m) == 1, (i, a, "period")
            periods_checked += 1
            target = (d*(2*a-1)-2*b) % m
            for r in RESIDUES:
                found = any(pow(2, r+s+1+MOD*j, m) == target for j in range(q))
                assert found == (a in children), (i, a, r, found, children)
                excluded_cases += not found

        for a, child_idx in children.items():
            assert f.parent(a) == FAMILIES[child_idx], (i, a, child_idx)
        print(f"node {i} {f}: valuations<{tail}, allowed {tuple(children)}, special bound ok")

    assert all(not CHILDREN[k] for k in (2, 5, 7))
    print(f"PASS: {len(RESIDUES)} infinite index progressions mod {MOD}")
    print(f"PASS: {periods_checked} checked complete modular periods and "
          f"{excluded_cases} all-index valuation exclusions")
    print("PASS: exact 8-node backward tree terminates at 3 no-parent leaves")
    print("Uniformity follows from checked periods, 2^a residue gap, and "
          "exponential-over-linear exceptional inequalities.")


if __name__ == "__main__":
    verify()
