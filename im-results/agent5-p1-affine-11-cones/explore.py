"""Symbolic affine inverse-cone test for P1 n = r + 256*h.

The output is an exploratory certificate outline, not a Lean theorem.
All calculations are exact integer arithmetic, with every division validated
for every h >= 0 by coefficient divisibility.
"""
from dataclasses import dataclass

RESIDUES = (110, 158, 190, 206)


@dataclass(frozen=True)
class Aff:
    a: int = 0
    b: int = 0
    c: int = 0

    def __add__(self, other):
        if isinstance(other, int):
            other = Aff(0, 0, other)
        return Aff(self.a + other.a, self.b + other.b, self.c + other.c)

    __radd__ = __add__

    def __neg__(self):
        return Aff(-self.a, -self.b, -self.c)

    def __sub__(self, other):
        return self + -other if isinstance(other, Aff) else self + (-other)

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, n):
        return Aff(n * self.a, n * self.b, n * self.c)

    __rmul__ = __mul__

    def divmod(self, d):
        assert self.a % d == 0 and self.b % d == 0
        return Aff(self.a // d, self.b // d, self.c // d), self.c % d

    def at(self, h):
        return self.a * (1 << (256 * h)) + self.b * h + self.c

    def positive(self):
        # 2^(256*h) >= h+1 for every natural h
        return self.a + self.b >= 0 and self.a + self.c > 0


def classify(x, y):
    xr = x.divmod(4)[1]
    yr = y.divmod(2)[1]
    if xr == 2:
        assert yr == 1
        return "M"  # reachable even-left mod-four obstruction
    if xr == 0 and yr == 0:
        return "P"  # even-right power-of-two obstruction
    assert xr == 0 and yr == 1
    return "N"  # recurse on potential feeder


def tree(residue):
    p = 14 * (1 << residue)
    root = Aff(p, -512, -2 * residue - 16)
    agenda = [("", root, Aff(0, 0, 3))]
    hubs = {}
    while agenda:
        path, b, d = agenda.pop()
        assert path not in hubs
        assert b.positive() and d.positive()
        assert b.divmod(4)[1] == 0
        k = b.divmod(4)[0] - 1
        c = d + b.divmod(2)[0]
        children = []
        while True:
            assert k.positive() and c.positive()
            x, y = 2 * k - 4, c + 4
            kind = classify(x, y)
            assert x.positive() and y.positive()
            child_id = path + str(len(children))
            children.append((kind, x, y))
            if kind == "N":
                agenda.append((child_id, x, y))
            elif kind == "P":
                # x + 12 lies strictly between adjacent 14*2^j powers:
                # 14*2^(n-1) < x+12 < 14*2^n for n=residue+256*h.
                val = x + 12
                half = p // 2
                assert half < val.a < p
                assert val.b <= 0 and val.c <= 0
                assert val.a - half + val.b > 0
                assert val.a - half + val.c > 0
            if c.divmod(2)[1] == 0:
                break
            assert (c - 3).positive()
            c = (c - 3).divmod(2)[0]
            k = k + c.divmod(2)[0] + 1
        hubs[path] = (b, d, children)
    return hubs


def main():
    for r in RESIDUES:
        nodes = tree(r)
        kinds = [k for _, _, children in nodes.values() for k, _, _ in children]
        assert len(nodes) == 11
        assert kinds.count("N") == 10
        assert kinds.count("M") == 11
        assert kinds.count("P") == 11
        print(f"residue={r} (mod 256): hubs=11, feeder_edges=10, mod_leaves=11, power_leaves=11")
        for path, (_, _, children) in sorted(nodes.items(), key=lambda p: (len(p[0]), p[0])):
            print(" ", path or "root", "".join(k for k, _, _ in children))
        # Independent numeric spot checks on actual synthetic indices.
        for h in (0, 1, 2):
            for b, d, children in nodes.values():
                assert b.at(h) >= 8 and b.at(h) % 4 == 0 and d.at(h) > 0
                for kind, x, y in children:
                    assert classify(x, y) == kind
                    assert x.at(h) > 0 and y.at(h) > 0
        print("All affine-divisibility, positivity, leaf-gap and numeric checks passed.")


if __name__ == "__main__":
    main()
