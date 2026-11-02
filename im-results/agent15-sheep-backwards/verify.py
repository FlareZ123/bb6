"""Finite exact-arithmetic cross-check of the two analytic inverse theorems."""
def valuations(y):
    found = set()
    for a in range(y.bit_length()):
        if y == 3 * (1 << a) + a + 3:
            found.add(("special", a))
        d = (1 << (a + 1)) + 1
        z = 2 * y - 2 * a + 1
        if z >= 5 * d and z % d == 0 and (z // d) % 2:
            found.add(("normal", a))
    return found

def verify(bound=1000):
    count = 0
    for b in range(4, bound + 1, 2):
        p = ((1 << (b + 1)) + 1) // 3
        aa = set()
        if b >= 6:
            for a, good in [(0, b % 6 == 0), (1, b % 4 == 2),
                            (2, b % 18 == 14), (3, b % 8 == 4)]:
                if good:
                    aa.add(("normal", a))
        assert valuations(p) == aa, ("P", b)
        count += 1
    for b in range(7, bound + 1, 4):
        q = 2 * ((1 << (b + 1)) - 1) // 5
        aa = set()
        for a, good in [(1, b >= 11 and b % 20 == 11),
                        (2, b >= 15 and b % 12 == 3),
                        (5, b >= 67 and b % 60 == 7)]:
            if good:
                aa.add(("normal", a))
        assert valuations(q) == aa, ("Q", b)
        count += 1
    print("PASS:", count, "target exponents through", bound)

if __name__ == "__main__":
    verify()
