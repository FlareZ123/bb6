"""Cross-check 960 five-step sparse ray cylinders against 620 older gliders."""
from itertools import permutations, product
from census import gliders, Q, TOTAL, ONE_HALT

def five_templates():
    for direction in (0, 1):
        for b, c, d, e in permutations(range(1, 6), 4):
            for x, y in product(range(2), repeat=2):
                table = {
                    (0, 0): (1, direction, b),
                    (b, 0): (1, 1-direction, c),
                    (c, 1): (x, direction, d),
                    (d, 1): (0, 1-direction, e),
                    (e, x): (y, direction, 0),
                }
                assert len(table) == 5
                yield (direction, b, c, d, e, x, y), table

def conflicts(p, q):
    return any(k in q and q[k] != v for k, v in p.items())

def main():
    old = list(gliders())
    new = list(five_templates())
    assert len(old) == 620 and len(new) == 960
    for i, (_, p) in enumerate(new):
        assert p[(0, 0)][0] == 1
        assert p[(p[(0, 0)][2], 0)][1] != p[(0, 0)][1]
        for _, q in new[:i]:
            assert conflicts(p, q)
        for _, q in old:
            assert conflicts(p, q)
    total = len(new) * Q**7
    one = len(new) * 7 * 24**6
    assert total == 5_859_375_000_000
    assert one == 1_284_211_998_720
    print("new cylinders", len(new), "old cylinders", len(old))
    print("new full tables", total, "percent", 100*total/TOTAL)
    print("new exactly-one-halt tables", one, "percent", 100*one/ONE_HALT)
    print("combined gliders full percent", 100*(1_046_752_929_687_500+total)/TOTAL)
    print("combined gliders one-halt percent", 100*(270_785_272_872_960+one)/ONE_HALT)

if __name__ == "__main__":
    main()
