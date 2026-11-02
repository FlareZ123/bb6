"""Reproducible census of twenty sparse three-slot nonhalting cylinders."""
from itertools import product
from census import Q, TOTAL, ONE_HALT, gliders
from five_census import conflicts, five_templates

def bootstraps():
    for d, b, y in product((0, 1), range(1, 6), (0, 1)):
        p = {(0, 0): (1, d, b), (b, 0): (0, 1-d, 0), (0, 1): (y, 1-d, b)}
        assert len(p) == 3
        yield (d, b, y), p

def main():
    old = list(gliders())
    five = list(five_templates())
    new = list(bootstraps())
    assert len(old) == 620 and len(five) == 960 and len(new) == 20
    for i, (name, p) in enumerate(new):
        assert all(conflicts(p, q) for _, q in new[:i]), name
        assert all(conflicts(p, q) for _, q in old), name
        assert all(conflicts(p, q) for _, q in five), name
    count = len(new) * Q**9
    one = len(new) * 9 * 24**8
    assert count == 76293945312500
    assert one == 19813556551680
    prev = 1046752929687500 + 960 * Q**7
    prev_one = 270785272872960 + 960 * 7 * 24**6
    print("new three-slot cylinders", len(new), "no overlaps with 1580 prior")
    print("additional full", count, "percent", 100*count/TOTAL)
    print("additional one-halt", one, "percent", 100*one/ONE_HALT)
    print("combined full percent", 100*(prev+count)/TOTAL)
    print("combined one-halt percent", 100*(prev_one+one)/ONE_HALT)

if __name__ == "__main__":
    main()
