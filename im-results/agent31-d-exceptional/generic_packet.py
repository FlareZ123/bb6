"""Arbitrary-tail original raw-machine checks of universal B/E marker transducers.

Source macros are previously universally Lean-verified; this independently
checks exact physical F0 times and complete tapes in a bounded sample.
"""
from __future__ import annotations
import random
from check_second_escape import one, pairs, physical_return


def canonical(bits: list[int]) -> list[int]:
    while bits and bits[-1] == 0:
        bits.pop()
    return bits


def check(seed: int = 130057) -> None:
    rng = random.Random(seed)
    checks = 0
    for k in range(9):
        for q in range(10):
            for p in range(10):
                y = [rng.getrandbits(1) for _ in range(rng.randrange(13))]
                if q >= 1:
                    n = 3*k+2
                    t = 12*k*k+49*k+40
                    inp = one(n)+pairs(q)+[0]+one(p)+y
                    out = one(8*k+10)+pairs(q-1)+[0]+one(p)+y
                    elapsed, got = physical_return(inp, max_steps=100000)
                    assert (elapsed, got) == (t, canonical(out)), ('B',k,q,p,y)
                    checks += 1
                if p >= 3:
                    n = 3*k+4
                    t = 12*k*k+49*k+58+6*q
                    inp = one(n)+pairs(q)+[0]+one(p)+y
                    out = one(8*k+9)+pairs(q+2)+[0]+one(p-3)+y
                    elapsed, got = physical_return(inp, max_steps=100000)
                    assert (elapsed, got) == (t, canonical(out)), ('E',k,q,p,y)
                    checks += 1
    print(f'PASS {checks} exact arbitrary-binary-tail B/E steps, RNG seed {seed}')


if __name__ == '__main__':
    check()
