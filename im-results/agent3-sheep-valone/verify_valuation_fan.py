"""Independent exact test of Sheep one-valuation fan and arbitrary-source lifts.

Uses the authenticated published one-argument map; sources are synthetic.
"""

from random import Random


def section_next(t: int) -> int | None:
    a = (t & -t).bit_length()-1
    u = t >> a
    return None if u == 1 else t+a+(3 if u == 3 else (u-1)//2)


def first_even(t: int) -> int | None:
    z = section_next(t)
    if z is None:
        return None
    m = z-1
    h = (m & -m).bit_length()-1
    return 1+3**h*(m>>h)


def witness(b: int, shift: int=0) -> tuple[int,int,int]:
    if b < 1 or shift < 0:
        raise ValueError("positive valuation, nonnegative shift required")
    q,r=divmod(b,4)
    S=(16**q-1)//5
    assert 5*S+1 == 16**q
    w,c=((3*S,3),(18*S+3,9),(28*S+5,7),(88*S+17,11))[r]
    assert w>=2
    w+=2**(b+1)*shift
    c+=10*shift
    x=2*(2*w+1)
    y=2**b*c
    assert x%4==2 and c%2==1
    return x,y,c


def run() -> None:
    rng=Random(20261103)
    checked=0
    for b in range(1,2001):
        for shift in (0,1,3,rng.randrange(1,1_000_000)):
            x,y,c=witness(b,shift)
            assert section_next(x)==y
            assert first_even(x)==y
            assert (y & -y).bit_length()-1==b
            assert y>x
            checked+=1
    print(f"PASS: {checked} exact constructed first-even edges for every valuation b=1..2000")
    for b in range(1,50):
        x,y,c=witness(b,10**6)
        assert x>10**6 and y%2**b==0 and y%2**(b+1)==2**b
    print("PASS: arbitrarily large source progression for fixed target valuation")


if __name__=="__main__":
    run()
