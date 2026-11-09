"""Single runnable regression: real Sheep section F and E for two mixed Hensel examples.

SFT: python test_original_section.py
Uses the literal published t=5 first-return formula and the existing exact
Hensel generator. No numeric tape runtime simulation and no external packages.
"""
from mixed_witness import CASES, lift


def F(x):
    """Authentic section rule for x>=5, returning None at a halting power."""
    assert x >= 5
    a = (x & -x).bit_length()-1
    v = x >> a
    if v == 1:
        return None
    if v == 3:
        return x+a+3
    return x+a+(v-1)//2


def E(x):
    """Authentic first-even section return; log number of F transitions."""
    assert x >= 10 and x % 2 == 0
    cur = x
    count = 0
    while True:
        cur = F(cur)
        assert cur is not None, ("unexpected halt in mixed inverse edge",x)
        count += 1
        if cur % 2 == 0:
            return cur, count
        assert count <= 10, "the selected source should enter an even state"


def parent2(y):
    assert (y+12)%9 == 0
    z = 8*(y+12)//9 - 12
    assert z>=20 and z%8==4
    return z


def test_case(key,depth):
    k,j,_ = lift(key,depth)
    r,shift,b,d,_,_,_ = CASES[key]
    num = (1<<(j+shift))+b
    assert num % d == 0
    tail = num//d
    assert tail >=20 and tail % 2 == 0
    root = 1<<j
    assert E(tail)[0] == root
    print(key,"target exponent j=",j,"k=",k,
          "final F steps=",E(tail)[1],"tail bit length=",tail.bit_length())
    node = tail
    for i in range(depth):
        prev = parent2(node)
        got, count = E(prev)
        assert got == node and count == 1
        print("  genuine parent step",i+1,"parent bit length=",prev.bit_length())
        node = prev


def main():
    for key in ("Z29", "X8"):
        test_case(key,2)
    print("PASS: actual Sheep F/E source formula and all mixed inverse edges")


if __name__ == "__main__":
    main()
