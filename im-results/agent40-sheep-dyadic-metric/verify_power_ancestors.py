"""Exact all-depth generic inverse chains from powers of two.

For L>=1, j=6*5^(L-1)+1 satisfies 5^L | 2^j+2.
The repeated affine inverse x <- (4*y-2)/5 constructs L actual
generic Sheep even-return parents of the exact target 2^j.
The all-L proof is in NO-BOUNDED-HISTORY-INVARIANT.md.
Finite independent check: L=1,...,8.
"""


def check() -> None:
    for depth in range(1,9):
        j = 6*5**(depth-1)+1
        power = 1 << j
        assert (power+2) % (5**depth)==0
        y = power
        for k in range(1,depth+1):
            assert (4*y-2)%5==0,(depth,j,k)
            x = (4*y-2)//5
            assert x>=10 and x%4==2,(depth,j,k,x%4)
            a = 1
            u = x//2
            assert u>=5 and u%2==1
            f = x+a+(u-1)//2
            assert f==y and f%2==0
            h = 0
            v = f-1
            assert v>=5 and v%2==1
            e = 1+3**h*v
            assert e==y
            y=x
        print(f"PASS depth={depth}: power exponent {j}, "
              f"ancestor bit length {y.bit_length()}",flush=True)
    print("PASS all selected L<=8 literal generic predecessor chains",flush=True)


if __name__=="__main__":
    check()
