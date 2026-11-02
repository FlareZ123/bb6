"""Exact witnesses for a uniform all-exponent Sheep exceptional-parent cutoff.

The mathematical argument and its non-computational induction are in
EXCEPTIONAL-TAIL.md. All checks here use exact unbounded Python integers.
"""
from random import Random


def exceptional_cutoff(c: int, s: int, b: int, d: int) -> tuple[int, int]:
    assert c > 0 and s >= 0 and d > 0
    C = c << s
    D = 3*d
    B = 1
    while not (D*(1 << B) > C+abs(b) and C*(1 << B) > D):
        B += 1
    J = 2*B + abs(b) + 4
    while (1 << (J-B)) <= d*(J+B+3) + abs(b):
        J += 1
    assert J >= B
    return B, J


def check_cutoff(c: int, s: int, b: int, d: int) -> int:
    B, J = exceptional_cutoff(c,s,b,d)
    C, D = c << s, 3*d
    assert (1 << B)*D > C+abs(b)
    assert (1 << B)*C > D
    assert J >= 2*B+abs(b)+4
    assert (1 << (J-B)) > d*(J+B+3)+abs(b)
    edges = 0
    for j in (J, J+1, J+13):
        assert (1 << (j-B)) > d*(j+B+3)+abs(b)
        target = C*(1 << j)+b
        for a in range(j+B+3):
            result = D*(1 << a)+d*(a+3)
            assert result != target, (c,s,b,d,B,J,j,a)
            edges += 1
    return edges


def main() -> None:
    cases=0; edges=0
    for c in range(1,26):
        for s in (0,1,3,5):
            for d in (1,2,3,5,11):
                for b in (-25,-7,0,1,9,32):
                    edges += check_cutoff(c,s,b,d)
                    cases += 1
    rng=Random(61172026)
    for _ in range(1000):
        c=rng.randint(1,90)
        s=rng.randint(0,15)
        d=rng.randint(1,35)
        b=rng.randint(-150,150)
        edges += check_cutoff(c,s,b,d)
        cases+=1
    print(f"PASS: {cases} signed coefficient families; {edges} exact exceptional-branch inequalities")
    for t in ((1,0,0,1),(3,0,0,1),(3,0,-500,1),(1,7,21,3)):
        print(t, exceptional_cutoff(*t))


if __name__=='__main__':
    main()
