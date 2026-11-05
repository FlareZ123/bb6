"""Exact arithmetic audit for odd-parameter Machine C high-stopping tower claims.

This executable checks finitely many integer instances of the formulas
in AllOddMConstruction.md. It is not a proof of any universal statement.
The source-faithful Lean section transition and stopping criterion remain
in the repository's existing CSectionTotal / SectionParam files.
"""

def family(m: int, sector: str, q: int, n: int) -> dict:
    assert m >= 3 and m % 2 == 1
    assert sector in ("A", "B") and q >= 0 and n >= 0
    h = 1 << (2*m+2)
    c = h-1
    offset = 3*(h-m-1)
    d_a = ((m-1)//2) % 4
    d = d_a if sector == "A" else (d_a+2) % 4
    residue = 16 if sector == "A" else 0
    period = 1 << (d+5)
    initial = (-(3*(m+1)+(1 << d)*(residue+2))) % period
    j = period*q+initial
    for _ in range(n):
        j = h*j+offset

    a, k = 2*j+3, c*j+offset-2
    x, y, depth = a, k, 0
    while y >= 4 and y%2 == 0 and (x+y)%4 == 1:
        x, y = x+y-2, (y-2)//2
        depth += 1

    return {
        "m":m, "sector":sector, "q":q, "n":n, "j0":initial,
        "a":a, "k":k, "depth":depth, "normalizer":(x,y),
        "halt_parameter_equation":k+j+3*m+5 == h*(j+3),
        "exact_depth":depth == d+(2*m+2)*n,
        "normalized_cone":(
            x%16 == (3 if sector == "A" else 11)
            and y%32 == residue and y >= 32
        )
    }

def main() -> None:
    count = 0
    for m in range(3,102,2):
        for sector in ("A","B"):
            for q in (0,1,2):
                for n in (0,1,2):
                    v = family(m,sector,q,n)
                    assert v["halt_parameter_equation"],v
                    assert v["exact_depth"],v
                    assert v["normalized_cone"],v
                    count += 1
    for m in (3,5,7,9,11):
        for sector in ("A","B"):
            v = family(m,sector,0,0)
            print(f"m={m:2d} cone={sector} j0={v['j0']:3d} "
                  f"depth={v['depth']:3d} right={v['normalizer'][1]}")
    print(f"All {count} finite exact-arithmetic checks passed.")

if __name__ == "__main__":
    main()
