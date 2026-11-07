"""Check the uniform bounded (a,h) representatives of mixed Sheep edges.

Each sampled real generic quotient edge is normalized by periodicity of
a modulo q*ord_q(2), and h modulo ord_(q/3^e)(3/2) after 3-adic
preperiod e. Check both exact dyadic inverse and odd-q output equations.
This is finite evidence for the paper proof in MIXED-FINITE-PATH-LIFTING.
"""
from math import gcd
from verify_mixed_paths import sampled_edges, inverse_parent


def multiplicative_order(base: int, modulus: int) -> int:
    if modulus == 1:
        return 1
    assert gcd(base,modulus)==1
    x = 1
    for n in range(1,modulus*modulus+1):
        x = x*base%modulus
        if x==1:
            return n
    raise AssertionError((base,modulus))


def odd_return(a: int, h: int, rq: int, q: int) -> int:
    if q==1:
        return 0
    inv2 = pow(2,-1,q)
    first = ((2+pow(2,-a,q))*rq+2*a-1)*inv2%q
    t = 3*inv2%q
    return (1+pow(t,h,q)*(first-1))%q


def bounded_letter(p: int,q: int,a: int,h: int) -> tuple[int,int,int]:
    e = 0
    r = q
    while r%3==0:
        r//=3
        e+=1
    d = multiplicative_order((3*pow(2,-1,r))%r,r) if r>1 else 1
    D = q*multiplicative_order(2%q,q) if q>1 else 1
    if a>=p:
        a=p+(a-p)%D
    L=max(0,p-a-1)
    if h>=max(e,L):
        h=max(e,L)+(h-max(e,L))%d
    bound=p+D+e+d-1
    assert a+h+1<=bound,(p,q,a,h,bound)
    return a,h,bound


def check() -> None:
    total = 0
    for p in range(1,7):
        for q in (1,3,5,7,9,11,15,21,25,35):
            graph = sampled_edges(p,q)
            count = 0
            for source,targets in graph.items():
                for target,(a,h) in targets.items():
                    aa,hh,_ = bounded_letter(p,q,a,h)
                    precision=p+aa+hh+2
                    dyadic_parent = inverse_parent(
                        precision,aa,hh,target%(1 << p)
                    )
                    assert dyadic_parent%(1 << p)==source%(1 << p)
                    assert odd_return(aa,hh,source%q,q)==target%q
                    count+=1
            total+=count
            print(f"PASS p={p}, q={q}: {count} bounded edge labels",flush=True)
    assert total==123986,total
    print(f"PASS {total} mixed edge normal-form checks",flush=True)


if __name__=="__main__":
    check()
