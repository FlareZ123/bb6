"""Deterministic exact tests for Sheep's generic first-even-return mixed residue graph.

Each graph edge has a separate legal positive integer witness. These checks
make no claim about the actual blank-tape orbit or BB(6).
"""
from collections import deque
from math import gcd


def v2(n: int) -> int:
    assert n > 0
    return (n & -n).bit_length() - 1


def first_even(x: int) -> int:
    a = v2(x)
    u = x >> a
    assert a >= 1 and u >= 5 and u & 1
    f = x + a + (u-1)//2
    h = v2(f-1)
    assert h >= 0
    return 1 + 3**h * ((f-1) >> h)


def factors(q: int) -> list[tuple[int,int]]:
    assert q >= 1 and q & 1
    result = []
    n, ell = q, 3
    while ell*ell <= n:
        if n % ell == 0:
            k = 0
            while n % ell == 0:
                n //= ell
                k += 1
            result.append((ell,k))
        ell += 2
    if n > 1:
        result.append((n,1))
    return result


def euler_phi(q: int) -> int:
    result = q
    for ell, _ in factors(q):
        result = result // ell * (ell-1)
    return result


def odd_target(a: int, r: int, q: int) -> int:
    if q == 1:
        return 0
    return (r+a+(r*pow(2,-a,q)-1)*pow(2,-1,q)) % q


def choose_exponent(q: int, r: int, s: int, p: int) -> int:
    """Construct a >= p with odd_target(a,r,q) == s by ascending prime lift."""
    a, Q = 0, 1
    for ell, k in factors(q):
        B = Q * euler_phi(Q) * (ell-1)
        assert gcd(B,ell)==1 and pow(2,B,ell)==1
        t = 0
        for j in range(k):
            power = ell**j
            choices = [d for d in range(ell)
                       if odd_target(a+B*(t+power*d),r,ell**(j+1)) == s % ell**(j+1)]
            assert len(choices) == 1, (q,r,s,ell,k,j,choices)
            t += power*choices[0]
        a += B*t
        Q *= ell**k
        assert odd_target(a,r,Q)==s%Q
    period = q*euler_phi(q)
    if a < p:
        a += ((p-a+period-1)//period)*period
    assert a >= p and odd_target(a,r,q)==s%q
    return a


def zero_to_any(p: int, q: int, rq: int, s2: int, sq: int) -> tuple[int,int]:
    assert p>=1 and q>=1 and q&1 and not (s2&1)
    a = choose_exponent(q,rq,sq,p)
    mod2 = 1 << (p+1)
    u2 = (2*s2-2*a+1) % mod2
    uq = rq*pow(2,-a,q)%q if q>1 else 0
    t = (uq-u2)*pow(mod2,-1,q)%q if q>1 else 0
    u = u2+mod2*t
    if u < 5:
        u += ((5-u+mod2*q-1)//(mod2*q))*mod2*q
    x = (1<<a)*u
    f = x + a + (u-1)//2
    z = first_even(x)
    assert f == z and x%(1<<p)==0 and x%q==rq
    assert z%(1<<p)==s2 and z%q==sq
    return x,z


def dyadic_parent(p: int, a: int, h: int, s2: int) -> int:
    m = 1<<(p-a)
    D = 1+(1<<(a+1))
    u = ((3-2*a+(1<<(h+1))*pow(3**h,-1,m)*(s2-1))*pow(D,-1,m))%m
    return (1<<a)*u


def reverse_path(p: int) -> dict[int,tuple[int,int,int]]:
    history={0:(0,0,0)}
    todo=deque([0])
    while todo:
        target=todo.popleft()
        for a in range(1,p):
            for h in range(p-a):
                parent=dyadic_parent(p,a,h,target)
                if parent not in history:
                    history[parent]=(target,a,h)
                    todo.append(parent)
    assert len(history)==(1<<(p-1))
    return history


def prescribed_source_edge(p: int, q: int, a: int, h: int, s2: int, rq: int) -> tuple[int,int]:
    """Lift dyadic inverse edge to arbitrary source rq modq using CRT."""
    m=1<<p
    D=1+(1<<(a+1))
    v2res=(s2-1)*pow(3**h,-1,m)%m
    vd=(2*a-3)*pow(1<<(h+1),-1,D)%D
    v=v2res + m*((vd-v2res)*pow(m,-1,D)%D)
    u=(3-2*a+(1<<(h+1))*v)//D
    x=(1<<a)*u
    jump=1<<(p+a+h+1)
    t=(rq-x)*pow(jump,-1,q)%q if q>1 else 0
    v += m*D*t
    u=(3-2*a+(1<<(h+1))*v)//D
    if u<5 or v<5:
        inc=m*D*q
        reps=max((5-v+inc-1)//inc,(5-u+(1<<(p+h+1))*q-1)//((1<<(p+h+1))*q),0)
        v+=inc*reps
        u=(3-2*a+(1<<(h+1))*v)//D
    x=(1<<a)*u
    z=first_even(x)
    assert u>=5 and v>=5 and z==1+3**h*v
    assert x%m==dyadic_parent(p,a,h,s2) and x%q==rq and z%m==s2
    return x,z


def verify() -> None:
    total_lift, total_zero = 0, 0
    for p in range(1,7):
        m=1<<p
        paths=reverse_path(p)
        for q in [1,3,5,7,9,11,13,15,21,25,27,33,35,45,49,55,63,65,75,81,99,105]:
            for r2 in range(0,m,2):
                for rq in range(q):
                    current2,currentq=r2,rq
                    while current2:
                        dest,a,h=paths[current2]
                        x,z=prescribed_source_edge(p,q,a,h,dest,currentq)
                        current2,currentq=dest,z%q
                        total_lift+=1
                    for s2,sq in [(0,0),(m-2,q-1),(m-2,(q//2))]:
                        x,z=zero_to_any(p,q,currentq,s2,sq)
                        total_zero+=1
            print(f'PASS p={p}, q={q}, {m*q//2} mixed sources',flush=True)
    print(f'PASS {total_lift} exact CRT-lifted edges, {total_zero} exact mixed-zero-layer outgoing edges')


if __name__ == '__main__':
    verify()
