"""Exact-integer dyadic shadow census for the P1 n=16q+2 feeder roots.

The README gives the correspondence derivation and verification limits.
Original Lean-source transport is a separate proof obligation.
"""
import sys


def shadow(q: int, root: int) -> dict:
    assert q >= 3 and root in (0, 1)
    n = 16*q
    L = n + 8 + root
    z0 = (12 if root == 0 else 10)*q + 4
    pending = [(0, z0)]
    seen = {(0, z0)}
    edges = maximum_m = maximum_v = maximum_w = maximum_even_cost = 0
    while pending:
        m, z = pending.pop()
        w = L + m - z
        assert z > 0 and w >= 4
        v = (z & -z).bit_length()-1
        maximum_m = max(maximum_m, m)
        maximum_v = max(maximum_v, v)
        maximum_w = max(maximum_w, w)
        maximum_even_cost = max(maximum_even_cost, m+v+2)
        for t in range(v+1):
            numerator = L+m+t-1+(z >> t)
            if numerator % 2:
                continue
            child = (m+t+1, numerator//2)
            edges += 1
            if child not in seen:
                seen.add(child)
                pending.append(child)
    # Sufficient source safety conditions, see README correspondence proof.
    assert edges == len(seen)-1
    assert maximum_m+maximum_v+3 <= n
    assert (1 << (n-maximum_m)) >= 4*(L+maximum_m)+16
    assert 28*(1 << n) > 2*(L+maximum_m)+6*(1 << maximum_v)
    assert maximum_even_cost <= 15*q
    return dict(q=q, root=root, nodes=len(seen), edges=edges,
                maximum_m=maximum_m, maximum_v=maximum_v,
                maximum_w=maximum_w, maximum_even_cost=maximum_even_cost)


def direct(q: int, root: int) -> dict:
    """Independently exhaust the original b,d inverseAt recursion."""
    assert q >= 1 and root in (0, 1)
    p = 1 << (16*q)
    u = 7*p-4*q-3
    b0,d0 = ((4*u-4,4*u+9) if root == 0 else (6*u-2,2*u+5))
    pending = [(b0,d0,0)]
    seen = {(b0,d0)}
    edges = max_even = 0
    while pending:
        b,d,m = pending.pop()
        assert b >= 8 and b%4 == 0 and d%2 == 1
        assert b+d+2*m == b0+d0
        k,c,t = b//4-1,d+b//2,0
        while True:
            assert k >= 2 and c >= 3
            x,y = 2*k-4,c+4
            if c%2 == 0:
                max_even = max(max_even,m+t+1)
                break
            if x >= 8 and x%4 == 0:
                assert y%2 == 1
                assert x+y+2*(m+t+1) == b0+d0
                assert (x,y) not in seen
                edges += 1
                seen.add((x,y))
                pending.append((x,y,m+t+1))
            else:
                assert x%4 == 2 and x>2
            v = (c-3)//2
            k,c,t = k+v//2+1,v,t+1
    assert edges == len(seen)-1 and max_even <= 15*q
    return dict(q=q, root=root, nodes=len(seen),
                edges=edges, maximum_even_cost=max_even)


def main() -> None:
    qs = [int(a) for a in sys.argv[1:]] if len(sys.argv)>1 else range(1,1501)
    total = 0
    for q in qs:
        for root in (0,1):
            result = direct(q,root) if q<3 else shadow(q,root)
            if q in (1,2,38,101,294,498,633,774):
                print(result,flush=True)
            total += result["nodes"]
            if q in (38,101,294):
                independent = direct(q,root)
                assert independent["nodes"] == result["nodes"]
                assert independent["maximum_even_cost"] == result["maximum_even_cost"]
    print("CENSUS COMPLETE: feeders=",2*len(qs),"nodes=",total,flush=True)


if __name__ == "__main__":
    main()
