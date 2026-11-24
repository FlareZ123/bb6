"""Independent exact-integer two-row crossing search; no external packages.
Usage: python barrier_chain.py [last_scale]; default checks 5..30.
Return a concrete witness if an enumerated strict crossing exists.
"""
import sys

DIGITS = (0, 1, 4, 5)
COST = dict(zip(DIGITS, (3, 5, 4, 6)))
OFFSET = dict(zip(DIGITS, (0, 6, 18, 32)))
COEFFS = (4, 7, 13, 23, 41)


def next_row(a, q, e):
    for d in DIGITS:
        for r in DIGITS:
            n = e + a*r + d*q + OFFSET[d]
            if n % 16 == 0:
                yield r, d, q+COST[d], n//16


def crossing(a, b, k):
    M = 16**k
    for e0 in range((a+b)//3+1):
        states = {(b,e0)}
        for _ in range(k):
            states = {(Q,F) for q,e in states
                      for _,_,Q,F in next_row(a,q,e)}
        for q1,e1 in states:
            def dfs(i,q,e,Q,f,w,v,z):
                if i == k:
                    if (q,e) != (q1,e1):
                        return None
                    l = sum(COST[r] for r in w)
                    rem = l
                    B = 0
                    power = 1
                    for r in w:
                        B += (b*r+OFFSET[r]-r*rem)*power
                        power *= 16
                        rem -= COST[r]
                    y = M*e0-B
                    p = a*M+b-l
                    if 0 < 3*y < p:
                        return (e0,q1,e1,w,v,z,y,p)
                    return None
                if not q+3*(k-i) <= q1 <= q+6*(k-i):
                    return None
                for r,d,q2,e2 in next_row(a,q,e):
                    for t in DIGITS:
                        n = f+a*d+t*Q+OFFSET[t]
                        if n % 16 == 0:
                            hit = dfs(i+1,q2,e2,Q+COST[t],n//16,
                                      w+(r,),v+(d,),z+(t,))
                            if hit is not None:
                                return hit
                return None
            hit = dfs(0,b,e0,q1,e1,(),(),())
            if hit is not None:
                return hit
    return None


if __name__ == "__main__":
    end = int(sys.argv[1]) if len(sys.argv)>1 else 30
    for k in range(5,end+1):
        for a in COEFFS:
            for b in range(6):
                witness = crossing(a,b,k)
                if witness is not None:
                    raise SystemExit(f"crossing: {a=} {b=} {k=} {witness=}")
        print(f"scale {k}: all five coefficients negative", flush=True)
    print("upper u:", (41*16**end-22-6*end)//24)
