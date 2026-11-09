#!/usr/bin/env python3
"""Exact inverse-parent census for the Space Needle cancellation feeder r=6.

A necessary and sufficient incoming-parent equation is
2*x+3-2*u = (2^(u+1)+3)*(2*p+3).
The test checks all valuations 0<=u<=K, where x is the shifted
cancellation feeder and K is its terminal exponent.

Small-prime witnesses and signed base-B substitution are exact; all
positive divisibility hits are independently confirmed by an exact %
operation. No random sampling contributes to the completeness decision.
"""
import hashlib
import json
import math
import time
from array import array

R = 6
PRIME_LIMIT = 10000

def primes(n):
    sieve = bytearray(b"\1") * (n+1)
    sieve[:2] = b"\0\0"
    for p in range(2, math.isqrt(n)+1):
        if sieve[p]:
            sieve[p*p:n+1:p] = b"\0" * (((n-p*p)//p)+1)
    return (p for p in range(2,n+1) if sieve[p])

def order_log(p):
    z = 1
    e = -1
    for j in range(1,p):
        z = (2*z) % p
        if z == (p-3) % p and e < 0:
            e = j
        if z == 1:
            return (j,e) if e >= 0 else None
    return None

def signed_remainder(N,u):
    shift = u+1
    B = 1 << shift
    mask = B-1
    S = 0
    c = 1
    digits = 0
    while N:
        S += c*(N & mask)
        N >>= shift
        c *= -3
        digits += 1
    return S,B,digits

def main():
    started = time.monotonic()
    v = (9**R+3)//2
    K = R*(9**R+5)-1
    D = (1 << (v+1))+3
    C = 3*(1<<v)+v+3
    q,rem = divmod((1<<K)-C,D)
    assert rem == 0 and q >= 0
    x = (1<<v)*(2*q+3)
    assert x < 1<<K and x.bit_length() == K
    N0 = 2*x+3
    print("ROOT",dict(r=R,K=K,v=v,q_bits=q.bit_length(),x_bits=x.bit_length()),flush=True)

    witness = array("H",[0])*(K+1)
    useful = 0
    for p in primes(PRIME_LIMIT):
        if p <= 3:
            continue
        h = order_log(p)
        if h is None:
            continue
        L,e = h
        assert pow(2,L,p)==1 and pow(2,e,p)==p-3
        useful += 1
        xm = x % p
        for u in range((e-1)%L,K+1,L):
            if not witness[u] and (2*xm+3-2*u)%p:
                witness[u] = p
    print("SIEVE",dict(useful=useful,rejected=sum(bool(z) for z in witness),
                       elapsed=round(time.monotonic()-started,2)),flush=True)

    low = 0
    high = 0
    max_digits = 0
    parents = []
    for u in range(v+1):
        if witness[u]:
            continue
        low += 1
        N = N0-2*u
        if u >= 10000:
            S,B,digits = signed_remainder(N,u)
            good = S % (B+3) == 0
        else:
            good = N % ((1<<(u+1))+3) == 0
        if good:
            assert N % ((1<<(u+1))+3) == 0
            parents.append(u)
            print("LOW_PARENT",u,flush=True)
        if low%10000==0:
            print("LOW_PROGRESS",dict(low=low,u=u,elapsed=round(time.monotonic()-started,2)),flush=True)

    for u in range(v+1,K+1):
        if witness[u]:
            continue
        high += 1
        N = N0-2*u
        S,B,digits = signed_remainder(N,u)
        max_digits = max(max_digits,digits)
        assert digits <= 2*R and 3**(2*R+1) < B
        absS = abs(S)
        if absS == (absS>>(u+1))*(B+3):
            assert N % (B+3) == 0
            parents.append(u)
            print("HIGH_PARENT",u,flush=True)
        if high%50000==0:
            print("PROGRESS",dict(high=high,u=u,elapsed=round(time.monotonic()-started,2)),flush=True)

    checksum = hashlib.sha256()
    for u,p in enumerate(witness):
        if p:
            checksum.update(u.to_bytes(4,"little"))
            checksum.update(p.to_bytes(2,"little"))
    summary = dict(r=R,K=K,v=v,useful_primes=useful,
        rejected=sum(bool(z) for z in witness),low=low,high=high,
        max_digits=max_digits,parent_valuations=parents,
        witness_sha256=checksum.hexdigest(),
        elapsed=round(time.monotonic()-started,2))
    assert summary["rejected"]+low+high == K+1
    print("RESULT",json.dumps(summary,sort_keys=True),flush=True)

if __name__ == "__main__":
    main()
