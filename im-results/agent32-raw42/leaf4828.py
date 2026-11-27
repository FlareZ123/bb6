#!/usr/bin/env python3
"""Raw42/1LB leaf 4828: exact selected B0 macro and normal-word transducer.
Research model, not a nonhalting certificate. Python integers are unbounded.
See Raw42Leaf4828Recurrence.md for direct transition derivations.
"""
import argparse

TABLE = "1RB0RF1RC1LB0RD0RE1LD0LB0RA0LD---0RD"

def trim(x):
    while x and x[-1] == 0:
        x.pop()
    return x

def at(x,i):
    return x[i] if i < len(x) else 0

def macro(L,R):
    k,a,b,c = at(L,0),at(R,0),at(R,1),at(R,2)
    lp,t = L[1:],R[3:]
    if a == 0:
        l,r,n = lp,[k+b,c+2]+t,4*b+k+5
    elif a >= 2:
        l,r,n = lp,[k,1,a-2,b,c]+t,k+5
    elif b == 0 and c == 0:
        l,r,n = [1,0,k+1]+lp,t,4
    elif b == 0:
        l,r,n = [0,k+1]+lp,[c+1]+t,6
    elif b == 1:
        return None  # F0 query four defined steps later
    elif b == 2:
        l,r,n = lp,[k,c+5]+t,k+11
    else:
        l,r,n = [0,0,k+1]+lp,[b-3,c+2]+t,4*b-1
    return trim(l),trim(r),n

def normal(w):
    """One guarded normal return; None means outside sufficient guard only."""
    if not w or min(w)<2:
        raise ValueError(w)
    out,i,h = [],0,0
    while True:
        b,c,d = at(w,i)+h,at(w,i+1),at(w,i+2)
        if b<2 or (i and b<8 and not (b==6 and i>=len(w))):
            return None
        q,s = divmod(b-2,3)
        r = s+2
        if r==4:
            out.append(q+2)
            h=2*q+2
            i+=1
            continue
        if r==3:
            return out+[q+2,c+2*q+2,d+2]+w[i+3:]
        if q>=2:
            return out+[q,c+2*q+5]+w[i+2:]
        if i:
            return None
        if q==1:
            return [c+7]+w[2:]
        return [c+5,d+2]+w[3:]

def main():
    p=argparse.ArgumentParser()
    p.add_argument("returns",type=int)
    p.add_argument("--crosscheck",action="store_true",
                   help="also follow every selected B0 macro (much slower)")
    args=p.parse_args()
    L,R,w=[],[1,2],[2]
    n,t,maxlen=0,7,1
    for j in range(args.returns):
        nxt=normal(w)
        if nxt is None:
            print("guard failure",j,w)
            return
        if args.crosscheck:
            while True:
                m=macro(L,R)
                if m is None:
                    raise AssertionError(("F0",j,L,R,t+4))
                L,R,cost=m
                n+=1
                t+=cost
                if not L and R and R[0]==1 and all(a>=2 for a in R[1:]):
                    break
            assert R==[1]+nxt,(j,w,nxt,L,R)
        assert sum(nxt)-sum(w) in (2,3,5),(j,w,nxt)
        w=nxt
        maxlen=max(maxlen,len(w))
    print("normal returns",args.returns,"maxlen",maxlen,"word",w)
    if args.crosscheck:
        print("selected B0 macros",n,"primitive defined steps",t)
    print("Finite evidence only; no halt/nonhalt verdict.")
if __name__=="__main__":
    main()
