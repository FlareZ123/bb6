#!/usr/bin/env python3
"""Exact RF149 E0-section recurrence; no all-time nonhalting claim."""
from collections import Counter
from random import Random
TABLE = "1RB1RE_1RC0RA_0RD0RA_1LD0LE_1RF0LE_1RB---"
CODE = TABLE.replace("_", "")
TRANS = [None if w == "-" else (int(w), 1 if d == "R" else -1, ord(q)-65)
         for w,d,q in (CODE[i:i+3] for i in range(0,36,3))]

def step(left, right):
    # left = tuple of positive run lengths, separated by single zeros.
    # right = nonnegative integer, nearest bit least significant.
    if right & 1:
        return None, 1, "hole"
    right >>= 1
    w = [left[0]+2, *left[1:]] if left else [2]
    n = 2
    loops = []
    while True:
        b = right & 1
        right >>= 1
        n += 1
        if b == 0:
            c = right & 1
            right >>= 1
            n += 1
            if c == 0:
                d = right & 1
                right >>= 1
                n += 1
                if d == 0:
                    m = w[0]
                    return (tuple(w[1:]), (right << (m+3)) | (3 << (m+1))), n+2+m, "".join(loops)+"D0"
                w[0] += 1
                return (tuple(w), right << 1), n, "".join(loops)+"D1"
            extra = 1
        else:
            extra = 0
        a = right & 1
        right >>= 1
        n += 1
        if a == 0:
            w[0] += extra
            w.insert(0,1)
            loops.append("x" if extra else "y")
            continue
        e = right & 1
        right >>= 1
        if e == 0:
            w[0] += extra
            w.insert(0,1)
            return (tuple(w),right),n,"".join(loops)+("A0x" if extra else "A0y")
        w[0] += extra
        return (tuple(w),right<<2),n+2,"".join(loops)+("A1x" if extra else "A1y")

def word(s):
    return sum((b=="1")<<i for i,b in enumerate(s))
def show(r):
    return bin(r)[2:][::-1] if r else ""
def lword(left):
    return "0".join("1"*n for n in left)

def primitive_check():
    rng=Random(149)
    for _ in range(10000):
        left=tuple(rng.randrange(1,16) for _ in range(rng.randrange(6)))
        right=rng.randrange(1<<rng.randrange(0,40))
        l,r=lword(left),show(right)
        tape={-i-1 for i,b in enumerate(l) if b=="1"} | {i+1 for i,b in enumerate(r) if b=="1"}
        head,state=0,4
        pred,n,kind=step(left,right)
        for k in range(1000):
            if k and state==4 and head not in tape:
                ll="".join("1" if i in tape else "0" for i in range(head-1,min(tape|{head})-1,-1))
                rr="".join("1" if i in tape else "0" for i in range(head+1,max(tape|{head})+1))
                assert pred is not None and (lword(pred[0]),show(pred[1]),n)==(ll,rr,k),(left,r,kind,pred,n,ll,rr,k)
                break
            tr=TRANS[2*state+int(head in tape)]
            if tr is None:
                assert pred is None and k==1
                break
            w,d,state=tr
            if w: tape.add(head)
            else: tape.discard(head)
            head+=d
        else:
            raise AssertionError("unexpected regression cutoff")
    print("10000 macro regression cases passed")

if __name__=="__main__":
    import argparse
    p=argparse.ArgumentParser()
    p.add_argument("--steps",type=int,default=2000000)
    a=p.parse_args()
    primitive_check()
    left,right,t,k=(),word("0011"),7,0
    stats=Counter()
    while t<a.steps:
        ret,n,kind=step(left,right)
        if ret is None:
            print("F1",t+n)
            break
        stats[kind]+=1
        left,right=ret
        t+=n
        k+=1
    print("end",t,k,"return kinds",stats)
