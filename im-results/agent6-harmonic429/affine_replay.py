#!/usr/bin/env python3
"""Exact-integer #429 section-block generator for BB429AffineReplay.lean.
The branch selector is untrusted: Lean independently checks each block.
Times count BB429.next applications, never raw Turing-machine transitions.
"""
import argparse
import csv
from pathlib import Path


def tag(u, w):
    g = w - 2*u
    if g >= 3: return 'F'
    if g == 2: return 'R2'
    if g == 1: return 'R1'
    if g == 0: return 'R0'
    if g == -1: return 'Halt'
    if g == -2: return 'E1'
    if g == -3: return 'O2'
    r = g % 4
    if r == 0: return 'Eeven'
    if r == 2: return 'Eodd'
    if r == 3: return 'Oodd'
    return 'Oeven1' if w == 1 else 'Oeven'


def out(t, u, w):
    if t == 'F': return 2*u+3, w-2*u-3
    if t == 'R2': return 0, 4*u+18
    if t == 'R1': return 11, 4*u+2
    if t == 'R0': return 0, 4*u+12
    if t == 'E1': return 0, 2*w+12
    if t == 'Eeven': return 11, 2*u+w-2
    if t == 'Eodd': return 0, 2*u+w+10
    if t == 'O2': return 0, 2*w+8
    if t == 'Oeven1': return 11, 2*u+10
    if t == 'Oeven': return u-w//2+7, 2*w-4
    if t == 'Oodd': return u-w//2+3, 2*w
    raise ValueError(t)


def section(u, w, limit=10000):
    word = []
    for _ in range(limit):
        t = tag(u,w)
        if t == 'Halt': return u,w,word,True
        u,w = out(t,u,w)
        word.append(t)
        if u in (0,11): break
    return u,w,word,False


def translation_count(u, w, word, delta):
    """Find maximal guard horizon for this translation, using exact slopes."""
    if delta <= 0 or delta % 4: return 1
    u0,w0 = u,w
    p,q = 0,delta//4
    hi = None
    def cap(n):
        nonlocal hi
        assert n >= 0
        hi = n if hi is None else min(hi,n)
    for t in word:
        assert tag(u,w) == t
        g = w-2*u
        s = 4*(q-p)
        if t == 'F':
            if s < 0: cap((g-3)//(-s))
        elif t in ('R2','R1','R0','E1','O2'):
            if s: cap(0)
        else:
            upper = {'Eeven':-4,'Eodd':-6,'Oeven1':-7,'Oeven':-7,'Oodd':-5}[t]
            if s > 0: cap((upper-g)//s)
            if t == 'Oeven1' and q: cap(0)
            if t == 'Oeven' and q < 0: cap((w-3)//(-4*q))
        u,w = out(t,u,w)
        if t == 'F': p,q = 2*p,q-p
        elif t in ('R2','R1','R0'): p,q = 0,2*p
        elif t in ('E1','O2'): p,q = 0,2*q
        elif t in ('Eeven','Eodd'): p,q = 0,p+q
        elif t == 'Oeven1': p,q = 0,p
        else: p,q = p-q,2*q
    if (u,w,p,q) != (u0,w0+delta,0,delta//4): return 1
    if hi is None: raise RuntimeError(f'unbounded translation: {u0,w0,word,delta}')
    return hi+1


def blocks(budget, start=(0,0), start_time=0):
    u,w = start
    time = start_time
    for _ in range(budget):
        v,z,word,halt = section(u,w)
        if halt:
            raise RuntimeError(f'halting line {(v,z)} at {time+len(word)}')
        if v not in (0,11):
            # Finite progress remains valid if an unusually long nonsection segment occurs.
            count = 1
        else:
            if v != u:
                vv,zz,word2,halt2 = section(v,z)
                if vv == u and not halt2: v,z,word = vv,zz,word+word2
            count = translation_count(u,w,word,z-w) if v==u else 1
        delta = z-w
        quarter = delta//4 if count>1 else 0
        end = (u,w+delta*count) if count>1 else (v,z)
        end_time = time + count*len(word)
        yield (len(word),count,quarter,u,w,time,*end,end_time)
        u,w = end
        time = end_time


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('budget',type=int)
    parser.add_argument('output',type=Path)
    parser.add_argument('--u',type=int,default=0)
    parser.add_argument('--w',type=int,default=0)
    parser.add_argument('--time',type=int,default=0)
    args=parser.parse_args()
    with args.output.open('w',newline='') as f:
        writer=csv.writer(f)
        writer.writerow(('len','count','quarter','u','w','time','end_u','end_w','end_time'))
        for i, row in enumerate(blocks(args.budget,(args.u,args.w),args.time),1):
            writer.writerow(row)
            if i%10000==0: print(i,row[-3:],flush=True)
    print('final',i,row[-3:],flush=True)


if __name__=='__main__': main()
