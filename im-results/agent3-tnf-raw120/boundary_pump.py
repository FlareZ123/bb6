"""Search grouped same-state fresh-boundary triples for one/two insertions.
Only proposes witnesses; the existing multi.generate emits the Lean induction.
"""
from functools import lru_cache
import multi

def candidate(p, events):
    original = multi.local
    multi.local = lru_cache(maxsize=100000)(original)
    try:
        for maxperiod,maxdiff,cap in ((4,16,60),(12,64,60)):
            for side in ("L","R"):
                for q in range(6):
                    es=[(t,c) for t,s,c in events if s==side and c.q==q
                        and not (c.l.pre if side=="L" else c.r.pre)]
                    for period in range(1,maxperiod+1):
                        for i in range(min(cap,len(es)-2*period)):
                            t,c=es[i]
                            _,d=es[i+period]
                            _,e=es[i+2*period]
                            if d.h0-c.h0!=e.h0-d.h0:continue
                            a,b,z=[v.r.pre if side=="L" else v.l.pre for v in (c,d,e)]
                            diff=len(b)-len(a)
                            if not 1<=diff<=maxdiff or len(z)-len(b)!=diff:continue
                            def attempt(w,v):
                                w,v=multi.clean(w),multi.clean(v)
                                st=multi.C(q,w if side=="R" else (),() if side=="R" else w)
                                tg=multi.C(q,v if side=="R" else (),() if side=="R" else v)
                                res=multi.pump(p,st,tg,3000)
                                return (t,st,tg,res) if res else None
                            L,R=multi.lit,multi.rep
                            for k in range(len(a)+1):
                                if a[:k]!=b[:k]:break
                                I=b[k:k+diff]
                                if b[k+diff:]==a[k:] and a[:k]+I*2+a[k:]==z:
                                    ans=attempt(L(a[:k])+R(I)+L(a[k:]),
                                                L(a[:k]+I)+R(I)+L(a[k:]))
                                    if ans:return ans
                                for d1 in range(1,diff):
                                    I=b[k:k+d1]
                                    for j in range(k,len(a)+1):
                                        if b[k+d1:j+d1]!=a[k:j]:break
                                        J=b[j+d1:j+diff]
                                        if b[j+diff:]!=a[j:] or a[:k]+I*2+a[k:j]+J*2+a[j:]!=z:continue
                                        ans=attempt(L(a[:k])+R(I)+L(a[k:j])+R(J)+L(a[j:]),
                                                    L(a[:k]+I)+R(I)+L(a[k:j]+J)+R(J)+L(a[j:]))
                                        if ans:return ans
        return None
    finally:
        multi.local=original
