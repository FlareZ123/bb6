"""Search long epochs, then reuse the exact one-block proof generator."""
import generate_sweeps as one
from generate_sweeps import W,C

def candidate(p,events,side,state,period,maxdiff=64):
    base=one.local
    one.local=lambda p,q,l,r,side,block:base(p,q,l,r,side,block,limit=500)
    try:
        ev=[(t,c) for t,s,c in events if s==side and c.q==state and (c.r.pre=='' if side=='R' else c.l.pre=='')]
        for i,(t,c) in enumerate(ev[:8]):
            if i+2*period>=len(ev):break
            _,d=ev[i+period];_,e=ev[i+2*period]
            delta=d.h0-c.h0
            if e.h0-d.h0!=delta:continue
            a,b,z=(c.l.pre,d.l.pre,e.l.pre) if side=='R' else (c.r.pre,d.r.pre,e.r.pre)
            diff=len(b)-len(a)
            if not 1<=diff<=maxdiff:continue
            for k in range(len(a)+1):
                if b[:k]!=a[:k] or b[k+diff:]!=a[k:]:continue
                block=b[k:k+diff]
                if a[:k]+block*2+a[k:]!=z:continue
                w,v=W(a[:k],block,a[k:]),W(a[:k]+block,block,a[k:])
                st=C(c.q,0,0,w if side=='R' else W(),w if side=='L' else W())
                tg=C(c.q,delta,0,v if side=='R' else W(),v if side=='L' else W())
                ans=one.pump(p,st,tg,3000)
                if ans:return t,c,st,tg,ans
        return None
    finally:
        one.local=base
