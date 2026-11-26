"""Branching variant of Agent10's symbolic sweep search (untrusted)."""
from collections import deque
import multi

def pump(p, st, tg, limit=10000):
    target=tg.norm()
    todo=deque([(st,[])])
    seen={st.norm()}
    while todo and len(seen)<=limit:
        c,hist=todo.popleft()
        if c.norm()==target:
            return hist,c
        if len(hist)>=300:
            continue
        def add(d,event):
            k=d.norm()
            if k not in seen:
                seen.add(k)
                todo.append((d,hist+[event]))
        for sd in ("L","R"):
            w,o=(c.l,c.r) if sd=="L" else (c.r,c.l)
            lp,wr,op=multi.prefix(w),multi.rest(w),multi.prefix(o)
            if not wr or not wr[0][1]:
                continue
            I=wr[0][0]
            for j in range(min(20,len(op))+1):
                ans=multi.local(p,c.q,lp if sd=="L" else op[:j],
                    op[:j] if sd=="R" else lp,sd,I)
                if not ans:
                    continue
                k,O=ans
                w2=multi.clean(multi.lit(lp)+wr[1:])
                o2=multi.clean(multi.lit(op[:j])+multi.rep(O)+multi.lit(op[j:])+multi.rest(o))
                d=multi.C(c.q,w2,o2) if sd=="L" else multi.C(c.q,o2,w2)
                add(d,("loop",c,d,k,sd,I,O,j))
        try:
            d=multi.step(p,c)
        except ValueError:
            continue
        add(d,("step",c,d,1))
    return None

def generate(i,p,seed):
    def unpack(c):
        q,l,r=c
        return multi.C(q,tuple((w,bool(b)) for w,b in l),tuple((w,bool(b)) for w,b in r))
    st,tg=unpack(seed["st"]),unpack(seed["tg"])
    ans=pump(p,st,tg)
    assert ans is not None,(i,seed)
    return multi.generate(i,p,(seed["t"],st,tg,ans))
