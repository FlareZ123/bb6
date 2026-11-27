"""Untrusted fixed-point compression; the final Lean checker is unchanged."""
from emit_rungram import witness

def compact(table,d):
    es,S=witness(table,*d)
    P=[{},{}]
    for i in range(2):
        for dst,ins in es[i].items():
            for b,src in ins:
                if src==dst==b==0:continue
                assert (src,b) not in P[i] or P[i][src,b]==dst
                P[i][src,b]=dst
    return P,S

def minimize(table,d):
    P,S=compact(table,d)
    n=[len(x)//2 for x in d]
    for _ in range(6):
        changed=False
        for side in range(2):
            obs=[set() for i in range(n[side])]
            for q,a,l,r in S:
                x,y=(l,r) if side==0 else (r,l)
                obs[x].add((q,a,y))
            color=[];ids={}
            for i,o in enumerate(obs):
                key=(i==0,frozenset(o));color.append(ids.setdefault(key,len(ids)))
            while True:
                ids={};new=[]
                for i in range(n[side]):
                    key=(color[i],*(color[P[side][i,b]] if (i,b) in P[side] else -1 for b in [0,1]))
                    new.append(ids.setdefault(key,len(ids)))
                if new==color:break
                color=new
            if len(ids)==n[side]:continue
            dd=[0]*(len(ids)*2)
            for (i,b),j in P[side].items():dd[2*color[i]+b]=color[j]
            candidate=d.copy();candidate[side]=dd
            try:pp,ss=compact(table,candidate)
            except ValueError:continue
            d=candidate;P,S=pp,ss;n[side]=len(ids);changed=True
        if not changed:break
    return d,P,S
