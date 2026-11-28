from collections import defaultdict
from generate import STATES,closed_states

def simulate_bits(p, cap=100000, candidates=16):
    q=h=L=R=0
    heads=[];mins=[];maxs=[]
    lefts=[];rights=[];stateL=defaultdict(list);stateR=defaultdict(list)
    ss=closed_states(p)
    for t in range(cap+1):
        if q in ss:return ('closed',t,ss)
        for right,indices in ((True,stateR.get((q,R),[])),(False,stateL.get((q,L),[]))):
            cand=indices[-candidates:]
            if len(indices)>candidates:cand=[indices[0],*cand]
            for i in reversed(cand):
                delta=h-heads[i]
                if (right and delta<0) or (not right and delta>0):continue
                k=(t-i).bit_length()-1;j=t-(1<<k)
                b=(min if right else max)((mins if right else maxs)[i+(1<<k)-1][k],(mins if right else maxs)[j+(1<<k)-1][k])
                n=heads[i]-b if right else b-heads[i]+1
                if (right and ((L^lefts[i])&((1<<n)-1))==0) or (not right and ((R^rights[i])&((1<<n)-1))==0):
                    return ('side',i,t-i,right,b)
        s=2*q+(R&1);a=p[s]
        if a is None:return ('split',s,t)
        if a=='H':return ('halt',t)
        stateL[q,L].append(t);stateR[q,R].append(t)
        heads.append(h);lefts.append(L);rights.append(R)
        mi=[h];ma=[h];k=1
        while (1<<k)<=t+1:
            j=t-(1<<(k-1));mi.append(min(mi[k-1],mins[j][k-1]));ma.append(max(ma[k-1],maxs[j][k-1]));k+=1
        mins.append(mi);maxs.append(ma)
        w=int(a[0]);q=STATES.index(a[2]);R=(R&~1)|w
        if a[1]=='R':L=(L<<1)|w;R>>=1;h+=1
        else:R=(R<<1)|(L&1);L>>=1;h-=1
    return ('residual',cap)
