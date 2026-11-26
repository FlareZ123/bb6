import json, collections, math
DOM=[[8],list(range(25)),[11],[6],[17],[13],[11],list(range(25)),[2],[0,7,15,18,19,20,21,22,24],list(range(25)),list(range(25))]
ROOT=tuple(d[0] if len(d)==1 else -1 for d in DOM)
def trace(t,limit=256):
    if all(v>0 for v in t):return ('total',)
    L=R=q=h=0; seen={}; history=[]
    for n in range(limit+1):
        slot=2*q+(R&1); v=t[slot]
        if v<=0:return ('hole' if v<0 else 'halt',n,slot)
        conf=(q,L,R)
        if conf in seen:return ('cycle',seen[conf],n-seen[conf])
        seen[conf]=n
        lo=hi=h
        for j in range(n-1,max(-1,n-129),-1):
            oq,oh,ol,orr=history[j];lo=min(lo,oh);hi=max(hi,oh)
            if oq!=q or h==oh:continue
            if h>oh and R==orr:
                if (L^ol)&((1<<(oh-lo))-1)==0:return ('side',j,n-j,True,lo)
            elif h<oh and L==ol:
                if (R^orr)&((1<<(hi-oh+1))-1)==0:return ('side',j,n-j,False,hi)
        if n==limit:return ('open',n)
        history.append((q,h,L,R));v-=1
        w=(v//2)&1
        if v&1:L=(L<<1)|w;R>>=1;h+=1
        else:R=(((R>>1)<<1)|w)<<1|(L&1);L>>=1;h-=1
        q=v//4
def main():
    stack=[ROOT];counts=collections.Counter();masses=collections.Counter();leaves=[];maxhalt=0
    while stack:
        t=stack.pop();r=trace(t);typ=r[0];counts[typ]+=1
        if typ=='hole':
            s=r[2]
            for v in DOM[s]:stack.append(t[:s]+(v,)+t[s+1:])
        else:
            masses[typ]+=math.prod(len(DOM[i]) for i,v in enumerate(t) if v<0)
            leaves.append([t,r])
            if typ=='halt':maxhalt=max(maxhalt,r[1]+1)
    assert sum(masses.values())==3515625
    print(counts,masses,maxhalt)
    json.dump(dict(domains=DOM,leaves=leaves,counts=counts,masses=masses,maxhalt=maxhalt),open('box16.json','w'))
if __name__=='__main__':main()
