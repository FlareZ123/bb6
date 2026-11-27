"""Symbolic search: one n-fold block tracked in a concrete n=0 trajectory.
Every step and sweep generated below is checked by rfl for arbitrary tails."""
import collections

def step(p,q,l,r):
    a=(l or '0')[0]
    if a not in '01':raise ValueError('read opaque tail')
    m=p[2*q+int(a)]
    if m=='---':raise ValueError('hole')
    w,d,s=m;q=ord(s)-65
    if d=='R':
        b=(r or '0')[0]
        if b not in '01':raise ValueError('read opaque tail')
        l=b+w+l[1:];r=r[1:]
    else:l=l[1:];r=w+r
    return q,l,r

def parse(t):
    t=t.replace('_','');return [t[j:j+3] for j in range(0,36,3)]

def trace(p,k):
    q,l,r=0,'1'*k,'111';tr=[(q,l,r)]
    for _ in range(2000):
        q,l,r=step(p,q,l,r);tr.append((q,l,r))
        if q==0 and l and set(l)=={'1'} and r=='111':return tr
    raise ValueError('no return')

def sweep(p,q,side,frame,I,oframe,maxcost=120):
    a=frame+I+'X';b=oframe+'Y';l,r=(a,b) if side==0 else (b,a)
    qq=q
    for cost in range(1,maxcost+1):
        try:qq,l,r=step(p,qq,l,r)
        except ValueError:return
        a,b=(l,r) if side==0 else (r,l)
        if qq==q and a==frame+'X' and b.startswith(oframe) and b.endswith('Y') and len(b)==len(oframe)+len(I)+1:
            return cost,b[len(oframe):-1]

def search(p,k):
    tr=trace(p,k);target=len(tr)-1
    init=[(0,0,j,'111111') for j in range(k+1)]
    Q=collections.deque(init);prev={s:None for s in init};cache={};end=None
    while Q:
        s=Q.popleft();t,side,pos,I=s;q,l,r=tr[t];words=[l,r];a,b=words[side],words[1-side]
        if t==target and side==0 and I=='111111':end=s;break
        if t<target:
            ww=words.copy();ww[side]=a[:pos]+'X'+a[pos:]
            try:
                qq,ll,rr=step(p,q,*ww);z=(ll,rr);assert z[side].count('X')==1 and 'X' not in z[1-side]
                v=(t+1,side,z[side].index('X'),I)
                assert (qq,ll.replace('X',''),rr.replace('X',''))==tr[t+1]
                if v not in prev:prev[v]=(s,('step',1));Q.appendleft(v)
            except ValueError:pass
        frame=a[:pos]
        for j in range(min(len(b),16)+1):
            oframe=b[:j];key=(q,side,frame,I,oframe)
            if key not in cache:cache[key]=sweep(p,q,side,frame,I,oframe)
            out=cache[key]
            if out:
                cost,O=out;v=(t,1-side,j,O)
                if v not in prev:prev[v]=(s,('sweep',cost));Q.append(v)
    if end is None:return None
    path=[];s=end
    while prev[s] is not None:
        a,edge=prev[s];path.append((a,s,edge));s=a
    path.reverse();out=[]
    for a,b,e in path:
        if out and e[0]=='step' and out[-1][2][0]=='step':out[-1]=(out[-1][0],b,('step',out[-1][2][1]+1))
        else:out.append((a,b,e))
    return dict(k=k,kout=len(tr[-1][1]),base=target,coef=sum(e[1] for _,_,e in out if e[0]=='sweep'),steps=[dict(src=a,dst=b,edge=e,cfg=tr[a[0]],out=tr[b[0]]) for a,b,e in out])
