import json,sys
from functools import lru_cache
from collections import Counter,defaultdict
from pathlib import Path
p=json.load(open('partition.json'))['open'][int(sys.argv[1])]
N=int(sys.argv[2]); MIN=4
@lru_cache(None)
def one(q,lp,rp,I,right):
    l,r=(lp,rp+I) if right else (lp+I,rp)
    q0=q
    for k in range(1,60):
        if not l:return None
        v=p[2*q+int(l[0])]
        if v==24:return None
        w=str((v>>1)&1);q=v//4
        if v&1:
            if not r:return None
            l,r=r[0]+w+l[1:],r[1:]
        else:l,r=l[1:],w+r
        if q!=q0:continue
        if right and r==rp and l.startswith(lp) and len(l)==len(lp)+len(I):return k,l[len(lp):]
        if not right and l==lp and r.startswith(rp) and len(r)==len(rp)+len(I):return k,r[len(rp):]
    return None

def step(z):
 q,l,r=z;v=p[2*q+int(l[0] if l else '0')];assert v!=24
 w=str((v>>1)&1)
 return (v//4, (r[0] if r else '0')+w+l[1:],r[1:]) if v&1 else (v//4,l[1:],w+r)

def repetitions(a,I):
    n=0;k=len(I)
    while a.startswith(I,n*k):n+=1
    return n

def accelerate(z,remaining):
    q,l,r=z;best=None
    for right in (True,False):
        a,b=(r,l) if right else (l,r)
        # repeat block starts within first four cells; use fixed frame of up to four cells on opposite side
        for j in range(min(5,len(a))):
            pref,aa=a[:j],a[j:]
            for w in range(1,7):
                if len(aa)<MIN*w:break
                I=aa[:w]
                if aa[:MIN*w]!=I*MIN:continue
                n=repetitions(aa,I)
                for k in range(min(5,len(b))+1):
                    bpre=b[:k];lp,rp=(bpre,pref) if right else (pref,bpre)
                    res=one(q,lp,rp,I,right)
                    if not res:continue
                    c,O=res;n2=min(n,remaining//c)
                    if n2<MIN:continue
                    score=c*n2
                    if best is None or score>best[0]:
                        aout=pref+aa[n2*w:];bout=bpre+O*n2+b[k:]
                        out=(q,bout,aout) if right else (q,aout,bout)
                        best=(score,(right,q,lp,rp,I,O,c),n2,out)
    return best

z=(0,'','');n=0;prev=z;cnt=0;actions=[];rules=Counter()
while n<N:
    acc=accelerate(z,N-n)
    if acc:
        if cnt:actions.append(('finite',cnt,prev,z));cnt=0
        d,rule,k,zz=acc;actions.append(('sweep',rule,k,z,zz));rules[rule]+=1
        n+=d;z=zz;prev=z
    else:
        z=step(z);cnt+=1;n+=1
        if cnt==64:actions.append(('finite',cnt,prev,z));cnt=0;prev=z
if cnt:actions.append(('finite',cnt,prev,z))
assert p[2*z[0]+int(z[1][0] if z[1] else '0')]==24
print('actions',len(actions),'finite',sum(a[1] for a in actions if a[0]=='finite'),'sweep steps',sum(a[1][-1]*a[2] for a in actions if a[0]=='sweep'),'rules',len(rules),'counts',Counter(a[0] for a in actions));print(rules.most_common(20));json.dump(actions,open(f'sweep{sys.argv[1]}.json','w'))
