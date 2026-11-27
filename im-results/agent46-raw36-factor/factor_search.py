"""Sparse BiDFA factor abstraction; discovery is untrusted, Lean checks the result.
Usage:
  python factor_search.py --fixtures  # deterministic checked bank from groups
  python factor_search.py depth0.zip depth1.zip ...  # discover from pinned artifacts
"""
from collections import defaultdict, deque
from itertools import product
from pathlib import Path
import hashlib, json, sys, zipfile

D=Path(__file__).resolve().parent
EXPECTED="d8c24af73349583b6a1c842680d2b201ddd585265db721086f88d3c01426da54"
class DFA:
    def __init__(self,fn,init):
        self.fn=fn;self.ss=[init];self.idx={init:0};self.tab={}
    def push(self,s,b):
        key=(s,b)
        if key in self.tab:return self.tab[key]
        x=self.fn(self.ss[s],b);k=self.idx.get(x)
        if k is None:k=len(self.ss);self.idx[x]=k;self.ss.append(x)
        self.tab[key]=k;return k
    def dump(self):
        return [self.tab.get((i,b),0) for i in range(len(self.ss)) for b in range(2)]

def solve(t,dl,dr,cap=10000):
    d=[dl,dr];p=[t[i:i+3] for i in range(0,36,3)]
    p=[None if x=='---' else (int(x[0]),int(x[1]=='R'),ord(x[2])-65) for x in p]
    es=[defaultdict(set),defaultdict(set)];ws=[defaultdict(list),defaultdict(list)]
    S={(0,0,0,0)};Q=deque(S)
    for e in es:e[0].add((0,0))
    def add(q,a,l,r):
        s=q,a,l,r
        if s not in S:S.add(s);Q.append(s)
    def pop(s,b,src):
        q,a,l,r=s;w,direction,n=p[2*q+a]
        if direction:add(n,b,d[0].push(l,w),src)
        else:add(n,b,src,d[1].push(r,w))
    while Q:
        if len(S)>cap:return None
        s=Q.popleft();q,a,l,r=s;m=p[2*q+a]
        if m is None:return None
        w,side,n=m;old=l if side else r;dest=d[1-side].push(old,w);e=w,old
        if e not in es[1-side][dest]:
            es[1-side][dest].add(e)
            for st in ws[1-side][dest]:pop(st,*e)
        x=r if side else l;ws[side][x].append(s)
        for b,y in es[side][x]:pop(s,b,y)
    return dict(table=t,states=len(S),edges=sum(len(v) for E in es for v in E.values()),dfa=[dl.dump(),dr.dump()])

def make(k,period,patterns,mode,mod=2):
    k=max(k,max(map(len,patterns),default=0)-1);mask=(1<<k)-1
    pp=[(len(p),int(p,2)) for p in patterns]
    init=(-1,0,0,tuple(0 for p in pp))
    def f(s,b):
        w,n,i,cs=s
        if w==-1 and b==0:return s
        w=max(w,0);v=(w<<1)|b;out=[]
        for c,(l,x) in zip(cs,pp):
            hit=(n+1>=l and v&((1<<l)-1)==x)
            if mode==0:r=int(c or hit)
            elif mode==1:r=(c+hit)%mod
            elif mode==2:r=min(c+hit,mod)
            elif mode==3:r=1 if hit else min(c+1,mod) if c else 0
            elif mode==4:r=1 if hit else 1+(c%mod) if c else 0
            out.append(r)
        return (v&mask,min(n+1,k),(i+1)%period,tuple(out))
    return DFA(f,init)

PS=[(),('00',),('000',),('11',),('111',),('00','11'),('0100',),('0010',),('00100',),('000','0010'),('00','0010'),('00','00100'),('00','11','0010'),('000','111'),('000','111','0010'),('001','011'),('01','10'),('0011','1100'),('010','101')]
PARAMS=[(2,1,('00100',),0),(2,3,('00','11'),2)]+[(k,p,ps,m) for k,p,ps,m in product(range(2,7),[1,2,3],PS,range(5)) if ps or not m]
def trial(t,feature):
    a=solve(t,make(*feature),make(*feature))
    if a is not None:a['feature']=feature
    return a
def one(t):
    for f in PARAMS:
        a=trial(t,f)
        if a is not None:return a
def decode(t):
    assert len(t)==12 and all('A'<=c<='Y' for c in t)
    return ''.join('---' if n==24 else str(n//12)+'LR'[(n%12)//6]+chr(65+n%6) for n in map(lambda c:ord(c)-65,t))
def fixtures():
    out=[]
    for line in (D/'factor_groups.txt').read_text().splitlines():
        feature,encoded=line.split('] ',1)
        f=json.loads(feature+']')
        for t in encoded.split():
            a=trial(decode(t),f)
            assert a is not None,t
            out.append(a)
    out.sort(key=lambda a:a['table'])
    assert len(out)==len({a['table'] for a in out})==227
    canonical=json.dumps(out,sort_keys=True,separators=(',',':')).encode()
    assert hashlib.sha256(canonical).hexdigest()==EXPECTED
    return out
def main():
    if sys.argv[1:]==['--fixtures']:
        out=fixtures()
    else:
        from concurrent.futures import ProcessPoolExecutor
        ts=sorted({x['table'].replace('_','') for f in sys.argv[1:] for x in json.loads(zipfile.ZipFile(f).read('depth.json'))['cases'] if x['kind']=='open'})
        assert ts
        with ProcessPoolExecutor(max_workers=8) as pool:out=[a for a in pool.map(one,ts) if a is not None]
        print('input',len(ts),'certified candidates',len(out))
    (D/'raw36-factor.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
    print('wrote',len(out),'literal BiDFA certificates')
if __name__=='__main__':main()
