"""Candidate discovery for the Raw45 A1=1LB/B1=0LA/C1=1RE four-hole subtree.
Run from repository root: python3 im-results/agent24-raw45-c1re/scan.py /tmp/re.json
The output is NOT trusted proof data until the separate Lean audit accepts it.
"""
import sys, json, time, collections
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'agent48-raw139-f1-oneLA'))
import autopump as ap

PARENT='1RB1LB_1RC0LA_0RD1RE_1LD1RB_------_------'
def parse(s):
    s=s.replace('_','')
    return [24 if v=='---' else (ord(v[2])-65)*4+int(v[0])*2+(v[1]=='R') for v in (s[i:i+3] for i in range(0,36,3))]

def string(a):
    s=['---' if x==24 else f'{(x>>1)&1}{"R" if x&1 else "L"}{chr(65+(x>>2))}' for x in a]
    return '_'.join(''.join(s[i:i+2]) for i in range(0,12,2))

def word(w): return [x if isinstance(x,str) else '*'+x.p for x in w]

def recipe(i,s,res):
    e,fam,(ops,end)=res
    groups=[]; a=b=0
    for op in ops:
        if op[0]=='step':
            b+=1
            if groups and isinstance(groups[-1],int): groups[-1]+=1
            else: groups.append(1)
        else:
            side,q,sp,dp,P,O,k,sr,dr=op[-1]
            lp,rp,L,R=(sp,dp,sr,dr) if side=='L' else (dp,sp,dr,sr)
            groups.append([side,lp,rp,P,O,word(L),word(R),k]); a+=k
    return [i,s,e,[fam[0],word(fam[1]),word(fam[2])],a,b,groups]

def classify(p,limit=250):
    q=h=0; tape=set(); hist=[]; prev=[[] for _ in range(6)]
    for t in range(limit+1):
        ones=frozenset(tape)
        for i in reversed(prev[q][-32:]):
            _,x,o=hist[i]; delta=h-x
            heads=[z[1] for z in hist[i:]]
            if delta>=0:
                b=min(heads)
                if {j-x for j in o if j>=b}=={j-h for j in ones if j>=b+delta}:
                    return ('cycle',i,t-i,True,b)
            if delta<=0:
                b=max(heads)
                if {j-x for j in o if j<=b}=={j-h for j in ones if j<=b+delta}:
                    return ('cycle',i,t-i,False,b)
        hist.append((q,h,ones)); prev[q].append(t)
        j=2*q+int(h in tape); v=p[j]
        if v==24: return ('query',t,j)
        if v&2: tape.add(h)
        else: tape.discard(h)
        h+=1 if v&1 else -1; q=v>>2
    return ('open',)

def scan(parent=PARENT, limit=250):
    counts=collections.Counter(); pumps=[]; opens=[]; maxquery=0
    def search(p):
        nonlocal maxquery
        r=classify(p,limit); kind=r[0]
        if kind=='cycle': counts['cycle']+=1; return r
        if kind=='query':
            _,n,j=r; maxquery=max(maxquery,n)
            if p.count(24)==1: counts['last']+=1; return ('last',n,j)
            counts['split']+=1; kids=[]
            for v in range(24):
                a=p.copy(); a[j]=v; kids.append(search(a))
            return ('split',n,j,kids)
        r=ap.find(p,2000)
        if r:
            counts['pump']+=1; idx=len(pumps)
            pumps.append(recipe(idx,string(p),r)); return ('pump',idx)
        counts['open']+=1; idx=len(opens); opens.append(string(p)); return ('open',idx)
    p=parse(parent); r=classify(p,limit); assert r[0]=='query'
    _,n,j=r; kids=[]; start=time.monotonic()
    for v in range(24):
        a=p.copy(); a[j]=v; old=counts.copy(); kids.append(search(a))
        print(v,string(a),counts-old,round(time.monotonic()-start,2),flush=True)
    return {'parent':parent,'tree':['split',n,j,kids],'counts':dict(counts),'pumps':pumps,'opens':opens,'maxquery':max(maxquery,n)}

if __name__=='__main__':
    out=scan(sys.argv[2] if len(sys.argv)>2 else PARENT)
    Path(sys.argv[1]).write_text(json.dumps(out)+'\n')
    print(out['counts'],out['maxquery'],out['opens'],flush=True)
