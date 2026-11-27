from collections import defaultdict,deque
from pathlib import Path
import sys,itertools,time,json
r=Path(__file__).resolve().parent;sys.path.insert(0,str(r.parent/'agent11-raw39'));from rungram_regen import RunDFA
class DFA:
    def __init__(self,params):
        self.p=params;self.words=[self.zero()];self.ids={self.words[0]:0};self.delta=[[None,None]]
    def push(self,i,b):
        j=self.delta[i][b]
        if j is None:
            v=self.key(self.words[i],b)
            j=self.ids.get(v)
            if j is None:j=len(self.words);self.ids[v]=j;self.words.append(v);self.delta.append([None,None])
            self.delta[i][b]=j
        return j
    def finish(self):return [0 if j is None else j for a in self.delta for j in a]
class Bits(DFA):
    def zero(self):return 0
    def key(self,v,b):return ((v<<1)|b)&((1<<self.p)-1)
class Lag(DFA):
    def zero(self):return (0,())
    def key(self,v,b):
        lag,c,m,k=self.p;x,rs=v;a=b^((x>>(lag-1))&1) if lag else b
        if not rs and a==0:y=()
        elif rs and rs[0][0]==a:
            n=rs[0][1];y=((a,c+1 if n==c+m else n+1),)+rs[1:]
        else:y=(((a,1),)+rs)[:k]
        return (((x<<1)|b)&((1<<lag)-1),y)

def discover(t,D,L,R,stop=0,fuel=12,cap=100000):
    ds=[D(L),D(R)];t=t.replace('_','');p=[t[i:i+3] for i in range(0,36,3)];
    # context = q,a,leftPrefix,leftTail,rightPrefix,rightTail,fuel remaining
    seen=set();states=set();todo=deque();E=[defaultdict(set),defaultdict(set)];wait=[defaultdict(set),defaultdict(set)];E[0][0].add((0,0));E[1][0].add((0,0))
    def add(x):
        if x not in seen:
            if len(seen)>=cap:raise ValueError('cap')
            seen.add(x);todo.append(x)
    def root(a,l,r):
        x=(a,l,r)
        if x not in states:states.add(x);add((stop,a,(),l,(),r,fuel))
    def flush(d,P,i):
        for b in reversed(P):
            j=ds[d].push(i,b);e=(b,i)
            if e not in E[d][j]:
                E[d][j].add(e)
                for x in wait[d][j]: succ(x,b,i)
            i=j
        return i
    def succ(x,b,i):
        q,a,L,l,R,r,k=x;m=p[2*q+a];w=int(m[0]);d=m[1]=='R';q=ord(m[2])-65
        if d:y=(q,b,(w,)+L,l,(),i,k-1)
        else:y=(q,b,(),i,(w,)+R,r,k-1)
        add(y)
    root(0,0,0)
    while todo:
        x=todo.popleft();q,a,L,l,R,r,k=x
        if q==stop and k<fuel:
            nl=flush(0,L,l);nr=flush(1,R,r);root(a,nl,nr);continue
        if k==0:raise ValueError('fuel')
        m=p[2*q+a]
        if m=='---' or m=='HHH':raise ValueError('hole')
        w=int(m[0]);d=m[1]=='R';nq=ord(m[2])-65
        if d:
            if R:add((nq,R[0],(w,)+L,l,R[1:],r,k-1))
            else:
                wait[1][r].add(x)
                for b,i in E[1][r]:succ(x,b,i)
        else:
            if L:add((nq,L[0],L[1:],l,(w,)+R,r,k-1))
            else:
                wait[0][l].add(x)
                for b,i in E[0][l]:succ(x,b,i)
    return {'dfa':[d.finish() for d in ds],'states':len(states),'contexts':len(seen),'edges':sum(len(e) for g in E for e in g.values()),'roots':sorted(states),'incoming':[[sorted(g[i]) for i in range(len(ds[d].words))] for d,g in enumerate(E)]}
if __name__=='__main__':
    table=sys.argv[1];fuel=int(sys.argv[2]) if len(sys.argv)>2 else 12;stop=int(sys.argv[3]) if len(sys.argv)>3 else 0
    for D,P in [(Bits,k) for k in range(1,24)]+[(RunDFA,(k,c,c,m,m)) for k in range(1,6) for c in range(1,6) for m in range(1,6)]+[(Lag,(lag,c,m,k)) for lag in range(1,8) for k in range(1,5) for c in range(1,5) for m in range(1,5)]:
        try:
            v=discover(table,D,P,P,stop=stop,fuel=fuel,cap=150000);print('PASS',D.__name__,P,v['states'],v['contexts'],v['edges'],flush=True);v['method']=[D.__name__,P,P,stop,fuel];Path('macrodfa-witness.json').write_text(json.dumps(v));break
        except ValueError as e:
            if D==Bits: print('fail',P,e,flush=True)
    else:print('no certificate')
