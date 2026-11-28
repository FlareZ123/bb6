"""Untrusted discovery/emission for exact E/F-quotiented six-hole certificates."""
from pathlib import Path
from collections import Counter,defaultdict,deque
import sys
from generate_slice import simulate,cert,boolean
ROOT=[8,-1,11,-1,13,13,-1,-1,-1,-1,-1,-1]

def gram(k):return 0,lambda x,b: ((x<<1)|b)&((1<<k)-1)
def rle(n,cap,mod):
    def push(x,b):
        bit,runs=x
        if bit!=b:return (b,(1,)+runs[:n-1])
        j=runs[0]
        if j==0:return x
        return (b,(j+1 if j<cap+mod-1 else cap,)+runs[1:])
    return (0,(0,)),push

def learn(row,desc,limit=5000,other=None):
    initial,P=desc;initialR,PR=other or desc
    tab=[[initial],[initialR]];ids=[{initial:0},{initialR:0}];D=[{},{}];push=[P,PR]
    def dfa(d,i,b):
        k=(i,b)
        if k in D[d]:return D[d][k]
        y=push[d](tab[d][i],b);j=ids[d].get(y)
        if j is None:j=len(tab[d]);tab[d].append(y);ids[d][y]=j
        D[d][k]=j;return j
    edges=[defaultdict(set),defaultdict(set)];wait=[defaultdict(list),defaultdict(list)]
    for e in edges:e[0].add((0,0))
    seen={(0,0,0,0)};todo=[(0,0,0,0)];failure=False;capped=False
    def add(x):
        nonlocal failure,capped
        if x not in seen:
            seen.add(x);todo.append(x)
            if row[2*x[0]+x[1]]<=0:failure=True
            if len(todo)>=limit:capped=True
    def pop(x,edge,pushed):
        q,b,l,r=x;m=row[2*q+b]-1;s=m>>2;c,pre=edge
        if m&1:add((s,c,pushed,pre))
        else:add((s,c,pre,pushed))
    def addEdge(d,x,b,pre):
        if (b,pre) in edges[d][x]:return
        e=(b,pre);edges[d][x].add(e)
        for c,j in wait[d][x]:
            pop(c,e,j)
            if failure or capped:return
    i=0
    while i<len(todo) and not failure and not capped:
        c=todo[i];i+=1;q,b,l,r=c;m=row[2*q+b]-1;w=(m>>1)&1;d=not(m&1)
        if m<0:failure=True;break
        x=(r if d else l);j=dfa(d,x,w);addEdge(d,j,w,x)
        z=l if d else r;wait[1-d][z].append((c,j))
        for e in edges[1-d][z]:
            pop(c,e,j)
            if failure or capped:break
    if failure or capped:return None
    return dict(edges=[[sorted(edges[d][k]) for k in range(len(tab[d]))] for d in (0,1)],pushes=[[[D[d].get((k,b),0) for b in (0,1)] for k in range(len(tab[d]))] for d in (0,1)],seen=sorted(seen))

def specs():
    return [('g'+str(k),gram(k)) for k in [1,2,3,4,5,6,7]]+[(f'r{n},{cap},{mod}',rle(n,cap,mod)) for n in [1,2,3] for cap in [1,2,3,4] for mod in [1,2,3]]

def solve(row):
    for name,desc in specs():
        c=learn(row,desc)
        if c:return name,c
    return None,None

def simulate_long(row,N=20000,window=256):
    q=h=l=r=0;hist=[];seen={};byq=[deque(maxlen=window) for _ in range(6)]
    for t in range(N+1):
        i=2*q+(l&1);a=row[i]
        if a<0:return ('last' if row.count(-1)==1 and 0 not in row else 'hole',i,t)
        if not a:return ('halt',t)
        key=(q,l,r);j=seen.get(key)
        if j is not None:
            right=h>=hist[j][1];bound=(min if right else max)([h]+[x[1] for x in hist[j:t]]);return ('cycle',j,t-j,right,bound)
        seen[key]=t
        if t and t%4==0:
            lo=hi=h;prev=t
            for j in reversed(byq[q]):
                if t-j>4*window:break
                for k in range(prev-1,j-1,-1):lo=min(lo,hist[k][1]);hi=max(hi,hist[k][1])
                prev=j;q0,h0,l0,r0=hist[j]
                if h>=h0 and r==r0 and ((l^l0)&((1<<(h0-lo+1))-1))==0:return ('cycle',j,t-j,True,lo)
                if h<=h0 and l==l0 and ((r^r0)&((1<<(hi-h0))-1))==0:return ('cycle',j,t-j,False,hi)
        hist.append((q,h,l,r));byq[q].append(t)
        n=a-1;w=(n>>1)&1;q=n>>2
        if n&1:l=((l>>1)<<2)|(w<<1)|(r&1);r>>=1;h+=1
        else:l>>=1;r=(r<<1)|w;h-=1
    return ('timeout',)

def rescue(row):
    w=simulate_long(row,2000,64)
    if w[0]!='timeout':return w,None
    base=specs();extra=[(f'g{k}',gram(k)) for k in [8,9,10]]+[(f'r{n},{c},{m}',rle(n,c,m)) for n in [1,2,3,4] for c in [1,2,3,4,5,6] for m in [1,2,3,4] if n>3 or c>4 or m>3]
    for name,d in extra:
        c=learn(row,d,20000)
        if c:return ('far',name),c
    pool=base[:7]+[(n,d) for n,d in base[7:] if n.startswith('r1,') or n.startswith('r2,1,') or n.startswith('r2,2,')]
    for n1,d1 in pool:
        for n2,d2 in pool:
            if n1==n2:continue
            c=learn(row,d1,10000,d2)
            if c:return ('far',n1+';'+n2),c
    return ('timeout',),None

def rename(v):return v+4 if 17<=v<=20 else v-4 if 21<=v<=24 else v
def sym(row,s):return s<8 and all(row[i]==rename(row[i^2 if i>=8 else i]) for i in range(12))
HARD=(8,17,11,2,13,13,14,18,23,-1,3,21)

def discover(d,s,v):
    root=ROOT.copy();root[6]=d;root[s]=v
    stats=Counter();maxhalt=0
    def visit(row,weight):
        nonlocal maxhalt
        stats['nodes']+=1;mass=weight*25**row.count(-1)
        w=simulate(row,120)
        if w[0]=='timeout':
            key=tuple(row)
            if key==HARD: w=['known',0]
            else:
                _,c=solve(key)
                if c is not None:w=['far',c]
                else:
                    u,c=rescue(key)
                    if u[0]=='far':w=['far',c]
                    elif u[0]!='timeout':
                        w=simulate(row,2000)
                        if w[0]=='hole' and row.count(-1)==1 and 0 not in row:w=['last',w[1],w[2]]
                        if w[0]=='timeout':raise RuntimeError(('rescue mismatch',key,u))
                    else:raise RuntimeError(('unresolved',key))
        tag=w[0]
        if tag=='hole':
            i,t=w[1:]
            if row.count(-1)==1 and 0 not in row:
                maxhalt=max(maxhalt,t);stats['last']+=1;stats['last_mass']+=mass;return ['last',i,t]
            orbit=sym(row,i);stats['orbit' if orbit else 'branch']+=1
            return ['orbit' if orbit else 'branch',i,[visit(row[:i]+[j]+row[i+1:],weight*(2 if orbit and j>=17 else 1)) for j in range(21 if orbit else 25)]]
        if tag in ('halt','last'):maxhalt=max(maxhalt,w[-1])
        stats[tag]+=1;stats[tag+'_mass']+=mass;return list(w)
    t=visit(root,1);assert sum(stats[k] for k in ('halt_mass','cycle_mass','last_mass','far_mass','known_mass'))==25**6
    print(d,s,v,dict(stats),'max live halt',maxhalt,flush=True);return t,max(255,maxhalt+6)

def emit(d,s,v,tree,B,out,limit=251,partlimit=600):
    prefix=f'Box27Orbit{d:02d}V{v:02d}';ns=f'BB6.Agent49.{prefix}';out=Path(out);out.mkdir(parents=True,exist_ok=True)
    head=f'set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace {ns}\nopen BB6Coverage BB6.Agent13BlankDelay\nopen BB6.Agent49.Box27Slice (Good split_good)\nopen BB6.Agent49.Box27OrbitTree (Tree audit audit_sound split_ef_good representative)\nopen BB6.Agent13.Box17 (decode slot)\n'
    def size(t):return 1+sum(size(c) for c in t[2]) if t[0] in ('branch','orbit') else 1
    def term(t):
        tag,*a=t
        if tag=='halt':return f'.terminal (.halt {a[0]})'
        if tag=='last':return f'.terminal (.last {a[0]} {a[1]})'
        if tag=='cycle':return f'.terminal (.cycle {a[0]} {a[1]} {boolean(a[2])} ({a[3]}))'
        if tag=='known':return f'.terminal (.cert {a[0]})'
        if tag=='far':return '.automata '+cert(a[0])
        i,k=a;return f'.{tag} {i} ['+',\n'.join(f'({j}, {term(u)})' for j,u in enumerate(k))+']'
    core=prefix+'Core';imports='import Box27OrbitTree\nimport Box27EarlyTerminal\n'
    known='def known : Array PartialMachine := #[]\ntheorem knownGood (i : Nat) (q : PartialMachine) (h : known[i]? = some q) : Good '+str(B)+' q := by simp [known] at h\n'
    if (d,v)==(14,18):
        imports+='import Box27D14V18Alternating\n';known=f'''def known : Array PartialMachine := #[BB6.Agent49.Box27D14V18Alternating.p]
theorem knownGood (i : Nat) (q : PartialMachine) (h : known[i]? = some q) : Good {B} q := by
  cases i with
  | zero =>
    have he : BB6.Agent49.Box27D14V18Alternating.p = q := by simpa [known] using h
    rw [← he]
    exact BB6.Agent49.Box27D14V18Alternating.bound {B}
  | succ i => simp [known] at h
'''
    (out/(core+'.lean')).write_text(imports+head+f'def base : PartialMachine := refine (BB6.Agent49.Box27EarlyTerminal.base {d}) (slot {s}) (decode {v})\n'+known+f'end {ns}\n')
    parts=[];buf=[];count=0;serial=0;joins=[]
    def flush():
        nonlocal buf,count
        if not buf:return
        name=f'{prefix}Part{len(parts):04d}';parts.append(name)
        (out/(name+'.lean')).write_text('import '+core+'\n'+head+'\n'.join(buf)+f'\nend {ns}\n');buf=[];count=0
    def go(t,p):
        nonlocal serial,count
        i=serial;serial+=1;n=f'g{i}';z=size(t)
        if z<=limit:
            if count+z>partlimit:flush()
            buf.append(f'def p{i} : PartialMachine := {p}\ndef t{i} : Tree := {term(t)}\ntheorem c{i} : audit {B} known 6 p{i} t{i} = true := by decide\ntheorem {n} : Good {B} p{i} := audit_sound {B} known knownGood 6 p{i} t{i} c{i}\n');count+=z;return n
        tag,sl,k=t;names=[go(c,f'(refine {p} (slot {sl}) (decode {j}))') for j,c in enumerate(k)];orbit=tag=='orbit'
        intro=f'  apply split_ef_good {B} {p} {sl} (by decide)\n  intro v hr\n  have hle : v.val ≤ 20 := of_decide_eq_true hr\n' if orbit else f'  apply split_good {B} {p} {sl}\n  intro v\n'
        joins.append(f'theorem {n} : Good {B} {p} := by\n'+intro+'  have hv : '+' ∨ '.join(f'v = {j}' for j in range(len(k)))+' := by omega\n  rcases hv with '+'|'.join(['rfl']*len(k))+'\n'+''.join('  · exact '+x+'\n' for x in names));return n
    name=go(tree,'base');flush()
    source=''.join('import '+p+'\n' for p in parts)+'import Box27CanonicalFrontier\n'+head+'\n'.join(joins)+f'\ntheorem bound : Good {B} base := {name}\n'
    source+=f'''theorem source_bound (m : Machine) (hm : BB6.Agent49.Box27CanonicalFrontier.child {d} {v} m) : WeightedBound {B} m := by
  rcases hm with ⟨hf,hd,hv⟩
  apply bound m
  unfold base
  change m (slot {s}) = decode {v} at hv
  rw [← hv]
  exact compatible_refine _ m _ (BB6.Agent49.Box27EarlyTerminal.base_compatible {d} m hf hd)
#print axioms bound
#print axioms source_bound
end {ns}
'''
    (out/(prefix+'Source.lean')).write_text(source);print(prefix,len(parts),serial,len(joins),flush=True)
if __name__=='__main__':
    d,s,v=map(int,sys.argv[1:4]);t,B=discover(d,s,v);emit(d,s,v,t,B,sys.argv[4])
