"""Generate a source-checked partition of a five-hole Raw10 Box27 slice.

Discovery is untrusted. Lean checks all transition, cycle, automaton and
exhaustiveness obligations independently. Run from any directory.
"""
from collections import defaultdict, Counter
from pathlib import Path
import json

def gram(k):
    return 0,lambda x,b: ((x<<1)|b)&((1<<k)-1)

def rle(n,cap,mod):
    def push(x,b):
        bit,runs=x
        if bit!=b:return (b,(1,)+runs[:n-1])
        j=runs[0]
        if j==0:return x
        return (b,(j+1 if j<cap+mod-1 else cap,)+runs[1:])
    return (0,(0,)),push

def learn(row,desc,limit=5000):
    initial,P=desc
    tab=[[initial],[initial]];ids=[{initial:0},{initial:0}];D=[{},{}]
    def dfa(d,i,b):
        k=(i,b)
        if k in D[d]:return D[d][k]
        y=P(tab[d][i],b);j=ids[d].get(y)
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

# Same discovery order as the locally executed run; later candidates not needed.
SPECS=[gram(1),gram(2),rle(1,1,1),rle(1,1,2),gram(3),rle(1,2,1),rle(1,2,2),gram(4),gram(5)]
ROOT=[8,-1,11,-1,13,13,14,17,21,-1,-1,-1]
B=108
stats=Counter();certs=[];attainers=[];maxweight=0
def delay(row):
    def f(path):
        t=path[-1];opts=[]
        for q in range(6):
            if q in path:continue
            a=row[2*q]
            if a<0 or (a>0 and ((a-1)>>1)&1==0 and (a-1)>>2==t):opts.append(f(path+[q]))
        return max(opts,key=len) if opts else path
    return f([0])

def weight(row,n):
    global maxweight,attainers
    p=delay(row);w=n+len(p)
    if w>maxweight:maxweight=w;attainers=[]
    if w==maxweight:attainers.append((row,n,p))

def simulate(row,N=120):
    q=h=l=r=0;hist=[]
    for t in range(N+1):
        i=2*q+(l&1);a=row[i]
        if a<0:return ('hole',i,t)
        if not a:return ('halt',t)
        lo=hi=h
        for j in range(t-1,-1,-1):
            q0,h0,l0,r0=hist[j];lo=min(lo,h0);hi=max(hi,h0)
            if q0!=q:continue
            if h>=h0 and r==r0 and ((l^l0)&((1<<(h0-lo+1))-1))==0:return ('cycle',j,t-j,True,lo)
            if h<=h0 and l==l0 and ((r^r0)&((1<<(hi-h0))-1))==0:return ('cycle',j,t-j,False,hi)
        hist.append((q,h,l,r))
        n=a-1;w=(n>>1)&1;q=n>>2
        if n&1:l=((l>>1)<<2)|(w<<1)|(r&1);r>>=1;h+=1
        else:l>>=1;r=(r<<1)|w;h-=1
    return ('timeout',)

def visit(row):
    stats['nodes']+=1;mass=25**row.count(-1)
    v=simulate(row)
    if v[0]=='halt':
        weight(row,v[1]);stats['halt']+=1;stats['halt_mass']+=mass;return list(v)
    if v[0]=='hole':
        i,t=v[1:]
        if row.count(-1)==1 and all(a!=0 for a in row):
            stats['last']+=1;stats['last_mass']+=mass
            weight(row[:i]+[0]+row[i+1:],t)
            return ['last',i,t]
        stats['branch']+=1
        return ['branch',i,[[a,visit(row[:i]+[a]+row[i+1:])] for a in range(25)]]
    if v[0]=='cycle':
        stats['cycle']+=1;stats['cycle_mass']+=mass;return list(v)
    for desc in SPECS:
        c=learn(row,desc)
        if c is not None:
            i=len(certs);certs.append(dict(row=row,cert=c));stats['cert']+=1;stats['cert_mass']+=mass
            return ['cert',i]
    raise RuntimeError(('open',row))

def trie(xs):
    if not xs:return '.empty'
    if xs==[0]:return '.leaf'
    return '(.branch '+trie([x//2 for x in xs if x%2==0])+' '+trie([x//2 for x in xs if x%2==1])+')'
def arr(xs):return '#['+', '.join(xs)+']'
def boolean(b):return 'true' if b else 'false'
def stack(c,d):
    edges=arr(['['+', '.join('('+boolean(b)+', '+str(i)+')' for b,i in row)+']' for row in c['edges'][d]])
    pushes=arr(['('+str(a)+', '+str(b)+')' for a,b in c['pushes'][d]])
    return '⟨'+edges+', '+pushes+'⟩'
def cert(c):
    rows=[[] for _ in range(12)]
    for q,b,l,r in c['seen']:rows[2*q+b].append(r+len(c['edges'][1])*l)
    return '⟨'+stack(c,0)+', '+stack(c,1)+', '+arr([trie(sorted(set(x))) for x in rows])+'⟩'
def term(t):
    tag,*v=t
    if tag=='halt':return '.terminal (.halt '+str(v[0])+')'
    if tag=='last':return '.terminal (.last '+str(v[0])+' '+str(v[1])+')'
    if tag=='cycle':
        e,p,r,b=v
        return f'.terminal (.cycle {e} {p} {boolean(r)} ({b}))'
    if tag=='cert':return '.automata '+cert(certs[v[0]]['cert'])
    if tag=='branch':
        s,k=v
        return '.branch '+str(s)+' ['+',\n'.join('('+str(a)+', '+term(t)+')' for a,t in k)+']'
    raise ValueError(t)
def size(t):return 1+sum(size(c) for _,c in t[2]) if t[0]=='branch' else 1

def emit(tree):
    out=Path(__file__).resolve().parent
    mods=[];buf=[];count=0;serial=0
    head='set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace BB6.Agent49.Box27Slice\nopen BB6Coverage BB6.Agent13BlankDelay\nopen BB6.Agent13.Box17 (decode slot)\n'
    def flush():
        nonlocal buf,count
        if not buf:return
        name=f'Box27SlicePart{len(mods):03d}'
        (out/(name+'.lean')).write_text('import Box27SliceCore\n'+head+'\n'.join(buf)+'\nend BB6.Agent49.Box27Slice\n')
        mods.append(name);buf=[];count=0
    joins=[]
    def go(t,p):
        nonlocal serial,count
        i=serial;serial+=1;n=f'g{i}'
        if size(t)<=126:
            if count+size(t)>250:flush()
            buf.append(f'def p{i} : PartialMachine := {p}\ndef t{i} : Tree := {term(t)}\ntheorem c{i} : audit {B} 5 p{i} t{i} = true := by decide\ntheorem {n} : Good {B} p{i} := audit_sound {B} 5 p{i} t{i} c{i}\n')
            count+=size(t);return n
        assert t[0]=='branch'
        s,k=t[1:]
        names=[go(c,f'(refine {p} (slot {s}) (decode {a}))') for a,c in k]
        assert [a for a,_ in k]==list(range(25))
        js=f'theorem {n} : Good {B} {p} := by\n  apply split_good {B} {p} {s}\n  intro v\n  have hv : '+' ∨ '.join(f'v = {a}' for a in range(25))+' := by omega\n  rcases hv with '+'|'.join(['rfl']*25)+'\n'+''.join('  · exact '+x+'\n' for x in names)
        joins.append(js);return n
    name=go(tree,'root');flush()
    source=''.join('import '+m+'\n' for m in mods)+head+ '\n'.join(joins)
    source+='\ntheorem bound : Good 108 root := '+name+'\n'
    source+='''theorem parent_bound (m : Machine) (hm : BB6.Agent49Box.Fits BB6.Agent49BoxBridge.raw10Remainder[27]! m)
    (hd0 : m (3,false) = decode 14) (hd1 : m (3,true) = decode 17)
    (he : m (4,false) = decode 21) : WeightedBound 108 m :=
  bound m (parent_compatible m hm hd0 hd1 he)

def attainerTable : PartialMachine := fun s =>
  some (decode ([8,4,11,24,13,13,14,17,21,15,3,0] : List (Fin 25))[BB6.Agent13.Box17.index s]!)
def attainer : Machine := fun s => (attainerTable s).getD none
theorem attainer_compatible : compatible attainerTable attainer := by
  intro s t ht
  simp [attainer,ht]
theorem attainer_halts : HaltsAfter attainer 107 :=
  BB6.Agent13.Box17.zipHalt_sound attainerTable 107 (by decide) attainer attainer_compatible
theorem attainer_in_slice : compatible root attainer := by
  intro s t ht
  obtain ⟨q,b⟩ := s
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> simp [root] at ht ⊢ <;>
    first | subst t; decide | contradiction

/-- Exact weighted maximum over the five-hole physical cylinder.
    A valid halting trace at score 108 witnesses sharpness. -/
theorem exact_weighted (B : Nat) :
    (∀ m, compatible root m → WeightedBound B m) ↔ 108 ≤ B := by
  constructor
  · intro h
    have hd : 0 ∈ delays (zeroNext attainer) 0 := by decide
    have hb := h attainer attainer_in_slice 107 0 attainer_halts hd
    omega
  · intro h m hm k d hk hd
    have hb := bound m hm k d hk hd
    omega

#print axioms bound
#print axioms parent_bound
#print axioms attainer_halts
#print axioms attainer_in_slice
#print axioms exact_weighted
end BB6.Agent49.Box27Slice
'''
    (out/'Box27SliceSource.lean').write_text(source)

if __name__=='__main__':
    tree=visit(ROOT)
    assert maxweight==108 and len(certs)==41
    assert stats==dict(nodes=2526,branch=101,halt=101,halt_mass=432725,cycle=1959,cycle_mass=9321375,last=324,last_mass=8100,cert=41,cert_mass=3425),stats
    assert attainers==[([8,4,11,24,13,13,14,17,21,15,3,0],107,[0])]
    print(stats, maxweight, attainers)
    emit(tree)
