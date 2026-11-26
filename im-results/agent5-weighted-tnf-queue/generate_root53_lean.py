"""Translate exact generated Coq root53 witness shards into Lean checked trees.
Usage: python generate_root53_lean.py rocq53 lean53
No result depends on trusting this parser or the MITM closure search.
"""
import re, sys
from pathlib import Path
from collections import Counter
from functools import lru_cache
src, out = map(Path, sys.argv[1:3]); out.mkdir(parents=True, exist_ok=True)
MOVES=[w+d+q for q in 'ABCDEF' for w in '01' for d in 'LR']
ROOT=tuple(re.findall(r'...', '1RB1RD1RC1RE0LA---1LA1LD------------'))
assert len(ROOT)==12
BANK=[[(0,1),(2,1),(2,1)],[(0,1),(2,3),(2,3),(2,3)]]
for k in [2,3,4]:
    N=2**k
    BANK.append([(2*i,2*i+1) if i<N else (N+2*((i-N)%(N//2)),N+2*((i-N)%(N//2))+1) for i in range(2*N)])
# Explicit prefix DFA states: node zero is the all-zero initial state.
assert BANK[2]==[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]
def run_dfa(cap, mod, depth):
    states=[()]; ids={():0}; dfa=[]
    for old in states:
        row=[]
        for b in (0,1):
            if not old and not b: s=()
            elif old and old[0][0]==b: s=((b,min(cap,old[0][1]+1),(old[0][2]+1)%mod),)+old[1:]
            else: s=((b,1,1%mod),)+old[:depth-1]
            if s not in ids: ids[s]=len(states); states.append(s)
            row.append(ids[s])
        dfa.append(tuple(row))
    return dfa
for args in [(1,2,1),(1,3,1),(1,4,1),(2,2,1),(2,3,1),(3,1,1),(2,1,2),(3,1,2),(1,2,2),(1,3,2),(2,2,2),(1,4,2),(1,2,3),(2,1,3),(3,2,1),(1,5,1),(1,6,1)]: BANK.append(run_dfa(*args))

def idx(s): return 2*('ABCDEF'.index(s[0]))+int(s[1])
def replace(tab,i,m): return tab[:i]+(m,)+tab[i+1:]
def bit(b): return 'true' if b else 'false'
def mv(m): return f'⟨{bit(m[0]=="1")},{bit(m[1]=="R")},{ord(m[2])-65}⟩'
def sl(i): return f'({i//2},{bit(i%2)})'
def arr(x): return '#['+','.join(x)+']'
def lst(x): return '['+','.join(x)+']'
def trie(xs):
    if not xs: return '.empty'
    if xs==[0]: return '.leaf'
    return f'(.branch {trie([x//2 for x in xs if x%2==0])} {trie([x//2 for x in xs if x%2==1])})'
def mitm(tab,L,R):
    ds=[L,R]; E=[[set() for _ in d] for d in ds]; W=[[[] for _ in d] for d in ds]
    seen=set(); rows=[]
    def add(q,a,l,r):
        st=(q,a,l,r)
        if st not in seen: seen.add(st); rows.append(st)
    def pop(st,e):
        q,a,l,r,n,d,w=st; b,i=e
        if d: add(n,b,L[l][w],i)
        else: add(n,b,i,R[r][w])
    assert L[0][0]==R[0][0]==0
    E[0][0].add((0,0)); E[1][0].add((0,0)); add(0,0,0,0)
    for q,a,l,r in rows:
        t=tab[2*q+a]; assert t!='---', (tab,L,R)
        w,d,n=int(t[0]),int(t[1]=='R'),ord(t[2])-65
        st=(q,a,l,r,n,d,w); old=l if d else r; edge=(w,old); dest=ds[1-d][old][w]
        if edge not in E[1-d][dest]:
            E[1-d][dest].add(edge)
            for waiter in W[1-d][dest]: pop(waiter,edge)
        target=r if d else l; W[d][target].append(st)
        for e in sorted(E[d][target]): pop(st,e)
    def stack(d,i):
        return '⟨'+arr(lst(f'({bit(b)},{k})' for b,k in sorted(es)) for es in E[i])+','+arr(f'({i},{j})' for i,j in d)+'⟩'
    rs=[trie(sorted(r+len(R)*l for q,a,l,r in rows if 2*q+a==i)) for i in range(12)]
    return '⟨'+stack(L,0)+','+stack(R,1)+','+arr(rs)+'⟩'

class Parser:
    def __init__(self,s): self.ts=re.findall(r'\w+|[\[\](),;%]',s); self.i=0
    def pop(self,x=None):
        t=self.ts[self.i]; self.i+=1
        if x is not None: assert t==x,(t,x,self.ts[self.i:self.i+8])
        return t
    def num(self): return int(self.pop())
    def vec(self):
        self.pop('['); a=[]
        while self.ts[self.i]!=']':
            a.append(self.num()); self.pop('%');self.pop('N')
            if self.ts[self.i]==';': self.pop(';')
        self.pop(']'); assert len(a)%2==0
        return list(zip(a[::2],a[1::2]))
    def node(self):
        op=self.pop()
        if op=='ATcoarse':
            self.pop('('); t=self.pop()
            if t=='CTpair': n=('p',self.num(),self.num())
            else:
                assert t=='CTw';self.pop('('); t=self.pop()
                if t=='SWside': n=('s',self.pop(),self.num(),self.num(),self.num())
                else: assert t=='SWlast'; n=('h',self.num())
                self.pop(')')
            self.pop(')');return n
        if op=='ATdfa': return ('d',self.vec(),self.vec())
        assert op=='auto_split',op
        n=self.num();self.pop('(');q=self.pop();self.pop(',');b=self.pop();self.pop(')');self.pop('[')
        kids=[]
        while self.ts[self.i]!=']':
            kids.append(self.node())
            if self.ts[self.i]==';': self.pop(';')
        self.pop(']');assert len(kids)==24
        return ('b',n,idx(q+b[1]),kids)

stats=Counter()
def emit(t,tab):
    op=t[0]; stats[op]+=1
    if op=='s': return f'.side {bit(t[1]=="R")} {t[2]} {t[3]} {t[4]}'
    if op=='h': return f'.last {t[1]}'
    if op in ('p','d'):
        L,R=(BANK[t[1]],BANK[t[2]]) if op=='p' else (t[1],t[2]); return '.pair '+mitm(tab,L,R)
    assert op=='b'; _,n,i,kids=t; assert tab[i]=='---'
    return f'.split {n} '+arr(emit(k,replace(tab,i,m)) for k,m in zip(kids,MOVES))

header='import Root53Tree\nopen BB6Coverage BB6.Agent13BlankDelay Root53Tree\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
base='def rootParent : PartialMachine := fun (q,b) => match q.val,b with\n'+''.join(f'  | {i//2},{bit(i%2)} => some (some {mv(m)})\n' for i,m in enumerate(ROOT) if m!='---')+'  | _,_ => none\n'
(out/'Root53ParentBase.lean').write_text(header+base)
# Preserve original theorem cuts. Each source certificate subtree is independently checked.
for f in sorted(src.glob('Agent5Q0Root53S*.v')):
    n=f.stem[-2:]; s=f.read_text(); tables={'auto_parent':ROOT}; lines=['import Root53ParentBase\n'+header.split('\n',1)[1]]
    # ordered definitions and theorem boundaries
    pattern=r'Definition (p_\w+) := tm_upd (\w+) \(([A-F]),S([01])\) \(S([01]),([LR]),([A-F])\)\.|Definition cert_(\w+) : auto_tree := (.*?)\.\n|Theorem safe_(\w+) : source_table_safe auto_bound (\w+)\.\nProof\.(.*?)Qed\.'
    certs=set()
    for m in re.finditer(pattern,s,re.S):
        if m[1]:
            name,prev,q,b,w,d,new=m.groups()[:7]; i=idx(q+b); mov=w+d+new
            assert tables[prev][i]=='---'
            tables[name]=replace(tables[prev],i,mov)
            lines.append(f'def {name} : PartialMachine := refine {"rootParent" if prev=="auto_parent" else prev} {sl(i)} (some {mv(mov)})\n')
        elif m[8]:
            name=m[8]; p=Parser(m[9]); t=p.node(); assert p.i==len(p.ts); certs.add(name)
            data=emit(t,tables['p_'+name]); lines.append(f'def cert_{name} : Tree := {data}\n')
        else:
            name,table,proof=m.groups()[9:12]; assert table=='p_'+name
            if name in certs:
                lines.append(f'theorem safe_{name} : Cover (WeightedBound 208) {table} :=\n  check_sound 208 6 {table} cert_{name} (by decide)\n')
            elif 'r53_safe' in proof:
                stats['c']+=1
                assert ''.join(tables[table])=='1RB1RD1RC1RE0LA0RC1LA1LD---1LF1LC0LE'
                lines.append(f'theorem safe_{name} : Cover (WeightedBound 208) {table} :=\n  check_sound 208 1 {table} .symbolic (by decide)\n')
            else:
                stats['b']+=1
                z=re.search(r'\(n:=(\d+)\) \(h:=\(([A-F]),S([01])\)\)',proof); assert z
                nsteps,q,b=z.groups(); i=idx(q+b)
                lines.append(f'theorem safe_{name} : Cover (WeightedBound 208) {table} := by\n  apply split_sound 208 {table} {nsteps} {sl(i)} (by decide)\n  intro mv\n  rcases mv with ⟨w,r,q⟩\n  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega\n  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases w <;> cases r\n'+''.join(f'  · exact safe_{name}_{j}\n' for j in range(24)))
    lines.append(f'#print axioms safe_r{int(n)}\n')
    (out/f'Root53ParentS{n}.lean').write_text('\n'.join(lines))
lines=[f'import Root53ParentS{j:02d}' for j in range(24)]+[header.split('\n',1)[1],'''theorem root53_parent_cover : Cover (WeightedBound 208) rootParent := by
  apply split_sound 208 rootParent 12 (4,true) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases w <;> cases r''']+[f'  · exact safe_r{j}' for j in range(24)]+['#print axioms root53_parent_cover\n']
(out/'Root53Parent.lean').write_text('\n'.join(lines))
stats['b']+=1
assert stats=={'s':18227,'p':5664,'b':1283,'h':5578,'d':40,'c':1}, stats
print(stats)
