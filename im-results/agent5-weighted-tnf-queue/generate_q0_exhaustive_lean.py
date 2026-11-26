import argparse, json, re
from pathlib import Path
from collections import Counter
from q0_trace_emit import module as trace_module

MOVES=[w+d+q for q in 'ABCDEF' for w in '01' for d in 'LR']
BANK=[[(0,1),(2,1),(2,1)],[(0,1),(2,3),(2,3),(2,3)]]
for k in [2,3,4]:
    N=2**k
    BANK.append([(2*i,2*i+1) if i<N else (N+2*((i-N)%(N//2)),N+2*((i-N)%(N//2))+1) for i in range(2*N)])
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

def load(src):
    if src.is_file():
        manifest=json.loads(src.read_text())
        tab=tuple(re.findall(r'.{3}',manifest['table'].replace('_','')))
        def convert(t):
            if t[0]=='h' and t[3]: return ('b',t[1],t[2],list(map(convert,t[3])))
            return tuple(t[:2]) if t[0]=='h' else tuple(t)
        return manifest,tab,convert(manifest['tree'])
    manifest=json.loads((src/'q0-auto-candidate.json').read_text())
    rid=manifest['rootId']; tab=tuple(re.findall(r'.{3}',manifest['table'].replace('_','')))
    trees={}; tabs={'auto_parent':tab}
    pattern=r'Definition (p_\w+) := tm_upd (\w+) \(([A-F]),S([01])\) \(S([01]),([LR]),([A-F])\)\.|Definition cert_(\w+) : auto_tree := (.*?)\.\n|Theorem safe_(\w+) : source_table_safe auto_bound (\w+)\.\nProof\.(.*?)Qed\.'
    for name in manifest['modules']:
        for m in re.finditer(pattern,(src/(name+'.v')).read_text(),re.S):
            a,b,q,bit_,w,d,q2,c,body,s,p,proof=m.groups()
            if a:
                assert tabs[b][idx(q+bit_)]=='---'
                tabs[a]=replace(tabs[b],idx(q+bit_),w+d+q2)
            elif c:
                parser=Parser(body); trees[c]=parser.node(); assert parser.i==len(parser.ts)
            elif s not in trees:
                if 'r53_safe' in proof: trees[s]=('c',)
                else:
                    n,q,b=re.search(r'\(n:=(\d+)\) \(h:=\(([A-F]),S([01])\)\)',proof).groups()
                    trees[s]=('b',int(n),idx(q+b),[trees[s+'_'+str(i)] for i in range(24)])
    n,q,b=re.search(r'\(n:=(\d+)\) \(h:=\(([A-F]),S([01])\)\)',(src/'Agent5Q0AutoData.v').read_text()).groups()
    return manifest,tab,('b',int(n),idx(q+b),[trees['r'+str(i)] for i in range(24)])

def size(t): return 1+sum(map(size,t[3])) if t[0]=='b' else 1

def long_traces(t,tab):
    if t[0]=='h' and t[1]>512:
        yield tab,t[1]
    elif t[0]=='b':
        for k,m in zip(t[3],MOVES):
            yield from long_traces(k,replace(tab,t[2],m))

def emit(t,tab,stats):
    k=t[0];stats[k]+=1
    if k=='s': return f'.side {bit(t[1]=="R")} {t[2]} {t[3]} {t[4]}'
    if k=='h': return '.symbolic' if t[1]>512 else f'.last {t[1]}'
    if k=='p': return '.pair '+mitm(tab,BANK[t[1]],BANK[t[2]])
    if k=='d': return '.pair '+mitm(tab,t[1],t[2])
    if k=='c': return '.symbolic'
    _,n,i,kids=t; assert tab[i]=='---'
    return f'.split {n} '+arr(emit(k,replace(tab,i,m),stats) for k,m in zip(kids,MOVES))

def splitproof(p,t,name,childnames,B):
    _,n,i,_=t
    lines=[f'theorem safe_{name} : Cover (WeightedBound {B}) {p} := by',f'  apply split_sound {B} {p} {n} {sl(i)} (by decide +kernel)','  intro mv','  rcases mv with ⟨w,r,q⟩','  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega','  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases w <;> cases r']
    lines += ['  · exact safe_'+c for c in childnames]
    return '\n'.join(lines)+'\n'

def generate(src,out,chunk):
    manifest,tab,tree=load(src);rid=manifest['rootId'];B=manifest['bound'];ns=f'Q0Root{rid}';out.mkdir(exist_ok=True,parents=True)
    assert size(tree)==manifest['stats']['nodes']
    pre='set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nopen BB6Coverage BB6.Agent13BlankDelay Q0ExhaustiveTree\n'
    lines=['import Q0ExhaustiveTree']
    if rid in (53,56): lines+=[f'import Root{rid}Coverage']
    lines+=[pre,'namespace '+ns,'def rootParent : PartialMachine := fun (q,b) => match q.val,b with']
    lines += [f'  | {i//2}, {bit(i%2)} => some (some {mv(m)})' for i,m in enumerate(tab) if m!='---']
    lines += ['  | _, _ => none']
    if rid in (53,56): lines += [f'def sym (p : PartialMachine) : Bool := sameTable p Root{rid}Coverage.table{rid}',f'theorem sym_sound (p : PartialMachine) (h : sym p = true) : Cover (WeightedBound {B}) p := by',f'  have he : p = Root{rid}Coverage.table{rid} := sameTable_sound h','  subst p',f'  exact Root{rid}Coverage.weighted {B}']
    else: lines+=['def sym (_ : PartialMachine) : Bool := false',f'theorem sym_sound (p : PartialMachine) (h : sym p = true) : Cover (WeightedBound {B}) p := by contradiction']
    (out/(ns+'Base.lean')).write_text('\n'.join(lines+['end '+ns])+'\n')
    stats=Counter();stats['b']+=1
    traces=list(long_traces(tree,tab))
    if traces: trace_module(rid,B,traces,out/(ns+'Long.lean'))
    def prove(t,tab,p,name,lines,sym_name):
        if size(t)<=chunk:
            expr=emit(t,tab,stats)
            lines.append(f'def cert_{name} : Tree := {expr}')
            lines.append(f'theorem safe_{name} : Cover (WeightedBound {B}) {p} := check_sound {B} {sym_name} {sym_name}_sound 6 {p} cert_{name} (by decide +kernel)')
        else:
            stats['b']+=1;_,n,i,kids=t;assert tab[i]=='---'
            names=[name+'_'+str(j) for j in range(24)]
            for m,k,cn in zip(MOVES,kids,names):
                cp='p_'+cn;lines.append(f'def {cp} := refine {p} {sl(i)} (some {mv(m)})');prove(k,replace(tab,i,m),cp,cn,lines,sym_name)
            lines.append(splitproof(p,t,name,names,B))
    _,n,i,kids=tree
    modules=[]
    for j,(m,k) in enumerate(zip(MOVES,kids)):
        name='r'+str(j);p='p_'+name;mod=ns+'Shard'+str(j);modules.append(mod)
        lines=['import '+ns+'Base',pre,'namespace '+ns,f'def {p} := refine rootParent {sl(i)} (some {mv(m)})']
        has_long=any(long_traces(k,replace(tab,i,m)))
        if has_long: lines.insert(1,'import '+ns+'Long')
        prove(k,replace(tab,i,m),p,name,lines,'longSym' if has_long else 'sym');lines+=['#print axioms safe_'+name,'end '+ns]
        (out/(mod+'.lean')).write_text('\n'.join(lines)+'\n')
    lines=['import '+m for m in modules]+[pre,'namespace '+ns,splitproof('rootParent',tree,'root',['r'+str(j) for j in range(24)],B),'#print axioms safe_root','end '+ns]
    (out/(ns+'Parent.lean')).write_text('\n'.join(lines)+'\n')
    assert sum(stats.values())==size(tree),stats
    print(rid, B, dict(stats),sum(stats.values()))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('src',type=Path);p.add_argument('out',type=Path);p.add_argument('--chunk',type=int,default=49);a=p.parse_args();generate(a.src,a.out,a.chunk)
