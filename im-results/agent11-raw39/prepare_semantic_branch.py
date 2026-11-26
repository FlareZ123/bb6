#!/usr/bin/env python3
"""Deterministically emit a source-audited normalized first-hole proof.
The generator and C++ search results are untrusted: each leaf, split,
weight, state-support claim, and semantic join is checked by Lean.
"""
import argparse,base64,hashlib,json,lzma,subprocess
from collections import Counter,defaultdict,deque
from itertools import product
from pathlib import Path

ROOT=Path(__file__).resolve().parent

def run(*a,**kw):return subprocess.run([str(x) for x in a],check=True,**kw)
def sha(b):return hashlib.sha256(b).hexdigest()
def bs(x):return str(bool(x)).lower()
def arr(xs):return '#['+','.join(xs)+']'
def trie(xs):
    xs=set(xs)
    if not xs:return '.empty'
    if xs=={0}:return '.leaf'
    return '(.branch '+trie(x//2 for x in xs if x%2==0)+' '+trie(x//2 for x in xs if x%2)+')'

def table_decl(table):
    p=table.replace('_','');out=['def table : PartialMachine := fun s =>','  match s.1.val,s.2 with']
    for j in range(12):
        m=p[3*j:3*j+3]
        if m!='---':out.append(f'  | {j//2},{bs(j%2)} => some (some ⟨{bs(m[0]=="1")},{bs(m[1]=="R")},{ord(m[2])-65}⟩)')
    return out+['  | _,_ => none']

def closure_proof(checker):
    return ['theorem checked : check table cert = true := by','  apply check_of_rows','  · decide','  · decide','  · decide','  · intro q a','    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega','    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases a',*[f'    · exact row_checked{j}' for j in range(12)],f'theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := {checker}.never table cert checked m hm','#print axioms never']

def asym_emit(line,tables):
    i,L,R,n,eL,eR,ss=line.split();i,L,R,n=map(int,(i,L,R,n));rows=defaultdict(list)
    for s in map(int,ss.strip(',').split(',')):
        r=s%(1<<R);l=(s>>R)%(1<<L);q=s>>(R+L);rows[q].append(r+(l<<R))
    assert sum(map(len,rows.values()))==n
    def edges(s):return [2*x+d for t in s.strip(',').split(',') for x,v in [map(int,t.split(':'))] for d in (0,1) if v&(1<<d)]
    out=[f'namespace M{i}',*table_decl(tables[i]),f'def leftGraph : Trie := {trie(edges(eL))}',f'def rightGraph : Trie := {trie(edges(eR))}']
    for j in range(12):out.append(f'def row{j} : Trie := {trie(rows[j])}')
    out.append(f'def cert : Cert := ⟨{L-1},{R-1},leftGraph,rightGraph,#['+','.join('row'+str(j) for j in range(12))+']⟩')
    for j in range(12):out.append(f'theorem row_checked{j} : (row cert {j//2} {bs(j%2)}).all (fun i => stateStepOK table cert {j//2} {bs(j%2)} (i/2^(cert.nR+1)) (i%2^(cert.nR+1))) = true := by decide')
    return '\n'.join(out+closure_proof('BB6.Agent32AsymNGram')+[f'end M{i}']),[i,L,R,n]

def rungram_emit(i,table,dl,dr,expected):
    d=[dl,dr];p=table.replace('_','');p=[p[j:j+3] for j in range(0,36,3)]
    edges=[defaultdict(set),defaultdict(set)];wait=[defaultdict(list),defaultdict(list)]
    seen={(0,0,0,0)};todo=deque(seen)
    for e in edges:e[0].add((0,0))
    def add(q,a,l,r):
        s=(q,a,l,r)
        if s not in seen:seen.add(s);todo.append(s)
    def pop(s,b,src):
        q,a,l,r=s;m=p[2*q+a];w,drct,n=int(m[0]),m[1],ord(m[2])-65
        if drct=='R':add(n,b,d[0][2*l+w],src)
        else:add(n,b,src,d[1][2*r+w])
    while todo:
        s=todo.popleft();q,a,l,r=s;m=p[2*q+a];assert m!='---'
        w,drct,n=int(m[0]),m[1],ord(m[2])-65
        side=int(drct=='R');dest=d[1-side][2*(l if side else r)+w];old=l if side else r
        e=(w,old)
        if e not in edges[1-side][dest]:
            edges[1-side][dest].add(e)
            for st in wait[1-side][dest]:pop(st,*e)
        x=r if side else l;wait[side][x].append(s)
        for b,y in edges[side][x]:pop(s,b,y)
    assert (len(seen),sum(len(v) for es in edges for v in es.values()))==expected
    out=[f'namespace M{i}',*table_decl(table)]
    for name,d,es in zip(['leftGraph','rightGraph'],[dl,dr],edges):
        pred=arr('['+','.join(f'({bs(b)},{y})' for b,y in sorted(es[x]))+']' for x in range(len(d)//2))
        out.append(f'def {name} : Graph := ⟨{arr(map(str,d))},{pred}⟩')
    rs=defaultdict(set)
    for q,a,l,r in sorted(seen):rs[q*2+a,l].add(r)
    for s in range(12):out.append(f'def row{s} : Array Trie := '+arr(trie(rs[s,l]) for l in range(len(dl)//2)))
    out.append('def cert : BB6.Agent32FastBiDFA.Cert := ⟨leftGraph,rightGraph,'+arr(f'row{s}' for s in range(12))+'⟩')
    for s in range(12):out.append(f'theorem row_checked{s} : rowCheck table cert {s//2} {bs(s%2)} = true := by decide')
    return '\n'.join(out+closure_proof('BB6.Agent32FastBiDFA')+[f'end M{i}'])

def move(i):return f'⟨{bs(i>=12)},{bs(i%12>=6)},{i%6}⟩'
def slot(s):return f'({s//2},{bs(s%2)})'
def refine(p,s,i):return f'(refine {p} {slot(s)} (some {move(i)}))'

class Node:
    def __init__(self,raw,p,cut,index,idx=()):
        self.tag,*self.v=raw;self.p=p;self.cut=cut;self.idx=idx;self.kids=[]
        if self.tag=='split':
            n,s,ks=self.v
            self.kids=[Node(k,refine(p,s,i),max(cut,i%6+1),index,idx+(i,)) for i,k in enumerate(ks) if i%6<=cut]
        elif self.tag=='open':self.i=index[self.v[0]]
        self.size=1+sum(k.size for k in self.kids)
        self.name='b'+'_'.join(map(str,idx)) if idx else 'allChild'
    def leaves(self):
        if self.tag=='open':yield self.i
        for k in self.kids:yield from k.leaves()

class Builder:
    def __init__(self,out,branch,B,limit,far,special):
        self.out=out;self.branch=branch;self.B=B;self.limit=limit;self.far=far;self.special=special;self.modules=[];self.stats=Counter();self.owner={}
        self.prefix='Raw39'+branch;self.base=self.prefix+'Base';self.ns='BB6.Agent11Raw39'+branch
    def emit(self,name,imports,body):
        h=''.join('import '+x+'\n' for x in sorted(set(imports)))+f'''set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {self.ns}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent10CachedAudit BB6.Agent11SemanticChunks
'''
        (self.out/(name+'.lean')).write_text(h+body+f'\nend {self.ns}\n')
    def render(self,t,imports):
        self.stats[t.tag]+=1
        if t.tag=='cycle':
            e,k,r,b=t.v;return f'.cycle {e} {k} {bs(r)} ({b})'
        if t.tag=='last':
            n,s=t.v;return f'.last {n} {slot(s)}'
        if t.tag=='open':
            if t.i in self.special:
                mod,tab,proof=self.special[t.i];imports.add(mod);return f'.proven ({tab}) ({proof})'
            return self.far[t.i]
        assert t.tag=='split' and len(t.kids)==24
        n,s,_=t.v
        return f'.split {n} {slot(s)} (byMove [\n'+',\n'.join(self.render(k,imports) for k in t.kids)+'])'
    def small(self,t):return t.size<=self.limit and (t.cut>=5 or t.tag!='split')
    def bound_leaf(self,t,imports):
        return f'''theorem {t.name} : Bound {self.B} {t.p} := by
  let t : Audit := {self.render(t,imports)}
  exact bound_of_cached {self.B} {t.p} t (by decide) (by rfl)
'''
    def compose(self,t):
        n,s,_=t.v;byid={k.idx[-1]:k.name for k in t.kids}
        lines=[f'theorem {t.name} : Bound {self.B} {t.p} := by',f'  apply join_normalized {self.B} {t.cut} {t.p} {n} {slot(s)} (by decide) (by rfl) (by decide) (by rfl)','  intro mv hv','  rcases mv with ⟨w,r,q⟩','  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega','  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl','  all_goals cases w <;> cases r']
        for q,w,r in product(range(6),range(2),range(2)):
            i=12*w+6*r+q;lines.append('  · exact '+byid[i] if i in byid else f'  · exact False.elim ((by decide : ¬ ({q} : Nat) ≤ {t.cut}) hv)')
        self.stats['join']+=1;return '\n'.join(lines)+'\n'
    def write(self,ts,body,imports,size):
        name=self.prefix+'Chunk'+f'{len(self.modules):03}';self.emit(name,imports|{self.base},body)
        self.modules.append([name,size,sorted(imports|{self.base})])
        for t in ts:self.owner[t.name]=name
        return name
    def build(self,t):
        if self.small(t):
            imports=set();return self.write([t],self.bound_leaf(t,imports),imports,t.size)
        imports=set();group=[];size=0;body=[]
        def flush():
            nonlocal imports,group,size,body
            if group:self.write(group,'\n'.join(body),imports,size)
            imports=set();group=[];size=0;body=[]
        for k in t.kids:
            if self.small(k):
                if size+k.size>4000:flush()
                group.append(k);size+=k.size;body.append(self.bound_leaf(k,imports))
            else:self.build(k)
        flush();imports={self.owner[k.name] for k in t.kids}
        return self.write([t],self.compose(t),imports,1)

def main():
    from prepare_raw39 import masks,parse
    ap=argparse.ArgumentParser();ap.add_argument('branch',choices=['1LB']);ap.add_argument('--work',type=Path);ap.add_argument('--out',type=Path,default=ROOT);ap.add_argument('--limit',type=int,default=1200);args=ap.parse_args()
    branch='LB';prefix='Raw39'+branch;spec=json.loads((ROOT/'lb-witnesses.json').read_text());p=(args.work or ROOT/'_build1LBsemantic').resolve();p.mkdir(parents=True,exist_ok=True);out=args.out.resolve();out.mkdir(parents=True,exist_ok=True)
    source=ROOT.parent/'agent11-raw121';asym_src=ROOT.parent/'agent32-raw59'/'ngram_asym.cpp'
    run('g++','-std=c++17','-O3',source/'fast_enum.cpp','-o',p/'enum');run(p/'enum',spec['child'],cwd=p)
    run('g++','-std=c++20','-O3',source/'bank.cpp','-o',p/'bank');run('g++','-std=c++17','-O3',asym_src,'-o',p/'ngram_asym')
    assert sha((p/'open.txt').read_bytes())==spec['open_sha256'];assert sha((p/'tree.json').read_bytes())==spec['tree_sha256']
    opens=(p/'open.txt').read_text().splitlines();index={s:i for i,s in enumerate(opens)};assert len(index)==len(opens)==5915
    root=Node(json.loads((p/'tree.json').read_text()),'pLB',4,index);ids=set(root.leaves());assert root.size==203557 and len(ids)==2959
    special={};data=lzma.decompress(base64.b64decode((ROOT/'Raw39LBProofs.json.xz.b64').read_text()));assert sha(data)==spec['proof_source_sha256']
    for name,code in json.loads(data).items():
        assert Path(name).name==name and name.startswith(prefix) and name.endswith('.lean');(out/name).write_text(code)
    # Only canonical representatives, selected independently by the exact tree.
    for i,j in spec['pairs']:
        assert i in ids and j not in ids
        kind='Width' if i in spec['width'] else 'Affine'
        if i==spec['rungram']['index']:kind='RunGram'
        mod=prefix+kind+str(i);ns='BB6.Agent11'+prefix+kind+'.M'+str(i);special[i]=(mod,ns+'.table',ns+'.never')
    rg=spec['rungram'];i=rg['index'];assert opens[i].replace('_','')==rg['table'];ns='BB6.Agent11'+prefix+'RunGram'
    code=rungram_emit(i,opens[i],*rg['dfa'],(rg['states'],rg['edges']))
    (out/(prefix+'RunGram'+str(i)+'.lean')).write_text(f'import FastBiDFA\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace {ns}\nopen BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1NGram BB6.Agent32FastBiDFA\n'+code+f'\nend {ns}\n')
    inp=''.join(f'{i} {opens[i]} {L} {R}\n' for i,L,R,n in spec['asym']);res=run(p/'ngram_asym',input=inp,text=True,capture_output=True);assert not res.stderr,res.stderr
    certs=sorted((asym_emit(line,opens) for line in res.stdout.splitlines()),key=lambda x:x[1][0]);assert [m for _,m in certs]==sorted(spec['asym'])
    groups=[];grp=[];n=0
    for c,meta in certs:
        if grp and n+meta[3]>2000:groups.append(grp);grp=[];n=0
        grp.append((c,meta));n+=meta[3]
    if grp:groups.append(grp)
    ns='BB6.Agent11'+prefix+'Asym'
    for j,g in enumerate(groups):
        mod=prefix+f'Asym{j:02}';(out/(mod+'.lean')).write_text(f'import AsymNGram\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace {ns}\nopen BB6Coverage\nopen BB6.Agent1NGram (Trie)\nopen BB6.Agent32AsymNGram\n'+'\n'.join(c for c,_ in g)+f'\nend {ns}\n')
        for _,(i,*_) in g:
            t=f'{ns}.M{i}';special[i]=(mod,t+'.table',t+'.never')
    todo=ids-special.keys();assert len(todo)==2860 and len(ids&special.keys())==99
    bank=spec['bank'];(p/'bank.txt').write_text('\n'.join(bank)+'\n');inp=''.join(f'{i} {opens[i].replace("_","")}\n' for i in sorted(todo))
    res=run(p/'bank',p/'bank.txt',input=inp,capture_output=True,text=True);assert not res.stderr,res.stderr
    found={int(i):a for i,a in (line.split() for line in res.stdout.splitlines())};assert set(found)==todo
    far={}
    for i,a in found.items():
        d,D,L,R,z=masks(parse(opens[i]),int(a[0]),[int(c,36) for c in a[1:]])
        far[i]=f'.far {bs(int(a[0]))} {d} ⟨0,{D},{L},{R},{z}⟩'
    b=Builder(out,branch,spec['bound'],args.limit,far,special);root.name='all1LB'
    b.emit(b.base,['Raw39SemanticChunks'],'''abbrev p39 : PartialMachine :=
  refine (pathEnd root 2 (path.take 3)).1 (3,true) (some ⟨false,true,0⟩)
abbrev pLB : PartialMachine := refine p39 (0,true) (some ⟨true,false,1⟩)
''');top=b.build(root);b.emit(prefix+'Complete',[top],'#print axioms all1LB\n')
    # Greedy weighted packing of the independent checking modules. Parent
    # composition modules are tiny and built only by the final assembly.
    leaves=[(name,size) for name,size,deps in b.modules if size>1 or not any(x.startswith(prefix+'Chunk') for x in deps)]
    groups={f'g{i}':[] for i in range(8)};weights=dict.fromkeys(groups,0)
    for name,size in sorted(leaves,key=lambda x:-x[1]):
        g=min(weights,key=weights.get);groups[g].append(name);weights[g]+=size
    manifest={'root':prefix+'Complete','groups':groups,'weights':weights,'modules':b.modules,'stats':dict(b.stats),'normalized_nodes':root.size,'open_count':len(ids)}
    (out/'shards-LBsemantic.json').write_text(json.dumps(manifest,indent=2)+'\n');print('chunks',len(b.modules),'weights',weights,'stats',b.stats,flush=True)
if __name__=='__main__':main()
