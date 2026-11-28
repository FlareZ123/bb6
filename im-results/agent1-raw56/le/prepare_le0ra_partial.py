#!/usr/bin/env python3
"""Source-generate a canonical Raw56 E1=0LE/E0=0RA partial frontier.

Closes 3,866 of 3,881 exact canonical open leaves with original-source FAR,
finite-stack DFA, late finite cuts, and three periodic-stack motif certificates.
The other fifteen leaves remain explicitly unresolved. All generated claims
are conditional until the original Lean kernel and axiom gate accept them.
"""
from __future__ import annotations
import base64,gzip,hashlib,itertools,json,subprocess,sys
from pathlib import Path
import emit_rc_rd as src
import prepare_le0lb as pre

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
AGENT=HERE.parent
CUT=ROOT/'im-results/agent7-raw49/cut.cpp'
FAR=ROOT/'im-results/agent19-raw40-cut/farbank.cpp'
DISC=AGENT/'discover_abstract_pinned.js'
BIDFA=ROOT/'im-results/agent32-raw59'
OFFSET=4811
COUNT=3881
BOUND=7014
PARENT='1RB---_1RC---_0RD---_1LD1LE_0RA0LE_------'
NS='BB6.Agent1Raw56.LE0RAPartial'
MOD='Raw56LE0RAPartial'
HARD={6209,6259,6286,6304,6337,6341,6416,6966,7174,7294,
      7862,7863,8472,8477,8515,8537,8552,8558}
MOTIFS={6286,6304,7174}
UNRESOLVED=HARD-MOTIFS

def sha(data,expected):
    got=hashlib.sha256(data).hexdigest()
    assert got==expected,(got,expected)

def generated(args):
    out=Path(args[0]).resolve()
    out.mkdir(parents=True,exist_ok=True)
    inv=json.loads(gzip.decompress(base64.b64decode((HERE/'inventory-79.json.gz.b64').read_text())))
    assert {i for i in inv['remaining'] if OFFSET<=i<OFFSET+COUNT}==HARD
    late=[r for r in inv['late'] if OFFSET<=r[0]<OFFSET+COUNT]
    assert len(late)==3 and {r[0] for r in late}=={4922,4944,7157}
    assert all((r[1]=='last' and r[2]<BOUND) or (r[1]=='cycle' and r[2]+r[3]<BOUND) for r in late)
    assert not any(OFFSET<=row[0]<OFFSET+COUNT for row in inv['sat'])
    extra={i:c for c,ds in inv['fmore'] for i in itertools.accumulate(ds)}
    abstract={i:p for p,ds in inv['abs'] for i in itertools.accumulate(ds)}
    for path,h in [
      (CUT,'88d5dfc4994f8bd203fe3f3def5ea90efda86037'),
      (FAR,'30cac1862b3b88d7ba596b359a9dc8503163593d'),
      (DISC,'8fe2ac5d02e9809ea27904da010833e24b331ad9'),
      (BIDFA/'emit_rungram.py','e11a06c9daf6720ee537e6d2dea27daba20d6723'),
      (BIDFA/'FastBiDFA.lean','6d31e7e2f081eac524a9c7bb8bd33e55bc1dfd7f'),
      (AGENT/'emit_rc_rd.py','f6753bf0e6368a66eadb148d5df61d491068e54a'),
    ]:pre.blob(path,h)
    for name,p in [('cut',CUT),('farbank',FAR)]:
        subprocess.run(['g++','-std=c++20','-O3',str(p),'-o',str(out/name)],check=True)
    stem=out/'0RA'
    subprocess.run([str(out/'cut'),PARENT,'1000','32','6',str(stem)],check=True)
    treefile=openfile=farfile=None
    treefile=stem.with_suffix('.json')
    openfile=stem.with_suffix('.open')
    farfile=stem.with_suffix('.far')
    rows=openfile.read_text().splitlines()
    assert len(rows)==len(set(rows))==COUNT
    tree=json.loads(treefile.read_text())
    print('PINNED_0RA_TREE_SHA256',hashlib.sha256(treefile.read_bytes()).hexdigest(),flush=True)
    print('PINNED_0RA_OPEN_SHA256',hashlib.sha256(openfile.read_bytes()).hexdigest(),flush=True)
    inp=''.join(f"{i} {t.replace('_','')}\n" for i,t in enumerate(rows)).encode()
    with farfile.open('wb') as f:
        subprocess.run([str(out/'farbank'),'5'],input=inp,stdout=f,check=True)
    print('PINNED_0RA_FAR_SHA256',hashlib.sha256(farfile.read_bytes()).hexdigest(),flush=True)
    bankfile=stem.with_suffix('.bank')
    bankfile.write_bytes(farfile.read_bytes()+''.join(f'{i-OFFSET} {c}\n' for i,c in sorted(extra.items()) if OFFSET<=i<OFFSET+COUNT).encode())
    bank={int(x.split()[0]):x.split()[1] for x in bankfile.read_text().splitlines()}
    assert len(bank)==len(bankfile.read_text().splitlines())
    assert len(bank)==3608,(len(bank),COUNT)

    gen=out/'0RAgen'
    gen.mkdir(exist_ok=True)
    sys.path.insert(0,str(BIDFA))
    from emit_rungram import emit
    from motif_quotient import minimize
    queries=[dict(id=i-OFFSET,table=rows[i-OFFSET],p=p) for i,p in sorted(abstract.items())
             if OFFSET<=i<OFFSET+COUNT]
    assert len(queries)==252
    reply=subprocess.check_output(['node',str(HERE/'le_replay.cjs'),str(DISC)],
                                  input=json.dumps(queries).encode())
    dfa=json.loads(reply)
    proven={}
    mods=[]
    for record in dfa:
        i=record['id']
        assert record['table']==rows[i] and i not in bank
        module=f'Raw56LE0RABiDFA{i}'
        namespace=f'BB6.Agent1Raw56.LE0RABiDFA{i}'
        d,g,states=minimize(record['table'],record['dfa'])
        assert len(states)<=record['states'] and sum(map(len,g))+2<=record['edges']
        code='\n'.join(['import FastBiDFA','set_option maxRecDepth 100000',
          'set_option maxHeartbeats 0',f'namespace {namespace}',
          'open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1NGram BB6.Agent32FastBiDFA',
          emit(i,record['table'],*d,[len(states),sum(map(len,g))+2]),f'end {namespace}',''])
        (gen/(module+'.lean')).write_text(code)
        mods.append(module)
        proven[i]=namespace+f'.M{i}'
    fullopen=out/'global-le'
    subprocess.run([str(out/'cut'),'1RB---_1RC---_0RD---_1LD1LE_---0LE_------',
                    '1000','32','7',str(fullopen)],check=True)
    sha(fullopen.with_suffix('.open').read_bytes(),'aba63f28439c707c3343fd4ff53f66717d5924b88b1aa8012947f6039e0da7ef')
    subprocess.run([sys.executable,str(HERE/'prepare_motif.py'),
      str(fullopen.with_suffix('.open')),str(gen),str(6286),str(7174)],check=True)
    subprocess.run([sys.executable,str(HERE/'prove_motif_6304.py'),str(gen)],check=True)
    motifmods=[f'Raw56LEMotif{i}' for i in sorted(MOTIFS)]
    for g in MOTIFS:
        assert rows[g-OFFSET] in (next((r['table'] for r in json.loads((HERE/'motif_spec.json').read_text())
                                      if r['id']==g),rows[g-OFFSET]),),g
        proven[g-OFFSET]=f'BB6.Agent1Raw56.LEMotif.M{g}'
    lateproof={}
    for r in late:
        i=r[0]-OFFSET
        if r[1]=='last':
            lateproof[i]=f'.last {r[2]} ({r[3]//2},{str(bool(r[3]%2)).lower()})'
        else:
            assert r[1]=='cycle' and r[4] in (0,1)
            lateproof[i]=f'.cycle {r[2]} {r[3]} {str(bool(r[4])).lower()} ({r[5]})'
    unexplained={i-OFFSET for i in UNRESOLVED}
    covered=set(bank)|set(proven)|set(lateproof)|unexplained
    assert len(covered)==COUNT and covered==set(range(COUNT)),(
       COUNT-len(covered),set(range(COUNT))-covered)
    assert len(set(bank))+len(set(proven))+len(set(lateproof))+len(unexplained)==COUNT
    print('CLASSIFICATION',len(bank),len(proven),len(lateproof),len(unexplained),flush=True)
    emitter=PartialEmitter(rows,tree,bank,proven,lateproof,unexplained,gen,mods+motifmods)
    emitter.write()
    print('COMPOSED_MODULES',len(emitter.manifest),'RESIDUALS',len(unexplained),flush=True)

class PartialEmitter:
    def __init__(self,rows,tree,bank,proven,lateproof,unresolved,out,leafmods):
        self.rows=rows;self.tree=tree;self.bank=bank;self.proven=proven
        self.lateproof=lateproof;self.unresolved=unresolved
        self.unresolvedTables={rows[i] for i in unresolved}
        self.out=out;self.leafmods=leafmods
        self.manifest=[]
        self.it=iter(enumerate(rows))
        self.parent=src.parse(PARENT)
        self.cut=src.support(self.parent)
        assert self.cut==5
        self.moduleIndex=0
        self.lines=[]
        self.weight=0
        self.current=None

    def emit(self,module,imports,lines):
        imports=list(dict.fromkeys(imports))
        head=f'''set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {NS}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial BB6.Agent47CanonicalFrontier
'''
        text=''.join(f'import {im}\n' for im in imports)+head+'\n'.join(lines)+f'\nend {NS}\n'
        (self.out/(module+'.lean')).write_text(text)
        self.manifest.append([module,imports])

    def open_leaf(self,tab):
        i,s=next(self.it)
        assert s==tab,(i,s,tab)
        return i

    def ordinary(self,t,p):
        kind=t[0]
        if kind=='cycle':
            return f'.cycle {t[1]} {t[2]} {str(bool(t[3])).lower()} ({t[4]})'
        if kind=='last':
            return f'.last {t[1]} {src.slot(t[2])}'
        if kind=='open':
            i=self.open_leaf(src.show(p))
            assert i not in self.unresolved,i
            if i in self.lateproof:return self.lateproof[i]
            if i in self.proven:
                n=self.proven[i]
                return f'.proven {n}.table {n}.never'
            assert i in self.bank,i
            return src.far(self.bank[i],p)
        assert kind=='split',t[:3]
        n,s,kids=t[1:]; assert len(kids)==24
        return f'.split {n} {src.slot(s)} (byMove [\n'+',\n'.join(
            self.ordinary(k,p[:s]+[src.move(i)]+p[s+1:])
            for i,k in enumerate(kids))+'])'

    def has_open(self,t):
        if t[0]=='open':return t[1] in self.unresolvedTables
        if t[0]=='split':return any(self.has_open(k) for k in t[3])
        return False

    def partial(self,t,p,cut):
        typ=t[0]
        if typ=='open':
            if t[1] in self.unresolvedTables:
                i=self.open_leaf(src.show(p))
                assert i in self.unresolved,i
                return '.unresolved'
            return f'.closed ({self.ordinary(t,p)})'
        if typ!='split' or (cut==6 and not self.has_open(t)):
            return f'.closed ({self.ordinary(t,p)})'
        n,s,kids=t[1:]
        return f'.split {n} {src.slot(s)} (byPartialMove [\n'+',\n'.join(
            self.partial(k,p[:s]+[src.move(i)]+p[s+1:],max(cut,i%6+1))
            for i,k in enumerate(kids))+'])'

    def cases(self):
        return '''  rcases m with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
'''

    def combine(self,name,n,s,cut,names):
        lines=[f'def k{name} : Move → PartialAudit := byPartialMove [{",".join("t"+x for x in names)}]',
               f'def t{name} : PartialAudit := .split {n} {src.slot(s)} k{name}',
               f'theorem q{name} : zipQueryOK {BOUND} p{name} {n} {src.slot(s)} = true := by decide']
        ck=f'''theorem ck{name} (m : Move) : (if m.next.val ≤ {cut} then canonicalCheck {BOUND} (refine p{name} {src.slot(s)} (some m)) (max {cut} (m.next.val+1)) (k{name} m) else true) = true := by
'''+self.cases()
        for q in range(6):
            for w in range(2):
                for r in range(2):
                    nm=names[12*w+6*r+q]
                    ck+=f'  · exact c{nm}\n'
        lines.extend([ck.rstrip(),f'''theorem c{name} : canonicalCheck {BOUND} p{name} {cut} t{name} = true := by
  simp only [t{name},canonicalCheck,q{name},Bool.true_and]
  exact allMoves_of _ ck{name}'''])
        return lines

    def shard(self,t,p,cut,name,expr,lines):
        lines.append(f'abbrev p{name} := {expr}')
        if src.size(t)<=96:
            lines += [f'def t{name} : PartialAudit := {self.partial(t,p,cut)}',
                      f'theorem c{name} : canonicalCheck {BOUND} p{name} {cut} t{name} = true := by decide +kernel']
            return
        n,s,kids=t[1:]
        names=[]
        for i,k in enumerate(kids):
            nm=f'{name}_{i:02}'
            names.append(nm)
            self.shard(k,p[:s]+[src.move(i)]+p[s+1:],max(cut,i%6+1),
                nm,f'refine p{name} {src.slot(s)} (some {src.mv(i)})',lines)
        lines.extend(self.combine(name,n,s,cut,names))

    def new_module(self):
        self.moduleIndex+=1
        return f'{MOD}Part{self.moduleIndex:03}'

    def flush(self):
        if self.current:self.emit(self.current,[MOD+'Base'],self.lines)
        self.lines=[];self.weight=0;self.current=None

    def visit(self,t,p,cut,name,expr):
        sz=src.size(t)
        if sz<=600:
            if self.current and self.weight+sz>600:self.flush()
            if not self.current:self.current=self.new_module()
            self.shard(t,p,cut,name,expr,self.lines)
            self.weight+=sz
            return self.current
        n,s,kids=t[1:]
        names=[];imports=[]
        for i,k in enumerate(kids):
            nm=f'{name}_{i:02}'
            names.append(nm)
            imports.append(self.visit(k,p[:s]+[src.move(i)]+p[s+1:],max(cut,i%6+1),
                nm,f'refine ({expr}) {src.slot(s)} (some {src.mv(i)})'))
        self.flush()
        mod=self.new_module()
        self.emit(mod,imports,[f'abbrev p{name} := {expr}']+self.combine(name,n,s,cut,names))
        return mod

    def write(self):
        base=['def p : PartialMachine := fun s => match s.1.val,s.2 with']
        for i,v in enumerate(self.parent):
            if v!='---':
                w,r,q=int(v[0]),v[1]=='R',ord(v[2])-65
                base.append(f'  | {i//2},{str(bool(i%2)).lower()} => some (some ⟨{str(bool(w)).lower()},{str(r).lower()},{q}⟩)')
        base += ['  | _,_ => none',
           'theorem root : p initialSlot = some (some ⟨true,true,1⟩) := by decide',
           '''theorem nohalt : weightedTNFNoAssignedHalt p := by
  intro s; rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide''',
           f'theorem supported : TNFSupport p {self.cut} := supportOK_sound _ _ (by decide)']
        self.emit(MOD+'Base',['Raw40Nores',*self.leafmods],base)
        t=self.tree
        n,s,kids=t[1:]
        names=[];imports=[]
        for i,k in enumerate(kids):
            nm=f'_{i:02}'
            names.append(nm)
            imports.append(self.visit(k,self.parent[:s]+[src.move(i)]+self.parent[s+1:],
                max(self.cut,i%6+1),nm,f'refine p {src.slot(s)} (some {src.mv(i)})'))
        self.flush()
        try:
            next(self.it)
            raise AssertionError('canonical residual traversal did not consume all rows')
        except StopIteration:
            pass
        final=['abbrev ptop := p']+self.combine('top',n,s,self.cut,names)+[
f'''def remaining15 := canonicalResiduals p {self.cut} ttop
theorem count15 : remaining15.length = 15 := by decide
theorem sound15 : ∀ m, TNFQuotientCompatible p m →
      WeightedBound {BOUND} m ∨
        ∃ e ∈ remaining15, TNFQuotientCompatible e.2 m := by
  intro m hm
  exact canonicalSound {BOUND} p {self.cut} ttop (by decide) supported root nohalt ctop m hm
#print axioms count15
#print axioms sound15''']
        self.emit(MOD+'All',imports,final)
        self.manifest=[[x,['FastBiDFA']] for x in self.leafmods]+self.manifest
        (self.out/'manifest.json').write_text(json.dumps(self.manifest,indent=2)+'\n')

if __name__=='__main__':
    generated(sys.argv[1:])
