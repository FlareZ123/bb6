"""Deterministic proof-candidate regeneration for Raw10 rectangle 33, B1=13, D0=2.
Reuses existing Box4 trace and reflective proof emitter with the correct domain.
Every generated leaf and branch is checked by Lean; unresolved leaves abort.
"""
from pathlib import Path
import argparse,json,os,shutil,subprocess,sys
from collections import Counter
from math import prod
HERE=Path(__file__).resolve().parent
BASE=HERE.parent/'agent13-raw10-box4'
BRANCH=HERE.parent/'agent13-raw10-box3-branches'
FIXED=[8,-1,11,13,1,13,2,-1,-1,-1,-1,-1]
TARGETS=(1,7,8,9,10,11)
BOUND=101
HARD={
 (8,20,11,13,1,13,2,23,4,0,2,21):'binary',
 (8,24,11,13,1,13,2,19,2,17,4,0):'binaryFlip',
 (8,24,11,13,1,13,2,23,0,10,4,20):'sweep',
 (8,20,11,13,1,13,2,19,4,24,0,10):'sweepFlip',
}
def call(*args):
    subprocess.run([str(x) for x in args],check=True)
def replace_once(s,a,b):
    assert s.count(a)==1,(a,s.count(a))
    return s.replace(a,b,1)
def prepare(work):
    fixed='int fx[6]={8,14,11,7,17,4};'
    domain='for(int i=0;i<12;i++){if(i<6)ds[i]={fx[i]};else if(i==target)ds[i]={0};else for(int v=1;v<=24;v++)if(i!=6||v!=9)ds[i].push_back(v);}'
    for n in ('scan.cpp','treegen.cpp'):
        s=(BASE/n).read_text()
        s=replace_once(s,fixed,'int fx[12]={'+','.join(map(str,FIXED))+'};')
        s=replace_once(s,domain,'for(int i=0;i<12;i++){if(fx[i]>=0)ds[i]={fx[i]};else if(i==target)ds[i]={0};else for(int v=1;v<=24;v++)ds[i].push_back(v);}')
        if n=='treegen.cpp':
            s=s.replace('for(int j=6;j<12;j++)','for(int j=0;j<12;j++)')
        (work/n).write_text(s)
    (work/'classify.cpp').write_text((BASE/'classify.cpp').read_text().replace('if(i!=6||v!=9)',''))
    shutil.copyfile(BRANCH/'rle_scan.cpp',work/'rle_scan.cpp')
    for n in ('scan','classify','treegen','rle_scan'):
        call('g++','-O3','-std=c++17',work/(n+'.cpp'),'-o',work/n)
def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--work',default='/tmp/raw10-box33-branch')
    args=ap.parse_args()
    work=Path(args.work).resolve();work.mkdir(parents=True,exist_ok=True)
    for pattern in ('open*.txt','ngram*.txt','hard*.txt','long*.json','tree*.txt','rlestart*.txt','rle*.txt','rlehard*.txt','greedyboxes.*','survivors.json'):
        for stale in work.glob(pattern):stale.unlink()
    os.chdir(work);prepare(work)
    sys.path[:0]=[str(BASE),str(BRANCH)]
    import finish,greedy
    from domain_lag_rle import run
    argv0=sys.argv;sys.argv=['emit_proof.py',str(HERE/'generated')]
    import emit_proof as emitter
    sys.argv=argv0
    Node=emitter.Node
    def domain_for(target):
        assert target in TARGETS
        return tuple((v,) if v>=0 else (0,) if i==target else tuple(range(1,25)) for i,v in enumerate(FIXED))
    finish.domain_for=domain_for
    greedy.BASE=[1<<v if v>=0 else (1<<25)-1 for v in FIXED]
    greedy.run=run
    greedy.HERE=work
    emitter.HERE=work
    emitter.OUT=HERE/'generated'
    shutil.rmtree(emitter.OUT,ignore_errors=True)
    emitter.OUT.mkdir(exist_ok=True)
    emitter.domain_for=domain_for
    oldwrite=emitter.write
    def write(name,imports,body):
        oldwrite(name.replace('Box4','Box33Branch'),
                 [x.replace('Box4','Box33Branch') for x in imports],
                 body.replace('Box4','Box33Branch').replace('3640','101'))
    emitter.write=write
    long={};stack=[];hard_seen=set();counts={}
    for target in TARGETS:
        call(work/'scan',target);call(work/'classify',target)
        pending=[tuple(map(int,l.split())) for l in open(f'hard{target}.txt') if l.strip()]
        initial_mass=sum(prod(len(domain_for(target)[i]) for i,v in enumerate(t) if v<0) for t in pending)
        terminal_mass=0;rlestart=[];counts[target]=Counter()
        while pending:
            t=pending.pop();z=finish.trace_long(t,limit=16384,cycle_limit=2048);kind=z[0]
            if kind=='hole':
                s=z[2];long[t]=('hole',s)
                pending.extend(t[:s]+(v,)+t[s+1:] for v in domain_for(target)[s]);continue
            terminal_mass+=prod(len(domain_for(target)[i]) for i,v in enumerate(t) if v<0)
            counts[target][kind]+=1
            if kind in ('halt','cycle','side'):
                if kind=='halt': assert z[1]+6<=BOUND,(t,z)
                long[t]=z
            else:rlestart.append(t)
        assert initial_mass==terminal_mass
        with open(f'rlestart{target}.txt','w') as f:
            for t in rlestart:f.write(' '.join(map(str,t))+'\n')
        call(work/'rle_scan',target)
        for l in open(f'rle{target}.txt'):
            v=list(map(int,l.split()));assert len(v)==21
            stack.append([v[:12],v[12:16],v[16:20]])
        for l in open(f'rlehard{target}.txt'):
            t=tuple(map(int,l.split()))
            assert t in HARD,(target,t,'unclosed: not a known symbolic leaf')
            hard_seen.add(t);long[t]=('known',HARD[t])
        print(target,dict(counts[target]),'long residual mass',initial_mass,flush=True)
    print('symbolic leaves used',sorted(hard_seen),flush=True)
    json.dump({'stack':stack,'block':[]},open(work/'survivors.json','w'))
    argv=sys.argv;sys.argv=['greedy.py'];greedy.main();sys.argv=argv
    for t in TARGETS:call(work/'treegen',t)
    boxes=emitter.bank_modules('B')
    masks=[tuple(e['mask']) for e in json.load(open('greedyboxes.json'))['boxes']]
    def late_node(t,target):
        for i,b in enumerate(masks):
            if greedy.subset(greedy.domain_mask(t),b):return Node(t,'a',(i,))
        w=long[t]
        if w[0]=='known':return Node(t,'known',('Box33BranchKnown','BB6.Agent13.Box33Branch.'+w[1]))
        if w[0]=='halt':return Node(t,'h',(w[1],))
        if w[0] in ('cycle','side'):return Node(t,'c',tuple(w[1:]))
        if w[0]=='hole':
            s=w[1]
            return Node(t,'b',(s,),[(v,late_node(t[:s]+(v,)+t[s+1:],target)) for v in domain_for(target)[s]])
        raise ValueError((t,w))
    def load(target):
        ds=domain_for(target);root=tuple(d[0] if len(d)==1 else -1 for d in ds)
        f=iter(open(f'tree{target}.txt'))
        def parse(t):
            line=next(f).split();k=line[0];a=tuple(map(int,line[1:]))
            if k=='b':
                s=a[0];return Node(t,'b',a,[(v,parse(t[:s]+(v,)+t[s+1:])) for v in ds[s]])
            if k=='o':
                assert a==t
                return late_node(t,target)
            return Node(t,k,a)
        result=parse(root);assert next(f,None) is None
        return result
    for t in TARGETS:emitter.tree_modules(t,load(t),boxes)
    emitter.write('Box33BranchClosure',[f'Box33BranchSlice{t}' for t in TARGETS],'''namespace BB6.Agent13.Box33Branch
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box
theorem allSlices : ∀ t : Fin 12, (t = 1 ∨ 7 ≤ t.val) → Good t (root t) := by
  intro t ht
  have h : t = 1 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11 := by omega
  rcases h with h|h|h|h|h|h <;> subst t
  · exact slice1
  · exact slice7
  · exact slice8
  · exact slice9
  · exact slice10
  · exact slice11
theorem sourceBound : ∀ m, Fits sourceDomain m → WeightedBound 101 m :=
  source_upper allSlices
#print axioms sourceBound
end BB6.Agent13.Box33Branch
''')
    print('generated all six branch slices; source check still required',flush=True)
if __name__=='__main__':main()
