"""Complete source proof generator for a retained Raw10 rectangle-33 child.
The computation may fail on a hard machine, in which case no source bound is emitted.
Never use untrusted discovery counts as a proof; compile the generated closure.
"""
from pathlib import Path
import argparse,json,os,shutil,subprocess,sys
from collections import Counter
from math import prod
HERE=Path(__file__).resolve().parent
BASE=HERE.parent/'agent13-raw10-box4'
BRANCH=HERE.parent/'agent13-raw10-box3-branches'
FIXED=None
TARGETS=None
BOUND=None
HARD_D14V17={
    (8,24,11,6,1,13,14,17,3,11,4,0): 'm0',
    (8,14,11,24,1,13,14,17,3,15,4,0): 'm1',
    (8,24,11,6,1,13,14,17,12,11,4,0): 'm2',
    (8,24,11,6,1,13,14,17,24,11,4,0): 'm3',
    (8,10,11,7,1,13,14,17,24,21,4,0): 'm4',
    (8,10,11,7,1,13,14,17,24,23,4,0): 'm5',
    (8,0,11,24,1,13,14,17,22,9,19,4): 'b0',
    (8,0,11,24,1,13,14,17,22,17,19,4): 'b1',
}
HARD_D14V18={
    (8,10,11,7,1,13,14,18,3,24,0,4): 'm0',
    (8,1,11,24,1,13,14,18,3,0,6,18): 'm1',
    (8,10,11,24,1,13,14,18,7,3,0,4): 'm2',
}
HARD={}
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
def make_core(out,family,d,v):
    core=(HERE/'Box33BranchCore.lean').read_text()
    tree=(HERE/'Box33BranchTree.lean').read_text()
    start=core.index('/-- B1=0LD')
    end=core.index('def sliceDomain',start)
    rows=''.join(f'  | {i} => [{x}]\n' for i,x in enumerate(FIXED) if x>=0)
    spec=f"""def literalDomain (i : Fin 12) : List (Fin 25) :=
  match i.val with
{rows}  | _ => List.finRange 25

def domain : Box Slot Transition := fun s => (literalDomain (index s)).map decode
def sourceDomain : Box Slot Transition := fun s =>
  match Box33D0.child {d} {v} s with
  | none => choices
  | some t => [t]

theorem sourceDomainEq : domain = sourceDomain := by
  funext s
  rcases s with ⟨q,b⟩
  revert q b
  decide

theorem source_compatible (m : Machine) (hm : compatible (Box33D0.child {d} {v}) m) :
    Fits sourceDomain m := by
  intro s
  unfold sourceDomain
  cases hs : Box33D0.child {d} {v} s with
  | none => exact choices_complete _
  | some t => simp [hm s t hs]

def haltTargets : List (Fin 12) := {list(TARGETS)}

"""
    core=core[:start]+spec+core[end:]
    core='import Box33D0Cut\n'+core
    core=core.replace('(t = 1 ∨ 7 ≤ t.val)','t ∈ haltTargets').replace('t = 1 ∨ 7 ≤ t.val','t ∈ haltTargets').replace('¬ (i = 1 ∨ 7 ≤ i.val)','i ∉ haltTargets')
    core=core.replace('Box33Branch',family).replace('101',str(BOUND))
    tree=tree.replace('Box33Branch',family).replace('101',str(BOUND))
    (out/(family+'Core.lean')).write_text(core)
    (out/(family+'Tree.lean')).write_text(tree)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--d0',type=int,required=True)
    ap.add_argument('--second',type=int,required=True)
    ap.add_argument('--bound',type=int,required=True)
    ap.add_argument('--work')
    args=ap.parse_args()
    global FIXED,TARGETS,BOUND,HARD
    d,v,BOUND=args.d0,args.second,args.bound
    if (d,v) in {(12,14),(12,16),(14,12),(14,18),(17,21),(17,22),(17,23),(17,24)}:
        from replay_direct import run_direct
        return run_direct(args)
    slot={2:3,3:3,4:3,12:1,14:7,16:7,17:8,18:8,19:8,20:8}[d]
    assert 1<=v<=24 and BOUND>=11
    family=f'Box33D{d}V{v}'
    HARD=HARD_D14V17 if (d,v)==(14,17) else {}
    FIXED=[8,-1,11,-1,1,13,d,-1,-1,-1,-1,-1]
    FIXED[slot]=v
    TARGETS=tuple(i for i,x in enumerate(FIXED) if x<0)
    out=HERE/'generated'/family
    work=Path(args.work or f'/tmp/raw10-{family}').resolve();work.mkdir(parents=True,exist_ok=True)
    for pattern in ('open*.txt','ngram*.txt','hard*.txt','long*.json','tree*.txt','rlestart*.txt','rle*.txt','rlehard*.txt','greedyboxes.*','survivors.json'):
        for stale in work.glob(pattern):stale.unlink()
    os.chdir(work);prepare(work)
    sys.path[:0]=[str(BASE),str(BRANCH)]
    import finish,greedy
    from domain_lag_rle import run
    argv0=sys.argv;sys.argv=['emit_proof.py',str(out)]
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
    emitter.OUT=out
    shutil.rmtree(emitter.OUT,ignore_errors=True)
    emitter.OUT.mkdir(exist_ok=True)
    emitter.domain_for=domain_for
    make_core(out,family,d,v)
    oldwrite=emitter.write
    def write(name,imports,body):
        oldwrite(name.replace('Box4',family),
                 [x.replace('Box4',family) for x in imports],
                 body.replace('Box4',family))
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
            record=list(map(int,l.split()));assert len(record)==21
            stack.append([record[:12],record[12:16],record[16:20]])
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
        if w[0]=='known':return Node(t,'known',(family+'Known','BB6.Agent13.'+family+'.'+w[1]))
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
    alternatives=' ∨ '.join(f't = {t}' for t in TARGETS)
    patterns='|'.join('h' for _ in TARGETS)
    cases=''.join(f'  · exact slice{t}\n' for t in TARGETS)
    emitter.write(f'{family}Closure',[f'{family}Slice{t}' for t in TARGETS],f'''namespace BB6.Agent13.{family}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box
theorem allSlices : ∀ t : Fin 12, t ∈ haltTargets → Good t (root t) := by
  intro t ht
  have h : {alternatives} := by simpa [haltTargets] using ht
  rcases h with {patterns} <;> subst t
{cases}theorem sourceBound : ∀ m, compatible (Box33D0.child {d} {v}) m → WeightedBound {BOUND} m := by
  intro m hm
  exact source_upper allSlices m (source_compatible m hm)
#print axioms sourceBound
end BB6.Agent13.{family}
''')
    print('generated all six branch slices; source check still required',flush=True)
if __name__=='__main__':main()
