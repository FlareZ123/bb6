#!/usr/bin/env python3
"""Generate an exact source proof for a completed Box28 D0=14,D1=17/18
discovery cut. Reuses the accepted reflective one-halt/stack proof method.
Requires preserved discovery artifact, not a second classification scan.
Refuses any unresolved leaf. The generated source must pass Lean separately.
"""
from pathlib import Path
import argparse, json, os, sys
from math import prod
HERE=Path(__file__).resolve().parent
BASE=HERE.parent/'agent13-raw10-box4'
TEMPLATE=HERE.parent/'agent13-raw10-box33'
BRANCH=HERE.parent/'agent13-raw10-box3-branches'
TARGETS=(1,3,8,9,10,11)
def put(out,name,content):
    (out/(name+'.lean')).write_text(content)

def source_core(out, name, d1, bound):
    s=(TEMPLATE/'Box33BranchCore.lean').read_text()
    s=s.replace('Box33Branch',name)
    s=s.replace('/-- B1=0LD and D0=0RA in the authentic Raw10 residual rectangle 33. -/',
                f'/-- D0=0RD, D1 code {d1} in authentic Raw10 rectangle 28. -/')
    old='  | 3 => [13]\n  | 4 => [1]\n  | 5 => [13]\n  | 6 => [2]'
    new=f'  | 4 => [11]\n  | 5 => [13]\n  | 6 => [14]\n  | 7 => [{d1}]'
    assert s.count(old)==1
    s=s.replace(old,new)
    s=s.replace('index s = 3','index s = 7').replace('i = 3 then ([13]',f'i = 7 then ([{d1}]')
    s=s.replace('then [decode 13]',f'then [decode {d1}]').replace('then [decode 2]','then [decode 14]')
    s=s.replace('([2] : List (Fin 25))','([14] : List (Fin 25))')
    s=s.replace('s = slot 3','s = slot 7').replace('slot 3)','slot 7)')
    s=s.replace('decode 13 ∈',f'decode {d1} ∈').replace('decode 2 ∈','decode 14 ∈')
    s=s.replace('raw10Remainder[33]','raw10Remainder[28]').replace('boxes[33]','boxes[28]').replace('(33 : Fin 34)','(28 : Fin 34)')
    s=s.replace('t = 1 ∨ 7 ≤ t.val','t = 1 ∨ t = 3 ∨ 8 ≤ t.val')
    s=s.replace('i = 1 ∨ 7 ≤ i.val','i = 1 ∨ i = 3 ∨ 8 ≤ i.val')
    s=s.replace('101',str(bound))
    put(out,name+'Core',s)
    s=(TEMPLATE/'Box33BranchTree.lean').read_text().replace('Box33Branch',name).replace('101',str(bound))
    put(out,name+'Tree',s)

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--d1',type=int,choices=(17,18),required=True)
    p.add_argument('--work',type=Path,required=True)
    p.add_argument('--out',type=Path,required=True)
    a=p.parse_args()
    work=a.work.resolve();out=a.out.resolve();out.mkdir(parents=True,exist_ok=True)
    os.chdir(work);fixed=[8,-1,11,-1,11,13,14,a.d1,-1,-1,-1,-1]
    name='Box28D'+str(a.d1)
    summary=json.load(open('summary.json'))
    assert set(map(int,summary))==set(TARGETS),'incomplete discovery'
    hard_rows={
      (8,0,11,24,11,13,14,17,22,9,19,4):('counterFalse',1,'counterPartial false','counter_compatible_never false'),
      (8,0,11,24,11,13,14,17,22,17,19,4):('counterTrue',1,'counterPartial true','counter_compatible_never true'),
      (8,14,11,24,11,13,14,17,3,15,4,0):('sweep',11,'sweepPartial','sweep_compatible_never'),
    } if a.d1==17 else {}
    remaining={tuple(t) for v in summary.values() for t in v['open_rows']}
    assert remaining==set(hard_rows),('unexpected unresolved rows',remaining)
    if hard_rows:
        ns='BB6.Agent17.Box28HardSource'
        lines=[f'import {name}Tree','import Box28HardSource',
          f'namespace BB6.Agent13.{name}','open BB6Coverage']
        for row,(label,target,part,proof) in hard_rows.items():
            lines.append(f'def {label} : Known {target} := ⟨{ns}.{part}, good_never {target} _ ({ns}.{proof})⟩')
        lines.append(f'end BB6.Agent13.{name}')
        put(out,name+'HardBank','\n'.join(lines)+'\n')
    max_late=max(v['late_max_halt'][0] for v in summary.values())
    bound=max(3640,max_late+5)
    source_core(out,name,a.d1,bound)
    sys.path[:0]=[str(BASE),str(BRANCH)]
    import finish,greedy
    from domain_lag_rle import run
    argv=sys.argv;sys.argv=['emit_proof.py',str(out)]
    import emit_proof as emitter
    sys.argv=argv
    def domain_for(target):
        assert target in TARGETS
        return tuple((v,) if v>=0 else (0,) if i==target else tuple(range(1,25)) for i,v in enumerate(fixed))
    finish.domain_for=domain_for
    greedy.BASE=[1<<v if v>=0 else (1<<25)-1 for v in fixed]
    greedy.run=run;greedy.HERE=work
    emitter.HERE=work;emitter.OUT=out;emitter.domain_for=domain_for
    oldwrite=emitter.write
    def write(mod,imports,body):
        oldwrite(mod.replace('Box4',name),[m.replace('Box4',name) for m in imports],body.replace('Box4',name))
    emitter.write=write
    stack=[];long={}
    for target in TARGETS:
        for row,w in json.load(open(f'late{target}.json')):
            long[tuple(row)]=w
        for line in open(f'rle{target}.txt'):
            v=list(map(int,line.split()));assert len(v)==21
            stack.append([v[:12],v[12:16],v[16:20]])
    json.dump({'stack':stack,'block':[]},open('survivors.json','w'))
    sys.argv=['greedy.py'];greedy.main();sys.argv=argv
    # Build first-hole proof tree from exact source slice domains.
    import subprocess
    from discover import prepare
    if not (work/'treegen').exists():prepare(work,fixed)
    for target in TARGETS:subprocess.run([str(work/'treegen'),str(target)],check=True)
    boxes=emitter.bank_modules('B')
    masks=[tuple(e['mask']) for e in json.load(open('greedyboxes.json'))['boxes']]
    Node=emitter.Node
    def late_node(t,target):
        for i,b in enumerate(masks):
            if greedy.subset(greedy.domain_mask(t),b):return Node(t,'a',(i,))
        if t in hard_rows:return Node(t,'known',(name+'HardBank',f'BB6.Agent13.{name}.{hard_rows[t][0]}'))
        w=long[t]
        if w[0]=='halt':return Node(t,'h',(w[1],))
        if w[0] in ('cycle','side'):return Node(t,'c',tuple(w[1:]))
        if w[0]=='hole':
            s=w[1];return Node(t,'b',(s,),[(v,late_node(t[:s]+(v,)+t[s+1:],target)) for v in domain_for(target)[s]])
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
    for target in TARGETS:emitter.tree_modules(target,load(target),boxes)
    emitter.write(name+'Closure',[f'{name}Slice{t}' for t in TARGETS],f'''namespace BB6.Agent13.{name}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box
theorem allSlices : ∀ t : Fin 12, (t = 1 ∨ t = 3 ∨ 8 ≤ t.val) → Good t (root t) := by
  intro t ht
  have h : t = 1 ∨ t = 3 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11 := by omega
  rcases h with h|h|h|h|h|h <;> subst t
  · exact slice1
  · exact slice3
  · exact slice8
  · exact slice9
  · exact slice10
  · exact slice11
theorem sourceBound : ∀ m, Fits sourceDomain m → WeightedBound {bound} m :=
  source_upper allSlices
#print axioms sourceBound
end BB6.Agent13.{name}
''')
    print('Generated source candidate',name,'weighted bound',bound,flush=True)
if __name__=='__main__':main()
