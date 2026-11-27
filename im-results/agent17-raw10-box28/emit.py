#!/usr/bin/env python3
"""Generate an exact source proof for a completed Box28 D0=14,D1=3/4/17/18/19/20
discovery cut. Reuses the accepted reflective one-halt/stack proof method.
Requires preserved discovery artifact, not a second classification scan.
Refuses any unresolved leaf. The generated source must pass Lean separately.
"""
from pathlib import Path
import argparse, json, os, sys, shutil, re
from math import prod
HERE=Path(__file__).resolve().parent
BASE=HERE.parent/'agent13-raw10-box4'
TEMPLATE=HERE.parent/'agent13-raw10-box33'
BRANCH=HERE.parent/'agent13-raw10-box3-branches'
from cuts import TODO, fixed_for, targets_for, second_index, stem, carry_rectangle
def put(out,name,content):
    (out/(name+'.lean')).write_text(content)

def source_core(out, name, d0, v, bound):
    s=(TEMPLATE/'Box33BranchCore.lean').read_text()
    s=s.replace('Box33Branch',name)
    s=s.replace('/-- B1=0LD and D0=0RA in the authentic Raw10 residual rectangle 33. -/',
                f'/-- D0={d0}, slot {second_index(d0)} code {v} in authentic Raw10 rectangle 28. -/')
    si=second_index(d0)
    fixed=fixed_for(d0,v)
    old='  | 0 => [8]\n  | 2 => [11]\n  | 3 => [13]\n  | 4 => [1]\n  | 5 => [13]\n  | 6 => [2]'
    new='\n'.join(f'  | {i} => [{c}]' for i,c in enumerate(fixed) if c>=0)
    assert s.count(old)==1
    s=s.replace(old,new)
    # One simultaneous substitution: avoids confusing code 2 with a newly inserted code.
    replacements={
        'index s = 3':f'index s = {si}',
        'i = 3 then ([13]':f'i = {si} then ([{v}]',
        'then [decode 13]':f'then [decode {v}]',
        'then [decode 2]':f'then [decode {d0}]',
        '([2] : List (Fin 25))':f'([{d0}] : List (Fin 25))',
        's = slot 3':f's = slot {si}',
        'slot 3)':f'slot {si})',
        'decode 13 ∈':f'decode {v} ∈',
        'decode 2 ∈':f'decode {d0} ∈',
    }
    s=re.sub('|'.join(map(re.escape,replacements)),lambda m:replacements[m[0]],s)
    s=s.replace('raw10Remainder[33]','raw10Remainder[28]').replace('boxes[33]','boxes[28]').replace('(33 : Fin 34)','(28 : Fin 34)')
    ts=targets_for(d0)
    for var in ('t','i'):
        s=s.replace(f'{var} = 1 ∨ 7 ≤ {var}.val',' ∨ '.join(f'{var} = {t}' for t in ts))
    s=s.replace('101',str(bound))
    put(out,name+'Core',s)
    s=(TEMPLATE/'Box33BranchTree.lean').read_text().replace('Box33Branch',name).replace('101',str(bound))
    put(out,name+'Tree',s)

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--d0',type=int,choices=tuple(TODO),default=14)
    p.add_argument('--d1','--code',dest='d1',type=int,required=True)
    p.add_argument('--work',type=Path,required=True)
    p.add_argument('--out',type=Path,required=True)
    p.add_argument('--far',type=Path)
    p.add_argument('--bank',type=Path,help='Previously selected certificate seed list; reconstruct masks, no discovery')
    a=p.parse_args()
    work=a.work.resolve();out=a.out.resolve();out.mkdir(parents=True,exist_ok=True)
    far=a.far.resolve() if a.far else None
    bank=a.bank.resolve() if a.bank else None
    os.chdir(work);fixed=fixed_for(a.d0,a.d1)
    TARGETS=targets_for(a.d0)
    name=stem(a.d0,a.d1)
    summary=json.load(open('summary.json'))
    assert set(map(int,summary))==set(TARGETS),'incomplete discovery'
    hard_rows={
      (8,0,11,24,11,13,14,17,22,9,19,4):('counterFalse',1,'counterPartial false','counter_compatible_never false'),
      (8,0,11,24,11,13,14,17,22,17,19,4):('counterTrue',1,'counterPartial true','counter_compatible_never true'),
      (8,14,11,24,11,13,14,17,3,15,4,0):('sweep',11,'sweepPartial','sweep_compatible_never'),
    } if (a.d0,a.d1)==(14,17) else {}
    # Exact analytically solved residual rows, independent of the finite FAR bank.
    d16_hard = {
        (16,17): ((8,10,11,22,11,13,16,17,20,4,0,12),'Box28D16V17PumpSource'),
        (16,18): ((8,1,11,0,11,13,16,18,10,22,23,4),'Box28D16V18GrowthSource'),
    }.get((a.d0,a.d1))
    if d16_hard:
        row,module=d16_hard
        hard_rows[row]=('d16Recurrence',row.index(0),'partialTable','compatible_never')
    remaining={tuple(t) for v in summary.values() for t in v['open_rows']}
    d2v13_rows=[[8,24,11,13,11,13,2,23,0,6,4,20],[8,24,11,13,11,13,2,23,0,10,4,20],[8,20,11,13,11,13,2,23,4,0,2,21],[8,20,11,13,11,13,2,19,4,24,0,6],[8,20,11,13,11,13,2,19,4,24,0,10],[8,24,11,13,11,13,2,19,2,17,4,0]]
    d2v13 = (a.d0,a.d1)==(2,13)
    if d2v13:
        hard_rows={tuple(row):(f'row{i}',row.index(0),None,None) for i,row in enumerate(d2v13_rows)}
    carry_rows={row for row in remaining if carry_rectangle(row)}
    if carry_rows:
        hard_rows.update({row:(f'carry{i}',row.index(0),None,None) for i,row in enumerate(sorted(carry_rows))})
    max_late=max(v['late_max_halt'][0] for v in summary.values())
    bound=max(3640,max_late+5)
    if far:
        manifest=json.loads((far/'far_manifest.json').read_text())
        assert set(map(tuple,manifest['open_rows'])) <= set(hard_rows)
        solved={tuple(row):param for row,param in manifest['solved']}
        assert set(solved)|set(hard_rows)==remaining, ('FAR coverage mismatch',(set(solved)|set(hard_rows))^remaining)
        imports=[name+'Tree']
        defs=[]
        for row in sorted(solved):
            i=sorted(remaining).index(row)
            width,cap,mod,runs,flip,mode=solved[row]
            assert len(row)==12 and row.count(0)==1
            target=row.index(0)
            label=f'far{i:02d}'
            farstem=f'{name}Far{i:02d}'
            ns=f'BB6BlockFAR{width}'
            for suffix in ('Packed','Proof'):
                src=(far/(farstem+suffix+'.lean')).read_text()
                if width==3:
                    src=src.replace('BB6BlockFAR.','BB6BlockFAR3.').replace('import BlockFAR\n','import BlockFAR3\n').replace('import RangeCheck\n','import RangeCheck3\n')
                (out/(farstem+suffix+'.lean')).write_text(src)
            bridge=farstem+'Source'
            q=f'BB6.Agent13.{name}.{farstem}'
            imports.append(bridge)
            im=[f'import {farstem}Proof',f'import BlockFARBridge{width}',f'import {name}Core']
            if flip: im.append(f'import MirrorTransport{width}')
            table=f'{ns}.{farstem}.machine'
            projected=f'{ns}.mirrorTable {table}' if flip else table
            proof=(f'{ns}.never_of_mirror projected (by simpa only [projected, {ns}.mirrorTable_involutive] using {ns}.{farstem}.never)' if flip else f'{ns}.{farstem}.never')
            codes=','.join('none' if v<0 else f'some {v}' for v in row)
            body=f'''namespace {q}
open BB6Coverage BB6.Agent49Box BB6.Agent13.Box17
def row : PartialMachine := fun s => (([{codes}] : List (Option (Fin 25)))[2*s.1.val+s.2.toNat]!).map decode
def projected : {ns}.Table := {projected}
def projectionCheck (s : Slot) : Bool :=
  match {ns}.partialTable projected s with
  | none => true
  | some t => decide (row s = some t)
theorem projection_checks : ∀ (q : Fin 6) (b : Bool), projectionCheck (q,b) = true := by decide
theorem projection (s : Slot) :
    match {ns}.partialTable projected s with
    | none => True
    | some t => row s = some t := by
  have hc := projection_checks s.1 s.2
  change projectionCheck s = true at hc
  cases h : {ns}.partialTable projected s with
  | none => trivial
  | some t => simpa [projectionCheck,h] using hc
theorem compatible_never (m : Machine) (hm : compatible row m) : NeverHalts m := by
  apply {ns}.transfer_never projected m
  · intro s t ht
    have h := projection s
    rw [ht] at h
    exact hm s t h
  · exact {proof}
end {q}
'''
            put(out,bridge,'\n'.join(im)+'\n'+body)
            hard_rows[row]=(label,target,None,None)
            defs.append(f'def {label} : Known {target} := ⟨{q}.row, good_never {target} _ {q}.compatible_never⟩')
        far_imports=imports[1:]; far_defs=defs
    else:
        far_imports=[];far_defs=[]
        assert remaining==set(hard_rows),('unexpected unresolved rows',remaining)
    if hard_rows:
        ns='BB6.Agent17.Box28D2V13Residual' if d2v13 else 'BB6.Agent17.Box28CarryRectangle' if carry_rows else 'BB6.Agent17.'+d16_hard[1] if d16_hard else 'BB6.Agent17.Box28HardSource'
        analytic_rows=set(hard_rows)-set(solved) if far else set(hard_rows)
        lines=[f'import {name}Tree',*(f'import {m}' for m in far_imports)]
        if analytic_rows:
            lines.append('import '+('Box28D2V13Residual' if d2v13 else 'Box28CarryRectangle' if carry_rows else d16_hard[1] if d16_hard else 'Box28HardSource'))
        lines.extend([f'namespace BB6.Agent13.{name}','open BB6Coverage',*far_defs])
        for row in sorted(analytic_rows):
            label,target,part,proof=hard_rows[row]
            if d2v13:
                i=label[3:]
                lines.append(f'def {label} : Known {target} := ⟨{ns}.row {i}, fun m _ hm => {ns}.rowBound _ {i} m hm⟩')
            elif row in carry_rows:
                two=str(row[1]==24).lower()
                codes=','.join('none' if v<0 else 'some '+str(v) for v in row)
                lines.append(f'''def {label}Row : PartialMachine := fun s => (([{codes}] : List (Option (Fin 25)))[2*s.1.val+s.2.toNat]!).map BB6.Agent13.Box17.decode
 theorem {label}Bound (m : Machine) (hm : compatible {label}Row m) : BB6.Agent13BlankDelay.WeightedBound {bound} m := by
  apply {ns}.rectangle_mono {bound} (by decide) {two} m
  intro s t ht
  have h : ∀ (q : Fin 6) (b : Bool), (BB6.Agent17.Box28CarryGateSource.baseTable {two} (q,b)).isSome = true → BB6.Agent17.Box28CarryGateSource.baseTable {two} (q,b) = {label}Row (q,b) := by decide
  exact hm s t ((h s.1 s.2 (by simp [ht])).symm ▸ ht)
 def {label} : Known {target} := ⟨{label}Row, fun m _ hm => {label}Bound m hm⟩''')
            else:
                lines.append(f'def {label} : Known {target} := ⟨{ns}.{part}, good_never {target} _ ({ns}.{proof})⟩')
        lines.append(f'end BB6.Agent13.{name}')
        put(out,name+'HardBank','\n'.join(lines)+'\n')
    source_core(out,name,a.d0,a.d1,bound)
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
    import modular_run
    oldcert=greedy.cert
    def cert(t,p):
        if p[0]=='m':return modular_run.run(t,p[1],100000)
        return oldcert(t,p)
    greedy.cert=cert;emitter.cert=cert
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
    if bank:
        entries=[]
        for row,param in json.loads(bank.read_text()):
            c=greedy.compress(cert(row,param))
            mask=greedy.safe_mask(c)
            assert greedy.subset(greedy.domain_mask(row),mask)
            entries.append({'t':row,'param':param,'mask':mask,'states':len(c['states'])})
        json.dump({'boxes':entries,'total':len(entries)},open('greedyboxes.json','w'))
    else:
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
    pred=' ∨ '.join(f't = {t}' for t in TARGETS)
    cases='\n'.join(f'  · exact slice{t}' for t in TARGETS)
    emitter.write(name+'Closure',[f'{name}Slice{t}' for t in TARGETS],f'''namespace BB6.Agent13.{name}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box
theorem allSlices : ∀ t : Fin 12, ({pred}) → Good t (root t) := by
  intro t ht
  rcases ht with {'|'.join('h' for _ in TARGETS)} <;> subst t
{cases}
theorem sourceBound : ∀ m, Fits sourceDomain m → WeightedBound {bound} m :=
  source_upper allSlices
#print axioms sourceBound
end BB6.Agent13.{name}
''')
    print('Generated source candidate',name,'weighted bound',bound,flush=True)
if __name__=='__main__':main()
