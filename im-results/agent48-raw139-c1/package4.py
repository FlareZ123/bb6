import json, pathlib, sys, re
from collections import Counter
from blockcert import generate
from scan import tree,scan,find_far,far,ORDER
from package import block_source, bl, slot

def make(spec,out,partition=None):
    counts=Counter(); opens=[]
    if partition is None:
        tr=tree(spec['parent'],counts,opens,spec['limit'],spec['maxd'])
        assert dict(counts)==spec['counts']
    else: tr,opens=partition['tree'],partition['open']
    idx={tuple(t):i for i,t in enumerate(opens)}
    if 'solved' in spec:
        solved={int(i):v for i,v in spec['solved'].items()}
    else:
        solved={i:['block',*params] for params,indices in spec['block_groups'] for i in indices}
        for i,(rev,dfa) in spec['far'].items(): solved[int(i)]=['far-dfa',rev,dfa]
        for i,args in spec['cycles'].items(): solved[int(i)]=['cycle',*args]
        for i,args in spec['late'].items():
            i=int(i)
            assert opens[i].count(24)==1 and scan(opens[i],args[0])==('hole',*args)
            solved[i]=['last',*args]
    assert set(solved)==set(range(len(opens)))
    ns=spec['namespace']; prefix=spec['prefix']; B=spec['bound']
    out.mkdir(parents=True,exist_ok=True)
    modules=[]
    blockids=sorted(i for i,x in solved.items() if x[0]=='block')
    for j in range(0,len(blockids),8):
        name=f'{prefix}Block{j//8:02}'
        modules.append(name)
        source='import BlockFAR2\nimport BlockFARBridge\nimport FastThreeHoleAudit\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n'
        for i in blockids[j:j+8]:
            _,w,c,m,r,f,ph=solved[i]
            data=generate(opens[i],w,c,m,r,f,phase=ph)
            assert data is not None
            source+=block_source(i,opens[i],data).replace('BB6.Agent48F1OneRABlocks',ns+'Blocks')
        (out/(name+'.lean')).write_text(source)
    base='set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n'
    base+=f'namespace {ns}\nopen BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10FastAudit\n'
    block_imports='import FastThreeHoleAudit\n'+''.join(f'import {m}\n' for m in modules)
    block_module={i:modules[j//8] for j,i in enumerate(blockids)}
    def imports_for(src):
        used=sorted({block_module[int(i)] for i in re.findall(r'Blocks\.H(\d+)\.ctr',src)})
        return 'import FastThreeHoleAudit\n'+''.join(f'import {m}\n' for m in used)
    def far_node(a):
        rev,d,dfa,t0,t1,z=a
        return f'.far {bl(rev)} {d} ⟨0,{dfa},{t0},{t1},{z}⟩'
    def leaf(n):
        k,*a=n
        if k=='cycle':
            e,s,r,x=a;return f'.cycle {e} {s} {bl(r)} ({x})'
        if k=='last':
            steps,s=a;return f'.last {steps} {slot(s)}'
        if k=='far':return far_node(a)
        if k=='open':
            i=idx[tuple(a[0])];v=solved[i]
            if v[0]=='block':
                p=f'{ns}Blocks.H{i}'
                return f'.proven {p}.ctr {p}.never'
            if v[0]=='far-dfa':return far_node(far(a[0],v[1],v[2]))
            return leaf(v)
        raise ValueError(k)
    def mov(v):return f'⟨{bl(v&2)},{bl(v&1)},{v//4}⟩'
    def build(n,t,name,lines):
        if n[0]!='split':return leaf(n),None
        _,steps,s,kids=n
        kids2=[]
        for i,(v,ch) in enumerate(zip(ORDER,kids)):
            t2=t.copy();t2[s]=v
            kids2.append(build(ch,t2,f'{name}_{i}',lines))
        lines.append(f'def p{name} : PartialMachine := fromCodes {t}')
        lines.append(f'def t{name} : Audit := .split {steps} {slot(s)} (byMove [\n'+',\n'.join(a for a,_ in kids2)+'])')
        if all(h is None for _,h in kids2):
            lines.append(f'theorem h{name} : fastCheck {B} p{name} t{name} = true := by decide +kernel')
        else:
            lines.append(f'''theorem h{name} : fastCheck {B} p{name} t{name} = true := by
  simp only [t{name}, fastCheck, Bool.and_eq_true]
  refine ⟨by decide +kernel, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  cases w <;> cases r
  all_goals
    have hcases : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
      have hlt := q.isLt
      simp only [Fin.ext_iff]
      omega
    rcases hcases with h | h | h | h | h | h
    all_goals subst q''')
            for i,(a,h) in enumerate(kids2):
                v=ORDER[i]
                if h is None:
                    lines.append('  · decide +kernel')
                else:
                    cname=h[1:]
                    lines.append(f'''  · change fastCheck {B} (refine p{name} {slot(s)} (some {mov(v)})) {a} = true
    have hp : refine p{name} {slot(s)} (some {mov(v)}) = p{cname} := tableOK_sound _ _ (by decide +kernel)
    rw [hp]
    exact {h}''')
        return f't{name}',f'h{name}'
    assert tr[0]=='split'
    _,steps,s,kids=tr
    rootkids=[];submods=[]
    for i,(v,ch) in enumerate(zip(ORDER,kids)):
        if ch[0]!='split':
            rootkids.append((leaf(ch),None));continue
        t=spec['parent'].copy();t[s]=v
        lines=[]
        a,h=build(ch,t,f'R{i}',lines)
        name=f'{prefix}Branch{i:02}';submods.append(name);rootkids.append((a,h))
        src=base+'\n'.join(lines)+f'\nend {ns}\n'
        (out/(name+'.lean')).write_text(imports_for(src)+src)
    name='Root'
    lines=[f'def pRoot : PartialMachine := fromCodes {spec["parent"]}',
           f'def tRoot : Audit := .split {steps} {slot(s)} (byMove [\n'+',\n'.join(a for a,_ in rootkids)+'])',
           f'''theorem hRoot : fastCheck {B} pRoot tRoot = true := by
  simp only [tRoot, fastCheck, Bool.and_eq_true]
  refine ⟨by decide +kernel, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  cases w <;> cases r
  all_goals
    have hcases : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
      have hlt := q.isLt
      simp only [Fin.ext_iff]
      omega
    rcases hcases with h | h | h | h | h | h
    all_goals subst q''']
    for i,(a,h) in enumerate(rootkids):
        v=ORDER[i]
        if h is None:lines.append('  · decide +kernel')
        else:
            cname=h[1:]
            lines.append(f'''  · change fastCheck {B} (refine pRoot {slot(s)} (some {mov(v)})) {a} = true
    have hp : refine pRoot {slot(s)} (some {mov(v)}) = p{cname} := tableOK_sound _ _ (by decide +kernel)
    rw [hp]
    exact {h}''')
    lines.append(f'''def parent : PartialMachine := pRoot
theorem root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide +kernel
theorem nohalt : weightedTNFNoAssignedHalt parent := by
  intro s
  unfold parent pRoot fromCodes
  cases h : ({spec["parent"]} : List Nat)[2 * s.1.val + s.2.toNat]? with
  | none => simp [h]
  | some n => by_cases hn : n < 24 <;> simp [h, hn]
noncomputable def certificate : WeightedTNFCertificate {B} parent 6 :=
  certifiedFast {B} parent tRoot root nohalt hRoot
theorem all_completions_weighted : ∀ m, compatible parent m → WeightedBound {B} m := certificate.sound
#print axioms hRoot
#print axioms all_completions_weighted
end {ns}
''')
    src=base+'\n'.join(lines)
    (out/(prefix+'Cover.lean')).write_text(imports_for(src)+''.join(f'import {m}\n' for m in submods)+src)
    return modules,submods,prefix+'Cover'
if __name__=='__main__':
    make(json.loads(pathlib.Path(sys.argv[1]).read_text()),pathlib.Path(sys.argv[2]))
