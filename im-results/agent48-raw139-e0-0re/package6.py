"""Generate a sharded Lean proof from a complete exact first-hole partition.

The emitted proof uses the existing FastThreeHoleAudit checker; no new
trusted decision procedure is introduced. Source-level acceptance is separate.
"""
import json
import pathlib
import re
import sys
from collections import Counter
from blockcert import generate
from scan import far, ORDER
from package import block_source, bl, slot


def first_hole(table, limit):
    """Exact linear replay: a late last-hole leaf needs no cycle search."""
    tape = set()
    q = h = 0
    for step in range(limit + 1):
        s = 2*q + int(h in tape)
        v = table[s]
        if v == 24:
            return ('hole', step, s)
        if v & 2:
            tape.add(h)
        else:
            tape.discard(h)
        q = v >> 2
        h += 1 if v & 1 else -1
    return ('open',)


def make(spec, partition, out):
    assert partition['counts'] == spec['counts']
    tr, opens = partition['tree'], partition['open']
    idx = {tuple(t): i for i,t in enumerate(opens)}
    assert len(idx) == len(opens) == spec['counts']['open']
    solved = {}

    def record(i, value):
        i = int(i)
        assert i not in solved
        solved[i] = value

    for params, indices in spec['block_groups']:
        for i in indices:
            record(i, ['block', *params])
    for i, args in spec['late'].items():
        i = int(i)
        assert opens[i].count(24) == 1 and first_hole(opens[i],args[0]) == ('hole',*args)
        record(i, ['last',*args])
    for i, namespace in spec['proven'].items():
        record(i, ['proven', namespace])
    assert set(solved) == set(range(len(opens)))
    ns, prefix, B = spec['namespace'], spec['prefix'], spec['bound']
    out.mkdir(parents=True,exist_ok=True)
    modules, block_module = [], {}
    blockids = sorted(i for i,x in solved.items() if x[0]=='block')
    for j in range(0,len(blockids),8):
        name = f'{prefix}Block{j//8:02}'
        modules.append(name)
        source = 'import BlockFAR2\nimport BlockFARBridge\nimport FastThreeHoleAudit\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n'
        for i in blockids[j:j+8]:
            _,w,c,m,r,f,ph = solved[i]
            assert not f  # block_source transfers the unreflected table
            data = generate(opens[i],w,c,m,r,f,phase=ph)
            assert data is not None, i
            source += block_source(i,opens[i],data).replace('BB6.Agent48F1OneRABlocks',ns+'Blocks')
            block_module[i] = name
        (out/(name+'.lean')).write_text(source)
    base = 'set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n'
    base += f'namespace {ns}\nopen BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10FastAudit\n'
    module_for = {}
    cap = spec['max_module_leaves']
    sizes = {}

    def size(n):
        if n[0]!='split': return 1
        value = sum(map(size,n[3]))
        sizes[id(n)] = value
        return value

    size(tr)
    assert sizes[id(tr)] == 1 + 23*spec['counts']['split']

    def imports_for(src):
        blocks = {block_module[int(i)] for i in re.findall(r'Blocks\.H(\d+)\.ctr',src)}
        branches = {module_for[n] for n in re.findall(r'\b[pth](R\d+(?:_\d+)*)\b',src) if n in module_for}
        names = sorted(blocks | branches | set(spec['external_imports']))
        return 'import FastThreeHoleAudit\n'+''.join(f'import {m}\n' for m in names)

    def leaf(n):
        k,*a = n
        if k=='cycle':
            e,s,r,x = a; return f'.cycle {e} {s} {bl(r)} ({x})'
        if k=='last':
            steps,s = a; return f'.last {steps} {slot(s)}'
        if k=='far':
            rev,d,dfa,t0,t1,z = a; return f'.far {bl(rev)} {d} ⟨0,{dfa},{t0},{t1},{z}⟩'
        if k=='open':
            i = idx[tuple(a[0])]; v = solved[i]
            if v[0]=='block':
                p=f'{ns}Blocks.H{i}'
                return f'.proven {p}.ctr {p}.never'
            if v[0]=='proven':
                p=v[1]
                return f'.proven {p}.ctr {p}.never'
            return leaf(v)
        raise ValueError(k)

    def mov(v): return f'⟨{bl(v&2)},{bl(v&1)},{v//4}⟩'

    def build(n,t,name,lines):
        if n[0]!='split': return leaf(n),None
        _,steps,s,kids = n
        assert len(kids)==24 and t[s]==24
        items=[]
        for i,(v,ch) in enumerate(zip(ORDER,kids)):
            t2=t.copy();t2[s]=v
            items.append((ch,t2,f'{name}_{i}'))
        if sizes[id(n)] > cap:
            children=emit_children(items)
        else:
            children=[build(ch,t2,cname,lines) for ch,t2,cname in items]
        lines.append(f'def p{name} : PartialMachine := fromCodes {t}')
        lines.append(f'def t{name} : Audit := .split {steps} {slot(s)} (byMove [\n'+',\n'.join(a for a,_ in children)+'])')
        if all(h is None for _,h in children):
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
            for i,(a,h) in enumerate(children):
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

    def emit_group(items):
        lines=[]
        results=[build(n,t,name,lines) for n,t,name in items]
        mod=prefix+'Branch'+items[0][2].replace('_','X')
        src=base+'\n'.join(lines)+f'\nend {ns}\n'
        (out/(mod+'.lean')).write_text(imports_for(src)+src)
        for _,_,name in items:
            module_for[name]=mod
        modules.append(mod)
        return results

    def emit_children(items):
        """Pack sibling subtrees into modules without creating extra dependencies."""
        result=[None]*len(items)
        pending=[]
        mass=0
        def flush():
            nonlocal pending,mass
            if pending:
                for j,x in zip(pending,emit_group([items[j] for j in pending])):
                    result[j]=x
            pending=[];mass=0
        for i,(n,t,name) in enumerate(items):
            if n[0]!='split':
                result[i]=(leaf(n),None)
            elif sizes[id(n)]>cap:
                flush()
                result[i]=emit_group([(n,t,name)])[0]
            else:
                if mass+sizes[id(n)]>cap:flush()
                pending.append(i);mass+=sizes[id(n)]
        flush()
        assert all(x is not None for x in result)
        return result

    # Root split's descendants use names R0, R1, ...; the top-level proof
    # itself uses Root so the same dependency extraction works transitively.
    lines=[]
    _,steps,s,kids=tr
    assert len(kids)==24
    items=[]
    for i,(v,ch) in enumerate(zip(ORDER,kids)):
        t=spec['parent'].copy(); t[s]=v
        items.append((ch,t,f'R{i}'))
    rootkids=emit_children(items)
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
        if h is None: lines.append('  · decide +kernel')
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
    (out/(prefix+'Cover.lean')).write_text(imports_for(src)+src)
    print('generated',len(blockids),'Block-FAR proofs,',len(set(module_for.values())),'branch modules and root;',sizes[id(tr)],'leaves')

if __name__=='__main__':
    make(json.loads(pathlib.Path(sys.argv[1]).read_text()),json.loads(pathlib.Path(sys.argv[2]).read_text()),pathlib.Path(sys.argv[3]))
