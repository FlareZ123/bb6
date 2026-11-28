#!/usr/bin/env python3
"""Emit independent, exact ordinary-region certificate modules for D0=1LF.

Input is the established replay partition and saved witness recipes, not a
fresh search. Each generated region theorem proves the actual semantic Cover
at the small finite bound. The two exceptional leaves are never substituted.
"""
import argparse
import hashlib
import json
import pathlib
import re
from blockcert import generate

B=148142
NS='BB6.Agent3D0LF1Ordinary'
ORDER=[4*q+2*w+r for w in range(2) for r in range(2) for q in range(6)]
BASE='''set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6Coverage.Agent10ZipAudit
open BB6.Agent3PackedAudit BB6.Agent48PackedPrefix
'''

def bl(v):return str(bool(v)).lower()
def slot(s):return f'({s//2},{bl(s%2)})'
def mov(v):return f'⟨{bl(v&2)},{bl(v&1)},{v//4}⟩'
def pack(xs,b):return sum(v<<(b*i) for i,v in enumerate(xs))
def vec(xs,b,stride=16):return f'⟨{b},{stride},#['+','.join(hex(pack(xs[i:i+stride],b)) for i in range(0,len(xs),stride))+']⟩'
def rows(xs,b):
    k=max(1,max(map(len,xs)))
    return f'⟨{vec([pack([v+1 for v in x],b) for x in xs],b*k,8)},{b},{k}⟩'

def dense_block_source(name,t,c,flip):
    ns={2:'BB6BlockFAR2',3:'BB6BlockFAR'}[c['width']]
    d,n=c['left_states'],c['right_nodes']; b=max(d,n).bit_length();pb=(2**c['width']*d).bit_length()
    moves=', '.join('none' if m is None else f'some ⟨{bl(m[0])},{bl(m[1])},{m[2]}⟩' for m in c['moves'])
    src=f'''namespace {NS}.Blocks.{name}
def machine : BB6BlockFAR.Table := fun q b => ([{moves}] : List (Option BB6BlockFAR.Move))[2*q.val+b.toNat]?.getD none
def cert : {ns}.Data {d-1} {n-1} := {{
  start := 0
  pushCodes := {vec(c['push'],b)}
  controlCodes := {vec(c['ctrl'],b)}
  auxiliaryCodes := {vec(c['aux'],b)}
  predecessorCodes := {rows(c['pred'],pb)}
  edgeCodes := {rows(c['edges'],b)}
  zeroCodes := {sum(1<<x for x in c['zero_states'])}
  zeroNextCodes := {vec(c['zeroNext'],b)}
}}
'''
    if d<10:
        src+='theorem valid : cert.Valid machine := ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩\n'
    else:
        src+='\n'.join(f'theorem row_{l} : cert.rowsAt machine ({l} : Fin {d}) = true := by decide +kernel' for l in range(d))
        src+=f'\ntheorem rows_valid : cert.rowsCheck machine = true := by\n  unfold {ns}.Data.rowsCheck\n  rw [show List.finRange {d} = ({list(range(d))} : List (Fin {d})) by decide]\n  simp ['+', '.join(f'row_{l}' for l in range(d))+']\n'
        src+='theorem valid : cert.Valid machine := ⟨by decide +kernel,by decide +kernel,rows_valid⟩\n'
    src+=f'''theorem forever : ∀ k, ∃ c, BB6BlockFAR.run machine k BB6BlockFAR.primBlank = some c :=
  cert.sound machine valid
def ctr : PartialMachine := fromCodes {t}
theorem same : {'FAR.reflectPartial ctr' if flip else 'ctr'} = BB6BlockFAR.partialTable machine :=
  tableOK_sound _ _ (by decide +kernel)
theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=
  '''
    if flip:src+='FAR.reflectNever m (BB6BlockFAR.transfer_never machine _ (by simpa only [← same] using FAR.reflectCompatible ctr m hm) forever)\n'
    else:src+='BB6BlockFAR.transfer_never machine m (by simpa only [← same] using hm) forever\n'
    return src+f'end {NS}.Blocks.{name}\n'

def build(part,plan,census,out,region_ids,cap=500):
    assert part['counts']==plan['counts']
    if 'open' in census:assert part['open']==census['open']
    idx={tuple(t):i for i,t in enumerate(part['open'])};assert len(idx)==4875
    recipes={int(i):v for i,v in census['recipes'].items()}
    out.mkdir(parents=True,exist_ok=True)
    module_for={}; block_module={}; blocks={}; tree=part['tree']
    def at(path):
        n=tree;t=part_table.copy()
        for j in path:
            assert n[0]=='split' and t[n[2]]==24
            t[n[2]]=ORDER[j];n=n[3][j]
        return n,t
    part_table=plan['parent']
    def graft(n,t):
        if n[0]=='split':
            k,s=n[1:3]; assert t[s]==24
            return ['split',k,s,[graft(ch,t[:s]+[v]+t[s+1:]) for v,ch in zip(ORDER,n[3])]]
        if n[0]!='open':return n
        assert n[1]==t
        i=idx[tuple(t)];r=recipes[i]
        assert i not in plan['exception_indexes']
        return materialize(r,t,f'H{i}')
    def materialize(r,t,name):
        if r[0]=='block':
            w,c,m,runs,flip,phase=r[1];assert name not in blocks
            blocks[name]=(t,r[1]);return ['proven',name]
        if r[0]=='split':
            n,s=r[1]['query'];assert t[s]==24 and len(r[1]['children'])==24
            # Census graft children are indexed by numeric transition code.
            # The original replay and byMove use write/direction/state order.
            return ['split',n,s,[materialize(ch,t[:s]+[v]+t[s+1:],f'{name}X{j}') for j,v in enumerate(ORDER) for ch in [r[1]['children'][v]]]]
        assert r[0] in ('last','cycle');return [r[0],*r[1]]
    selected=[]
    for i in region_ids:
        r=plan['ordinary_regions'][i];n,t=at(r['path']);assert t==r['table']
        selected.append((i,graft(n,t),t))
    print(f'{len(selected)} regions; {len(blocks)} Block-FAR witnesses',flush=True)
    for start in range(0,len(blocks),4):
        entries=list(blocks.items())[start:start+4]
        mod=f'D0LF1Blocks{region_ids[0]}X{start//4}'
        src='import BlockFAR2\nimport BlockFARBridge\nimport PackedPrefixAudit\n'+BASE
        for name,(t,r) in entries:
            w,c,m,runs,flip,phase=r
            data=generate(t,w,c,m,runs,flip,phase=phase,event_limit=50000)
            assert data is not None,name
            src+=dense_block_source(name,t,data,flip)
            block_module[name]=mod
        (out/f'{mod}.lean').write_text(src)
    sizes={}
    def size(n):
        z=sum(map(size,n[3])) if n[0]=='split' else 1
        sizes[id(n)]=z;return z
    def literal(n):
        k,*a=n
        if k=='cycle':e,s,r,x=a;return f'.cycle {e} {s} {bl(r)} ({x})'
        if k=='last':return f'.last {a[0]} {slot(a[1])}'
        if k=='far':rev,d,dfa,t0,t1,z=a;return f'.far {bl(rev)} {d} ⟨0,{dfa},{t0},{t1},{z}⟩'
        if k=='proven':return f'.proven {NS}.Blocks.{a[0]}.ctr {NS}.Blocks.{a[0]}.never'
        if k=='split':return f'.split {a[0]} {slot(a[1])} (byMove [\n'+',\n'.join(map(literal,a[2]))+'])'
        raise ValueError(k)
    def imports_for(src):
        deps={block_module[n] for n in re.findall(r'Blocks\.(H\d+(?:X\d+)*)\.ctr',src)}
        deps|={module_for[n] for n in re.findall(r'\b[pth](R\d+(?:X\d+)*)\b',src) if n in module_for}
        return 'import PackedPrefixAudit\n'+''.join(f'import {m}\n' for m in sorted(deps))
    def save(mod,lines):
        src='\n'.join(lines)+'\n';(out/f'{mod}.lean').write_text(imports_for(src)+BASE+f'namespace {NS}\n'+src+f'end {NS}\n')
    def build_sub(n,t,name):
        mod=f'D0LF1{name}';lines=[f'def p{name} : PartialMachine := fromCodes {t}']
        if sizes[id(n)]<=cap:
            lines.extend([f'def t{name} : Audit := {literal(n)}',f'theorem h{name} : packedCheck {B} p{name} t{name} = true := by\n  rw [← packedPrefixCheck_eq]\n  decide +kernel'])
        else:
            _,steps,s,kids=n
            children=[]
            for j,(v,ch) in enumerate(zip(ORDER,kids)):
                if sizes[id(ch)]<=1:children.append((literal(ch),None))
                else:
                    nm=f'{name}X{j}';build_sub(ch,t[:s]+[v]+t[s+1:],nm);children.append((f't{nm}',nm))
            lines.append(f'def t{name} : Audit := .split {steps} {slot(s)} (byMove [\n'+',\n'.join(a for a,_ in children)+'])')
            lines.append(f'''theorem h{name} : packedCheck {B} p{name} t{name} = true := by
  simp only [t{name}, packedCheck, Bool.and_eq_true]
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
            for v,(a,cname) in zip(ORDER,children):
                if cname is None:lines.append('  · decide +kernel')
                else:lines.append(f'''  · change packedCheck {B} (refine p{name} {slot(s)} (some {mov(v)})) {a} = true
    have hp : refine p{name} {slot(s)} (some {mov(v)}) = p{cname} := tableOK_sound _ _ (by decide +kernel)
    rw [hp]
    exact h{cname}''')
        if 'X' not in name:
            lines.extend([f'''theorem root{name} : p{name} initialSlot = some (some ⟨true,true,1⟩) := by decide +kernel
theorem nohalt{name} : weightedTNFNoAssignedHalt p{name} := by
  intro s
  unfold p{name} fromCodes
  cases h : ({t} : List Nat)[2 * s.1.val + s.2.toNat]? with
  | none => simp [h]
  | some n => by_cases hn : n < 24 <;> simp [h, hn]
theorem cover{name} : Cover (WeightedBound {B}) p{name} :=
  (certifiedPacked {B} p{name} t{name} root{name} nohalt{name} h{name}).toCover
#print axioms cover{name}'''])
        save(mod,lines);module_for[name]=mod
    for i,n,t in selected:
        size(n);build_sub(n,t,f'R{i}')
    print(f'{len(module_for)} tree modules and {len(set(block_module.values()))} block modules',flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('part',type=pathlib.Path);ap.add_argument('plan',type=pathlib.Path);ap.add_argument('census',type=pathlib.Path);ap.add_argument('out',type=pathlib.Path);ap.add_argument('--regions',default='small:600');ap.add_argument('--cap',type=int,default=600);a=ap.parse_args()
    plan=json.loads(a.plan.read_text());part=json.loads(a.part.read_text());census=json.loads(a.census.read_text())
    assert hashlib.sha256(a.part.read_bytes()).hexdigest()==plan['replay_sha256']
    ids=list(range(206)) if a.regions=='all' else [i for i,r in enumerate(plan['ordinary_regions']) if r['nodes']<=int(a.regions.removeprefix('small:'))] if a.regions.startswith('small:') else list(map(int,a.regions.split(',')))
    build(part,plan,census,a.out,ids,a.cap)
