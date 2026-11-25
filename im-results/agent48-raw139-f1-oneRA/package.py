import json, pathlib, sys
from collections import Counter
from blockcert import generate
from scan import tree, far, scan
from math import ceil

def pack(xs,b): return sum(v<<(b*i) for i,v in enumerate(xs))
def vec(xs,b,stride=16):
    return f'⟨{b},{stride},#['+','.join(hex(pack(xs[i:i+stride],b)) for i in range(0,len(xs),stride))+']⟩'
def rows(xs,b):
    k=max(1,max(map(len,xs)))
    return f'⟨{vec([pack([v+1 for v in x],b) for x in xs],b*k,8)},{b},{k}⟩'
def bl(x): return str(bool(x)).lower()
def slot(s): return f'({s//2},{bl(s%2)})'
def split_valid_source(s,d,ns):
    if d<10:return s.replace('by decide','by decide +kernel')
    old='theorem valid : cert.Valid machine := ⟨by decide,by decide,by decide⟩'
    rows='\n'.join(f'theorem row_{l} : cert.rowsAt machine ({l} : Fin {d}) = true := by decide +kernel' for l in range(d))
    proof=rows+f'\ntheorem rows_valid : cert.rowsCheck machine = true := by\n  unfold {ns}.Data.rowsCheck\n  rw [show List.finRange {d} = ({list(range(d))} : List (Fin {d})) by decide]\n  simp ['+', '.join(f'row_{l}' for l in range(d))+']\n'
    proof+='theorem valid : cert.Valid machine := ⟨by decide +kernel,by decide +kernel,rows_valid⟩'
    return s.replace(old,proof).replace('(by decide)','(by decide +kernel)')

def block_source(i,t,c):
    ns='BB6BlockFAR2' if c['width']==2 else 'BB6BlockFAR'
    d,n=c['left_states'],c['right_nodes']; b=max(d,n).bit_length()
    pb=(2**c['width']*d).bit_length()
    moves=', '.join('none' if m is None else f'some ⟨{bl(m[0])},{bl(m[1])},{m[2]}⟩' for m in c['moves'])
    source=f"""namespace BB6.Agent48F1OneRABlocks.H{i}
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
theorem valid : cert.Valid machine := ⟨by decide,by decide,by decide⟩
theorem forever : ∀ k, ∃ c, BB6BlockFAR.run machine k BB6BlockFAR.primBlank = some c :=
  cert.sound machine valid
def ctr : BB6Coverage.PartialMachine := BB6Coverage.FAR.fromCodes {t}
theorem same : ctr = BB6BlockFAR.partialTable machine :=
  BB6.Agent31ThreeHole.tableOK_sound _ _ (by decide)
theorem never (m : BB6Coverage.Machine) (hm : BB6Coverage.compatible ctr m) : BB6Coverage.NeverHalts m :=
  BB6BlockFAR.transfer_never machine m (by simpa only [← same] using hm) forever
#print axioms never
end BB6.Agent48F1OneRABlocks.H{i}
"""
    return split_valid_source(source,d,ns)
def make(spec,out,partition=None,blocks=None):
    counts=Counter();opens=[]
    if partition is None:
        tr=tree(spec['parent'],counts,opens,spec['limit'],spec['maxd'])
        assert dict(counts)==spec['counts']
    else: tr,opens=partition['tree'],partition['open']
    idx={tuple(t):i for i,t in enumerate(opens)}
    late={int(i):v for i,v in spec['late'].items()}
    fars={int(i):v for i,v in spec['far'].items()}
    params={i:v for v,inds in spec['block_groups'] for i in inds}
    assert set(params)|set(late)|set(fars)==set(range(len(opens)))
    assert len(params)+len(late)+len(fars)==len(opens)
    for i,(steps,s) in late.items():
        assert opens[i].count(24)==1 and scan(opens[i],steps)==('hole',steps,s)
    if blocks is None:
        blocks={i:generate(opens[i],*params[i],phase=i in spec['phase_indices']) for i in sorted(params)}
    assert all(blocks.values())
    out.mkdir(parents=True,exist_ok=True)
    modules=[]
    for j in range(0,len(params),8):
        name=f'Raw139OneRABlock{j//8:02}'
        modules.append(name)
        source='import BlockFAR2\nimport BlockFARBridge\nimport FastThreeHoleAudit\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n'
        for i in sorted(params)[j:j+8]: source+=block_source(i,opens[i],blocks[i])
        (out/(name+'.lean')).write_text(source)
    def far_node(a):
        rev,d,dfa,t0,t1,z=a
        return f'.far {bl(rev)} {d} ⟨0,{dfa},{t0},{t1},{z}⟩'
    def node(n):
        k,*a=n
        if k=='cycle':
            e,s,r,x=a; return f'.cycle {e} {s} {bl(r)} ({x})'
        if k=='last':
            steps,s=a;return f'.last {steps} {slot(s)}'
        if k=='far': return far_node(a)
        if k=='split':
            steps,s,children=a;return f'.split {steps} {slot(s)} (byMove [\n'+',\n'.join(map(node,children))+'])'
        if k=='open':
            i=idx[tuple(a[0])]
            if i in late: return node(('last',*late[i]))
            if i in fars: return far_node(far(a[0],*fars[i]))
            p=f'BB6.Agent48F1OneRABlocks.H{i}'
            return f'.proven {p}.ctr {p}.never'
        raise ValueError(k)
    b=spec['bound'];parent=spec['parent']
    source='import FastThreeHoleAudit\n'+''.join(f'import {m}\n' for m in modules)+f"""set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6.Agent48F1OneRA
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10FastAudit
def parent : PartialMachine := fromCodes {parent}
def tree : Audit := {node(tr)}
theorem checked : fastCheck {b} parent tree = true := by decide +kernel
theorem root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt parent := by
  intro s
  unfold parent fromCodes
  cases h : ({parent} : List Nat)[2 * s.1.val + s.2.toNat]? with
  | none => simp [h]
  | some n => by_cases hn : n < 24 <;> simp [h, hn]
noncomputable def certificate : WeightedTNFCertificate {b} parent 6 :=
  certifiedFast {b} parent tree root nohalt checked
theorem all_completions_weighted : ∀ m, compatible parent m → WeightedBound {b} m := certificate.sound
#print axioms checked
#print axioms all_completions_weighted
end BB6.Agent48F1OneRA
"""
    (out/'ChampionF1OneRACover.lean').write_text(source)
if __name__=='__main__':
    make(json.loads(pathlib.Path(sys.argv[1]).read_text()),pathlib.Path(sys.argv[2]))
