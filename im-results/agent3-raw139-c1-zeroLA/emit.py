import json, pathlib
from collections import Counter

def pack(xs,b): return sum(v<<(b*i) for i,v in enumerate(xs))
def vec(xs,b,stride=16): return f'⟨{b},{stride},#['+','.join(hex(pack(xs[i:i+stride],b)) for i in range(0,len(xs),stride))+']⟩'
def rows(xs,b):
    k=max(1,max(map(len,xs)))
    return f'⟨{vec([pack([v+1 for v in x],b) for x in xs],b*k,8)},{b},{k}⟩'
def bl(x): return str(bool(x)).lower()
def slot(s): return f'({s//2},{bl(s%2)})'
def block_source(i,t,c):
    ns='BB6BlockFAR2' if c['width']==2 else 'BB6BlockFAR'
    d,n=c['left_states'],c['right_nodes']; b=max(d,n).bit_length(); pb=(2**c['width']*d).bit_length()
    moves=', '.join('none' if m is None else f'some ⟨{bl(m[0])},{bl(m[1])},{m[2]}⟩' for m in c['moves'])
    s=f'''namespace BB6.Agent3Raw139C1ZeroLABlocks.H{i}
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
    if d<10: s+='theorem valid : cert.Valid machine := ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩\n'
    else:
        s+='\n'.join(f'theorem row_{l} : cert.rowsAt machine ({l} : Fin {d}) = true := by decide +kernel' for l in range(d))
        s+=f'\ntheorem rows_valid : cert.rowsCheck machine = true := by\n  unfold {ns}.Data.rowsCheck\n  rw [show List.finRange {d} = ({list(range(d))} : List (Fin {d})) by decide +kernel]\n  simp ['+', '.join(f'row_{l}' for l in range(d))+']\n'
        s+='theorem valid : cert.Valid machine := ⟨by decide +kernel,by decide +kernel,rows_valid⟩\n'
    return s+f'''theorem forever : ∀ k, ∃ c, BB6BlockFAR.run machine k BB6BlockFAR.primBlank = some c := cert.sound machine valid
def ctr : BB6Coverage.PartialMachine := BB6Coverage.FAR.fromCodes {t}
theorem same : ctr = BB6BlockFAR.partialTable machine := BB6.Agent31ThreeHole.tableOK_sound _ _ (by decide +kernel)
theorem never (m : BB6Coverage.Machine) (hm : BB6Coverage.compatible ctr m) : BB6Coverage.NeverHalts m :=
  BB6BlockFAR.transfer_never machine m (by simpa only [← same] using hm) forever
#print axioms never
end BB6.Agent3Raw139C1ZeroLABlocks.H{i}
'''

def emit(j,blocks,out):
    out.mkdir(parents=True,exist_ok=True); parent=j['parent']; opens=j['open']; idx={tuple(p):i for i,p in enumerate(opens)}; tr=j['tree']
    mods=[]; ids=sorted(map(int,blocks))
    for k in range(0,len(ids),8):
        name=f'Raw139C1ZeroLABlock{k//8:02}';mods.append(name)
        text='import BlockFAR2\nimport BlockFARBridge\nimport FastThreeHoleAudit\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n'
        for i in ids[k:k+8]: text+=block_source(i,opens[i],blocks[str(i)])
        (out/(name+'.lean')).write_text(text)
    def node(n):
        k,*a=n
        if k=='cycle':
            e,s,r,x=a; return f'.cycle {e} {s} {bl(r)} ({x})'
        if k=='last': return f'.last {a[0]} {slot(a[1])}'
        if k=='far':
            rev,d,dfa,t0,t1,z=a; return f'.far {bl(rev)} {d} ⟨0,{dfa},{t0},{t1},{z}⟩'
        if k=='split': return f'.split {a[0]} {slot(a[1])} (byMove [\n'+',\n'.join(map(node,a[2]))+'])'
        if k=='open':
            i=idx[tuple(a[0])]
            if i==9:return '.cycle 2075 10 true 39'
            p=f'BB6.Agent3Raw139C1ZeroLABlocks.H{i}';return f'.proven {p}.ctr {p}.never'
        raise ValueError(k)
    b=266; ns='BB6.Agent3Raw139C1ZeroLA'; imports='import FastThreeHoleAudit\n'+''.join(f'import {m}\n' for m in mods)
    common='set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n'+f'namespace {ns}\nopen BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10FastAudit\n'
    # Split the audit at its first query. Compose child theorems directly.
    assert tr[0]=='split'; steps,s,children=tr[1:]; order=[4*q+2*w+r for w in range(2) for r in range(2) for q in range(6)]
    for i,child in enumerate(children):
        p=parent.copy();p[s]=order[i];name=f'Raw139C1ZeroLABranch{i:02}'
        source=imports+common+f'def kid{i} : Audit := {node(child)}\ntheorem check{i} : fastCheck {b} (fromCodes {p}) kid{i} = true := by decide +kernel\nend {ns}\n'
        (out/(name+'.lean')).write_text(source)
    source=''.join(f'import Raw139C1ZeroLABranch{i:02}\n' for i in range(24))+common+f'''def parent : PartialMachine := fromCodes {parent}
theorem root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt parent := by
  intro s
  unfold parent fromCodes
  cases h : ({parent} : List Nat)[2 * s.1.val + s.2.toNat]? with
  | none => simp [h]
  | some n => by_cases hn : n < 24 <;> simp [h, hn]
'''
    for i,v in enumerate(order):
        p=parent.copy();p[s]=v; mv=f'⟨{bl(v&2)},{bl(v&1)},{v//4}⟩'; ref=f'refine parent {slot(s)} (some {mv})'
        source+=f'''theorem child_eq{i} : {ref} = fromCodes {p} := tableOK_sound _ _ (by decide)
theorem child{i} : ∀ m, compatible ({ref}) m → WeightedBound {b} m := by
  rw [child_eq{i}]
  exact (certifiedFast {b} (fromCodes {p}) kid{i} (by decide) (by rw [← child_eq{i}]; exact weightedTNFNoAssignedHalt_refine parent {slot(s)} {mv} nohalt) check{i}).sound
'''
    source+=f'''def c := (knownRun parent {steps}).getD blank
theorem run{steps} : knownRun parent {steps} = some c := by
  have h : (knownRun parent {steps}).isSome = true := by decide
  unfold c
  cases he : knownRun parent {steps} <;> simp_all
theorem read{steps} : readSlot c = {slot(s)} := by decide
theorem all_completions_weighted : ∀ m, compatible parent m → WeightedBound {b} m := by
  apply tnf_branch_sound {b} 6 parent {slot(s)} (by decide) (support6 parent) (by decide) (by decide) root
  · have hh : parent (readSlot c) = none := by rw [read{steps}]; decide
    have hw : ∀ d ∈ possibleDelays (refine parent (readSlot c) none) 0, d+{steps}+1 ≤ {b} := by
      rw [read{steps}]
      exact weightOK_sound parent {slot(s)} {steps} {b} (by decide)
    simpa only [read{steps}] using first_hole_weighted_halt {b} parent {steps} c root run{steps} hh hw
  · rintro ⟨w,r,q⟩ _
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> cases w <;> cases r
'''
    source+=''.join(f'    · exact child{i}\n' for q in range(6) for i in [q,q+6,q+12,q+18])
    source+=f'''  · intro q hq
    have h := q.isLt
    omega
theorem cover : Cover (WeightedBound {b}) parent := .leaf _ all_completions_weighted
#print axioms all_completions_weighted
#print axioms cover
end {ns}
'''
    (out/'Raw139C1ZeroLACover.lean').write_text(source)
if __name__=='__main__':
    emit(json.load(open('partition.json')),json.load(open('blocks.json')),pathlib.Path('generated'))
