"""Generate the E0=0LC, D0=0RC, C1=0LF exact parent Cover.
Run from this directory or specify an output directory. Reuses the established
first-hole scan and block-FAR witness search; Lean checks every witness.
"""
import json,pathlib,sys
from collections import Counter
root=pathlib.Path(__file__).resolve().parents[1]
sys.path[:0]=[str(root/'agent48-raw139-f1-oneLA'),str(root/'agent48-raw139-f1-oneRA')]
from scan import far,tree
from blockcert import generate

def pack(xs,b): return sum(v<<(b*i) for i,v in enumerate(xs))
def vec(xs,b,stride=16): return f'⟨{b},{stride},#['+','.join(hex(pack(xs[i:i+stride],b)) for i in range(0,len(xs),stride))+']⟩'
def rows(xs,b):
 k=max(1,max(map(len,xs)));return f'⟨{vec([pack([v+1 for v in x],b) for x in xs],b*k,8)},{b},{k}⟩'
def bl(x):return str(bool(x)).lower()
def slot(s):return f'({s//2},{bl(s%2)})'
P=[7,24,11,24,14,20,9,16,8,11,24,24]
NS='BB6.Agent6E0ZeroLC.D0ZeroRC.C1ZeroLF'
params={3:(2,2,2,2),4:(2,1,2,2),5:(2,1,2,2)}
counts=Counter();opens=[];tr=tree(P,counts,opens,250,2)
assert dict(counts)=={'maxquery':78,'split':33,'cycle':599,'last':138,'far':15,'open':8}
idx={tuple(t):i for i,t in enumerate(opens)}
source='''import BlockFAR2
import BlockFARBridge
import FastThreeHoleAudit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
'''
for i,par in params.items():
 t=opens[i];c=generate(t,*par);assert c
 d,n=c['left_states'],c['right_nodes'];b=max(d,n).bit_length();pb=(4*d).bit_length()
 moves=', '.join('none' if m is None else f'some ⟨{bl(m[0])},{bl(m[1])},{m[2]}⟩' for m in c['moves'])
 source+=f'''namespace {NS}.H{i}
def machine : BB6BlockFAR.Table := fun q b => ([{moves}] : List (Option BB6BlockFAR.Move))[2*q.val+b.toNat]?.getD none
def cert : BB6BlockFAR2.Data {d-1} {n-1} := {{
  start := 0
  pushCodes := {vec(c['push'],b)}
  controlCodes := {vec(c['ctrl'],b)}
  auxiliaryCodes := {vec(c['aux'],b)}
  predecessorCodes := {rows(c['pred'],pb)}
  edgeCodes := {rows(c['edges'],b)}
  zeroCodes := {sum(1<<x for x in c['zero_states'])}
  zeroNextCodes := {vec(c['zeroNext'],b)}
}}
theorem valid : cert.Valid machine := ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩
theorem forever : ∀ k, ∃ c, BB6BlockFAR.run machine k BB6BlockFAR.primBlank = some c :=
  cert.sound machine valid
def ctr : BB6Coverage.PartialMachine := BB6Coverage.FAR.fromCodes {t}
theorem same : ctr = BB6BlockFAR.partialTable machine :=
  BB6.Agent31ThreeHole.tableOK_sound _ _ (by decide)
theorem never (m : BB6Coverage.Machine) (hm : BB6Coverage.compatible ctr m) : BB6Coverage.NeverHalts m :=
  BB6BlockFAR.transfer_never machine m (by simpa only [← same] using hm) forever
#print axioms never
end {NS}.H{i}
'''

def node(t):
 k,*a=t
 if k=='cycle':e,s,r,x=a;return f'.cycle {e} {s} {bl(r)} ({x})'
 if k=='last':n,s=a;return f'.last {n} {slot(s)}'
 if k=='far':rev,d,dfa,t0,t1,z=a;return f'.far {bl(rev)} {d} ⟨0,{dfa},{t0},{t1},{z}⟩'
 if k=='split':n,s,children=a;return f'.split {n} {slot(s)} (byMove [\n'+',\n'.join(map(node,children))+'])'
 if k=='open':
  i=idx[tuple(a[0])]
  if i in params:return f'.proven {NS}.H{i}.ctr {NS}.H{i}.never'
  c=far(a[0],0,[0,1,2,1,2,2]);assert c;return node(('far',*c))
 raise ValueError(t)
source+=f'''namespace {NS}
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10FastAudit
def parent : PartialMachine := fromCodes {P}
def tree : Audit := {node(tr)}
theorem checked : fastCheck 84 parent tree = true := by decide +kernel
theorem root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt parent := by
  intro s
  unfold parent fromCodes
  cases h : ({P} : List Nat)[2 * s.1.val + s.2.toNat]? with
  | none => simp [h]
  | some n => by_cases hn : n < 24 <;> simp [h, hn]
noncomputable def certificate : WeightedTNFCertificate 84 parent 6 :=
  certifiedFast 84 parent tree root nohalt checked
theorem all_completions_weighted : ∀ m, compatible parent m → WeightedBound 84 m := certificate.sound
#print axioms checked
#print axioms all_completions_weighted
end {NS}
'''
out=pathlib.Path(sys.argv[1]) if len(sys.argv)>1 else pathlib.Path.cwd()
out.mkdir(parents=True,exist_ok=True)
(out/'Raw139E0ZeroLCD0ZeroRCC1ZeroLF.lean').write_text(source)
