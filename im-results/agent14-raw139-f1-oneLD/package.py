import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'agent48-raw139-f1-oneLA'))
from pathlib import Path
from scan import far
from emitproof import emit
import json,re
D=json.load(open('f1-14-600.json')); idx={tuple(p):i for i,p in enumerate(D['open'])}
def b(x):return str(bool(x)).lower()
def node(t):
 k,*v=t
 if k=='cycle':a,n,d,z=v;return f'.cycle {a} {n} {b(d)} ({z})'
 if k=='last':n,s=v;return f'.last {n} ({s//2},{b(s%2)})'
 if k=='split':n,s,children=v;return f'.split {n} ({s//2},{b(s%2)}) (byMove [\n'+',\n'.join(map(node,children))+'])'
 if k=='open':
  i=idx[tuple(v[0])]
  return f'.proven BB6.Agent14OneLD.H{i}.ctr BB6.Agent14OneLD.H{i}.never'
 if k=='far':d,n,dfa,t0,t1,z=v;return f'.far {b(d)} {n} ⟨0,{dfa},{t0},{t1},{z}⟩'
 raise ValueError(t)
head='import SweepPumping\nimport F0SiblingCover\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace BB6.Agent14OneLD\nopen BB6Coverage BB6Coverage.Agent31Pump\n'
parts=[]
for path in sorted(Path('.').glob('pump-*.json')):
 s=emit(path);i=path.stem.split('-')[1];a,b0=map(int,re.search(r'theorem growth \(n : Nat\) : run0 ctr \((\d+)\*n\+(\d+)\)',s).groups());t=json.load(open(path))['result'][0]
 s=s.replace(f'#print axioms growth\nend H{i}',f'theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=\n  never_of_growth ctr family {t} (fun n => {a}*n+{b0}) entry (fun k => by omega) growth m hm\n#print axioms growth\n#print axioms never\nend H{i}');parts.append(s)
Path('Agent14OneLDHard.lean').write_text(head+'\n\n'.join(parts)+'\nend BB6.Agent14OneLD\n')
Path('Agent14OneLDCover.lean').write_text('''import FastThreeHoleAudit
import Agent14OneLDHard
import Agent14OneLDCarry
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6.Agent14F1OneLD
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10FastAudit

def parent : PartialMachine := fromCodes '''+str(D['parent'])+'''
def tree : Audit := '''+node(D['tree'])+'''
theorem checked : fastCheck 264 parent tree = true := by decide
theorem root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt parent := by
  intro s
  unfold parent fromCodes
  cases h : (['''+','.join(map(str,D['parent']))+'''] : List Nat)[2 * s.1.val + s.2.toNat]? with
  | none => simp [h]
  | some n => by_cases hn : n < 24 <;> simp [h, hn]
noncomputable def certificate : WeightedTNFCertificate 264 parent 6 :=
  certifiedFast 264 parent tree root nohalt checked
theorem all_completions_weighted : ∀ m, compatible parent m → WeightedBound 264 m := certificate.sound
#print axioms checked
#print axioms all_completions_weighted
end BB6.Agent14F1OneLD
''')
