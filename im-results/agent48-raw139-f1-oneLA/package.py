from pathlib import Path
from scan import far
from emitproof import emit
import json,re
D=json.load(open('f1-2-600.json')); idx={tuple(p):i for i,p in enumerate(D['open'])}
def b(x):return str(bool(x)).lower()
def node(t):
 k,*v=t
 if k=='cycle':a,n,d,z=v;return f'.cycle {a} {n} {b(d)} ({z})'
 if k=='last':n,s=v;return f'.last {n} ({s//2},{b(s%2)})'
 if k=='split':n,s,children=v;return f'.split {n} ({s//2},{b(s%2)}) (byMove [\n'+',\n'.join(map(node,children))+'])'
 if k=='open':
  i=idx[tuple(v[0])]
  if i==7:return node(('far',*far(v[0],1,[0,1,2,3,4,1,5,3,4,4,0,1])))
  return f'.proven BB6.Agent48OneLA.H{i}.ctr BB6.Agent48OneLA.H{i}.never'
 if k=='far':d,n,dfa,t0,t1,z=v;return f'.far {b(d)} {n} ⟨0,{dfa},{t0},{t1},{z}⟩'
 raise ValueError(t)
head='import SweepPumping\nimport F0SiblingCover\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace BB6.Agent48OneLA\nopen BB6Coverage BB6Coverage.Agent31Pump\n'
parts=[]
for path in sorted(Path('.').glob('pump-*.json')):
 s=emit(path);i=path.stem.split('-')[1];a,b0=map(int,re.search(r'theorem growth \(n : Nat\) : run0 ctr \((\d+)\*n\+(\d+)\)',s).groups());t=json.load(open(path))['result'][0]
 s=s.replace(f'#print axioms growth\nend H{i}',f'theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=\n  never_of_growth ctr family {t} (fun n => {a}*n+{b0}) entry (fun k => by omega) growth m hm\n#print axioms growth\n#print axioms never\nend H{i}');parts.append(s)
Path('ChampionF1OneLAHard.lean').write_text(head+'\n\n'.join(parts)+'\nend BB6.Agent48OneLA\n')
Path('ChampionF1OneLACover.lean').write_text('''import FastThreeHoleAudit
import ChampionF1OneLAHard
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6.Agent48F1OneLA
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10FastAudit

def parent : PartialMachine := fromCodes '''+str(D['parent'])+'''
def tree : Audit := '''+node(D['tree'])+'''
theorem checked : fastCheck 290 parent tree = true := by decide
theorem root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt parent := by
  intro s
  unfold parent fromCodes
  cases h : (['''+','.join(map(str,D['parent']))+'''] : List Nat)[2 * s.1.val + s.2.toNat]? with
  | none => simp [h]
  | some n => by_cases hn : n < 24 <;> simp [h, hn]
noncomputable def certificate : WeightedTNFCertificate 290 parent 6 :=
  certifiedFast 290 parent tree root nohalt checked
theorem all_completions_weighted : ∀ m, compatible parent m → WeightedBound 290 m := certificate.sound
#print axioms checked
#print axioms all_completions_weighted
end BB6.Agent48F1OneLA
''')
