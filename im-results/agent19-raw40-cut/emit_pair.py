"""Emit concrete instances of the kernel-checked nested core theorem."""
import json,sys
from pathlib import Path
print('import Raw40PairCore\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace BB6.Agent19Raw40.PairLeaves\nopen BB6Coverage BB6Coverage.Agent31Pump BB6.Agent19Raw40.NestedCore BB6.Agent19Raw40.PairCore')
for line in Path(sys.argv[1]).read_text().splitlines():
 i,s,z,t,u,entry,initial=json.loads(line)
 print(f'\nnamespace Leaf{i}\n-- {s}\ndef table : PartialMachine := fun s =>\n  match s.1.val,s.2 with')
 for k in range(12):
  v=s[3*k:3*k+3]
  if v=='---':continue
  print(f'  | {k//2},{str(bool(k%2)).lower()} => some (some ⟨{str(v[0]=="1").lower()},{str(v[1]=="R").lower()},{ord(v[2])-65}⟩)')
 print(f'''  | _,_ => none

theorem core : Core table := by constructor <;> rfl

theorem boundary : Boundary2 table {z} {t} {u} := by
  constructor <;> intros <;> rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  PairCore.never2 table core {z} {t} {u} boundary {entry} {initial} (by rfl) m hm
#print axioms never
end Leaf{i}''')
print('end BB6.Agent19Raw40.PairLeaves')
