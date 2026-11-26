"""Emit concrete instances of the verified binary-counter core."""
import json,sys
from pathlib import Path
print('import Raw40DigitCore\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace BB6.Agent19Raw40.DigitLeaves\nopen BB6Coverage BB6Coverage.Agent31Pump BB6.Agent19Raw40.DigitCore')
for line in Path(sys.argv[1]).read_text().splitlines():
 i,s,q,frame,anchor,t,r,u,v,entry,initial=json.loads(line)
 frame='['+','.join(str(b).lower() for b in frame)+']'
 print(f'\nnamespace Leaf{i}\n-- {s}\ndef table : PartialMachine := fun s =>\n  match s.1.val,s.2 with')
 for k in range(12):
  a=s[3*k:3*k+3]
  if a=='---':continue
  print(f'  | {k//2},{str(bool(k%2)).lower()} => some (some ⟨{str(a[0]=="1").lower()},{str(a[1]=="R").lower()},{ord(a[2])-65}⟩)')
 print(f'''  | _,_ => none

theorem core : Core table {q} {frame} {anchor} {t} {r} {u} {v} := by
  constructor <;> intros <;> rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  DigitCore.never table {q} {frame} {anchor} {t} {r} {u} {v} core {entry} {initial} (by rfl) m hm
#print axioms never
end Leaf{i}''')
print('end BB6.Agent19Raw40.DigitLeaves')
