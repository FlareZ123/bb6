"""Reuse the box4 certificate pipeline for the C1=2 subrectangle of box3.
Run from any directory. Generated modules are uniquely named Box3C2*.
"""
from pathlib import Path
import re,sys,subprocess
HERE=Path(__file__).resolve().parent
BASE=HERE.parent/'agent13-raw10-box4'
def generate():
    for n in ('scan.cpp','classify.cpp','treegen.cpp','finish.py','greedy.py','emit_proof.py','replay.py','Box4Core.lean','Box4Tree.lean'):
        s=(BASE/n).read_text()
        s=s.replace('8,14,11,7,17,4','8,14,11,7,17,2').replace('if(i!=6||v!=9)','').replace(' if i!=6 or v!=9','').replace('[ALL^(1<<9)]+[ALL]*5','[ALL]*6')
        if n.endswith('.lean') or n=='emit_proof.py':
            s=s.replace('Box4','Box3C2').replace('3640','3592')
            s=s.replace('raw10Remainder[4]!','sourceDomain')
        if n=='Box4Core.lean':
            a=s.index('def literalDomain')
            b=s.index('def sliceDomain',a)
            s=s[:a]+'''def literalDomain (i : Fin 12) : List (Fin 25) :=
  match i.val with
  | 0 => [8]
  | 1 => [14]
  | 2 => [11]
  | 3 => [7]
  | 4 => [17]
  | 5 => [2]
  | _ => List.finRange 25

def domain : Box Slot Transition := fun s => (literalDomain (index s)).map decode

def sourceDomain : Box Slot Transition := fun s =>
  if index s = 5 then [decode 2] else raw10Remainder[3]! s

theorem literalDomain_matches : ∀ i : Fin 12, literalDomain i =
    if i = 5 then [2] else BB6.Agent49BoxEncoded.boxes[3]! i := by decide

theorem index_source (s : Slot) : index s = BB6.Agent17Raw10BoxFar.slotIndex s := by
  rcases s with ⟨q,b⟩
  revert q b
  decide

theorem decode_source (v : Fin 25) : decode v = BB6.Agent17Raw10BoxFar.decodeCode v := by
  revert v
  decide

theorem sourceDomainEq : domain = sourceDomain := by
  funext s
  have h := BB6.Agent17Raw10BoxFar.exact_box_at_index (3 : Fin 34) s
  change raw10Remainder[3]! s =
    (BB6.Agent49BoxEncoded.boxes[3]! (BB6.Agent17Raw10BoxFar.slotIndex s)).map BB6.Agent17Raw10BoxFar.decodeCode at h
  unfold domain sourceDomain
  rw [literalDomain_matches]
  by_cases hi : index s = 5
  · simp [hi]
  · simp only [if_neg hi]
    rw [h,index_source]
    rw [show decode = BB6.Agent17Raw10BoxFar.decodeCode from funext decode_source]

theorem source_subset : ∀ s v, v ∈ sourceDomain s → v ∈ raw10Remainder[3]! s := by
  intro s v hv
  by_cases hi : index s = 5
  · have hs : s = slot 5 := by rw [← slot_index s,hi]
    subst s
    have hm : decode 2 ∈ raw10Remainder[3]! (slot 5) := by decide
    simp [sourceDomain,index_slot] at hv
    rw [hv]
    exact hm
  · simpa [sourceDomain,hi] using hv

''' +s[b:]
        (HERE/n.replace('Box4','Box3C2')).write_text(s)
    lower=(BASE/'Box4Lower.lean').read_text().replace('Box4','Box3C2').replace('3640','3592').replace('3639','3591').replace('raw10Remainder[4]!','sourceDomain')
    t=[8,14,11,7,17,2,12,4,15,23,9,0]
    def move(v):
        if v==0:return 'some none'
        return f'some (some ⟨{str((v-1)//2%2==1).lower()},{str((v-1)%2==1).lower()},{(v-1)//4}⟩)'
    a=lower.index('def late :');b=lower.index('def lateMachine',a)
    lower=lower[:a]+'def late : PartialMachine := fun s => match s with\n'+''.join(f'  | ({i//2},{str(i%2==1).lower()}) => {move(v)}\n' for i,v in enumerate(t))+'  | _ => none\n\n'+lower[b:]
    (HERE/'Box3C2Lower.lean').write_text(lower)
if __name__=='__main__':
    generate()
    if '--prepare-only' not in sys.argv:
        subprocess.run([sys.executable,str(HERE/'replay.py'),'/tmp/a13-box3-c2-replay'],check=True)
