from pathlib import Path
import re,sys
names=sys.argv[1:]; inp=dict(l.split() for l in Path('canon_batches/inputs.txt').read_text().splitlines()); info=[]
for name in names:
    mod='Raw40C'+name.replace('_','');d=Path('canon_batches')/name
    B,n,delay,code=re.search(r'maxscore=(\d+) n=(\d+) delay=(\d+) table=(\S+)',(d/'stats.txt').read_text()).groups();info.append((mod,B,n,delay,code))
print('import Raw40Batch');print('\n'.join('import '+m+'All' for m,*_ in info))
print('''set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement BB6.Agent31FourHoleRoster BB6.Agent50TNFPilot
''')
for m,B,n,d,code in info:
    print(f'def {m}Witness : Machine := fun s =>\n  match s.1.val,s.2 with')
    for i,v in enumerate(re.findall('...',code.replace('_',''))):
        if v!='HHH' and v!='---':print(f'  | {i//2},{str(bool(i%2)).lower()} => some ⟨{str(v[0]=="1").lower()},{str(v[1]=="R").lower()},{ord(v[2])-65}⟩')
    print(f'''  | _,_ => none

theorem {m}_witness_compatible : compatible {m}.p {m}Witness := by
  intro s t ht
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> first
    | have h : {m}.p (_,_) = none := by decide; rw [h] at ht; contradiction
    | cases ht <;> rfl

theorem {m}_witness_halts : HaltsAfter {m}Witness {n} := by
  constructor <;> rfl

theorem {m}_witness_delay : {d} ∈ delays (zeroNext {m}Witness) 0 := by decide

theorem {m}_exact_weighted : (∀ m, compatible {m}.p m → WeightedBound {B} m) ∧
    ∀ B < {B}, ∃ m, compatible {m}.p m ∧ ¬ WeightedBound B m := by
  refine ⟨{m}.all,?_⟩
  intro B hB
  refine ⟨{m}Witness,{m}_witness_compatible,?_⟩
  intro hb
  have h := hb {n} {d} {m}_witness_halts {m}_witness_delay
  omega
#print axioms {m}_exact_weighted
''')
print('def closedBatch : List PartialMachine := ['+','.join(m+'.p' for m,*_ in info)+']')
print('''theorem closedBatch_sound : ∀ p ∈ closedBatch, ∀ m, TNFQuotientCompatible p m → WeightedBound 7014 m := by
  intro p hp
  simp only [closedBatch,List.mem_cons,List.not_mem_nil,or_false] at hp''')
print('  '+('rcases hp with '+'|'.join(['rfl']*len(info)) if len(info)>1 else 'subst p'))
for m,*_ in info: print(f'  · intro m hm k d hk hd\n    exact Nat.le_trans ({m}.all_quotient m hm k d hk hd) (by decide)')
print(f'''
theorem closedBatch_count : (batchRemaining closedBatch).length = {188-len(info)} := by decide

theorem closedBatch_roster_count : (batchRoster closedBatch).length = {264-len(info)} := by decide

theorem closedBatch_roster_sound : ∀ m, compatible root m → WeightedBound 7014 m ∨
    ∃ e ∈ batchRoster closedBatch, TNFQuotientCompatible e.2 m :=
  batch_roster_sound closedBatch closedBatch_sound

#print axioms closedBatch_roster_sound
end BB6.Agent19Raw40
''')
