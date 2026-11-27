"""Emit chunked, kernel-reduced exact late arrival and attaining completion."""
from generate_digit_sections import M
from pathlib import Path
import sys

def emit(rows,out):
 M0=M(rows[256]);out=out.joinpath('Raw54OneRALate.lean')
 s=['import Raw54Base','set_option maxRecDepth 100000','set_option maxHeartbeats 0','namespace BB6.Agent8Raw54.OneRALate','open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6Coverage.Agent50Zipper BB6.Agent48PrefixAudit BB6Coverage.Agent10ZipAudit','abbrev parent : PartialMachine := refine BB6.Agent8Raw54.e1 (4,false) (some ⟨true,true,0⟩)','theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide','theorem parent_nohalt : weightedTNFNoAssignedHalt parent :=\n  weightedTNFNoAssignedHalt_refine _ _ _ (weightedTNFNoAssignedHalt_refine _ _ _\n    (weightedTNFNoAssignedHalt_refine _ _ _\n      (pathEnd_nohalt root 2 (path.take 3) firstOneCylinder_no_assigned_halt)))','namespace M39447']
 slots=[3,5,10,11]
 for i,j in enumerate(slots):
  b,d,q=M0.a[j];s.append(f'def p{i} : PartialMachine := refine '+('parent' if i==0 else f'p{i-1}')+f' ({j//2},{str(bool(j%2)).lower()}) (some ⟨{str(b=="1").lower()},{str(d=="R").lower()},{ord(q)-65}⟩)')
 s += ['abbrev table : PartialMachine := p3','def bits (s : String) : List Bool := s.toList.map (· == \'1\')','def cfg (q : Fin 6) (h : Int) (l r : String) : Z := ⟨q,h,bits l,bits r⟩']
 c=(0,'','');h=0;steps=0;start=0;last='start';s.append('theorem accum0 : zrun table 0 start = some start := rfl');i=0
 N=39446
 while steps<N:
  q,l,r=c;action=M0.a[2*q+int(l[0] if l else '0')];h+=1 if action[1]=='R' else -1;c=M0.step(*c);steps+=1
  if steps%500==0 or steps==N:
   i+=1;q,l,r=c;s.append(f'def z{i} : Z := cfg {q} ({h}) "{l}" "{r}"')
   s.append(f'theorem seg{i} : zrun table {steps-start} {last} = some z{i} := by rfl')
   s.append(f'theorem accum{i} : zrun table {steps} start = some z{i} := by\n  rw [show {steps}={start}+{steps-start} by decide,zrun_add,accum{i-1}]\n  exact seg{i}')
   start=steps;last=f'z{i}'
 assert c[0]==0 and c[1][0]=='1' and M0.step(*c) is None
 s += [f'theorem query : zipQueryOK 39447 table 39446 (0,true) = true := by\n  rw [← queryAt_eq 39447 table 39446 (0,true) {last} accum{i}]\n  decide','theorem rest : restOK table (0,true) = true := by decide','theorem checked : zipCheck 39447 table (.last 39446 (0,true)) = true := by\n  change (zipQueryOK 39447 table 39446 (0,true) && restOK table (0,true)) = true\n  rw [query,rest]; rfl','theorem root_ok : table initialSlot = some (some ⟨true,true,1⟩) := by decide','theorem nohalt : weightedTNFNoAssignedHalt table :=\n  weightedTNFNoAssignedHalt_refine _ _ _ (weightedTNFNoAssignedHalt_refine _ _ _\n    (weightedTNFNoAssignedHalt_refine _ _ _ (weightedTNFNoAssignedHalt_refine _ _ _ parent_nohalt)))','theorem cover : ∀ m, compatible table m → WeightedBound 39447 m :=\n  (certifiedZip 39447 table (.last 39446 (0,true)) root_ok nohalt checked).sound','def witness : Machine := weightedTNFDefaultCompletion (refine table (0,true) none)','theorem witness_parent : compatible parent witness := by\n  have h4 := weightedTNFDefaultCompletion_compatible (refine table (0,true) none)\n  have h3 : compatible table witness := refine_preserves_compat table witness (0,true) none (by decide) h4']
 for i,j in reversed(list(enumerate(slots))):
  b,d,q=M0.a[j];s.append(f'  have hc{i} : compatible '+('parent' if i==0 else f'p{i-1}')+f' witness := refine_preserves_compat '+('parent' if i==0 else f'p{i-1}')+f' witness ({j//2},{str(bool(j%2)).lower()}) (some ⟨{str(b=="1").lower()},{str(d=="R").lower()},{ord(q)-65}⟩) (by decide) '+('h3' if i==3 else f'hc{i+1}'))
 s += ['  exact hc0','theorem witness_halts : HaltsAfter witness 39446 := by\n  obtain ⟨hr,hh,_⟩ := zipQueryOK_sound query\n  have hm : compatible (refine table (0,true) none) witness := weightedTNFDefaultCompletion_compatible _\n  cases he : knownRun table 39446 with\n  | none => simp [he] at hr\n  | some c =>\n    have hs : readSlot c = (0,true) := by simpa [he] using hr\n    apply first_hole_halts table 39446 c he\n    · simpa [hs] using hh\n    · simpa [hs] using hm','theorem witness_delay : 0 ∈ delays (zeroNext witness) 0 := by decide','theorem attained : ∃ m, compatible parent m ∧ HaltsAfter m 39446 ∧ 0 ∈ delays (zeroNext m) 0 :=\n  ⟨witness,witness_parent,witness_halts,witness_delay⟩','#print axioms cover','#print axioms attained','end M39447','end BB6.Agent8Raw54.OneRALate']
 out.write_text('\n'.join(s)+'\n')
 from repair_oneRA_late import repair
 repair(out.parent, update_base=False)
if __name__=='__main__':
 emit(Path(sys.argv[1]).read_text().splitlines(),Path(sys.argv[2]))
