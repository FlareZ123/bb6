import ZipAuditCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace BB6.Agent8Raw54.OneRA79
open BB6Coverage BB6Coverage.Agent10ZipAudit
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem checked : zipCycle table 4953 566 true 194 = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  zipCycle_sound table 4953 566 true 194 (by decide) checked m hm
#print axioms never
end BB6.Agent8Raw54.OneRA79
