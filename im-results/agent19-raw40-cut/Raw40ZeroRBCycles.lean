import ZipPrefixAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.ZeroRBCycles
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent48PrefixAudit

theorem zeroNever (m : Machine) (h : WeightedBound 0 m) : NeverHalts m := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    cases he : run m (n+1) blank with
    | some c => rfl
    | none =>
      have hd : 0 ∈ delays (zeroNext m) 0 := by
        apply List.mem_filter.mpr
        refine ⟨by decide, List.any_eq_true.mpr ?_⟩
        exact ⟨0,List.mem_finRange _,rfl⟩
      have H := h n 0 ⟨ih,he⟩ hd
      omega

namespace Leaf22
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem root : table initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt table := by
  intro s; rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide
theorem checked : zipCheck 0 table (.cycle 18 514 true (-3)) = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  zeroNever m ((certifiedZip 0 table (.cycle 18 514 true (-3)) root nohalt checked).sound m hm)
#print axioms never
end Leaf22
namespace Leaf390
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem root : table initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt table := by
  intro s; rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide
theorem checked : zipCheck 0 table (.cycle 257 396 true (-5)) = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  zeroNever m ((certifiedZip 0 table (.cycle 257 396 true (-5)) root nohalt checked).sound m hm)
#print axioms never
end Leaf390
end BB6.Agent19Raw40.ZeroRBCycles
