import CanonicalPartial
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent29Raw36
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent47PartialAudit BB6.Agent47CanonicalFrontier BB6.Agent19CanonicalPartial

abbrev parent : PartialMachine :=
  refine (pathEnd root 2 (path.take 2)).1 (3,false) (some ⟨false,false,3⟩)
abbrev d1 : PartialMachine := refine parent (3,true) (some ⟨true,false,1⟩)
abbrev branch : PartialMachine := refine d1 (1,true) (some ⟨false,false,0⟩)
abbrev child (mv : Move) : PartialMachine := refine branch (2,true) (some mv)

def literalParent : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨false,false,3⟩)
  | _,_ => none

theorem parent_literal : tableOK parent literalParent = true := by decide
theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem parent_nohalt : weightedTNFNoAssignedHalt parent :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 2) firstOneCylinder_no_assigned_halt)
theorem branch_root : branch initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem branch_nohalt : weightedTNFNoAssignedHalt branch :=
  weightedTNFNoAssignedHalt_refine _ _ _ (weightedTNFNoAssignedHalt_refine _ _ _ parent_nohalt)
theorem child_root (mv : Move) : child mv initialSlot = some (some ⟨true,true,1⟩) :=
  refine_preserves_firstOne branch (2,true) (some mv) (by decide) branch_root
theorem child_nohalt (mv : Move) : weightedTNFNoAssignedHalt (child mv) :=
  weightedTNFNoAssignedHalt_refine _ _ _ branch_nohalt
theorem parent_support : TNFSupport parent 4 := supportOK_sound _ _ (by decide)
def cut : PartialAudit := .split 5 (3,true) (byPartialMove [
  .unresolved,
  .unresolved,
  .unresolved,
  .closed (.cycle 7 1 false (-1)),
  .unresolved,
  .unresolved,
  .closed (.cycle 0 6 true (0)),
  .closed (.cycle 1 5 true (1)),
  .closed (.cycle 12 1 false (2)),
  .closed (.cycle 9 1 false (1)),
  .unresolved,
  .unresolved,
  .unresolved,
  .split 6 (1,true) (byPartialMove [.unresolved,
    .unresolved,
    .closed (.cycle 8 1 false (0)),
    .closed (.cycle 7 1 false (-1)),
    .unresolved,
    .unresolved,
    .unresolved,
    .unresolved,
    .unresolved,
    .unresolved,
    .unresolved,
    .unresolved,
    .unresolved,
    .unresolved,
    .unresolved,
    .closed (.cycle 7 1 false (-1)),
    .unresolved,
    .unresolved,
    .unresolved,
    .closed (.cycle 1 7 true (0)),
    .unresolved,
    .closed (.cycle 5 2 true (0)),
    .unresolved,
    .unresolved]),
  .unresolved,
  .closed (.cycle 7 1 false (-1)),
  .unresolved,
  .unresolved,
  .closed (.cycle 0 6 true (0)),
  .closed (.cycle 1 5 true (1)),
  .closed (.cycle 2 4 true (1)),
  .closed (.cycle 4 2 true (1)),
  .unresolved,
  .unresolved])
theorem checked : canonicalCheck 162 parent 4 cut = true := by decide
def remaining := canonicalResiduals parent 4 cut
theorem remaining_count : remaining.length = 24 := by decide
theorem root_entries : remaining.all (fun e => decide (e.2 initialSlot = some (some ⟨true,true,1⟩))) = true := by decide
theorem sound (m : Machine) (hm : TNFQuotientCompatible parent m) :
    WeightedBound 162 m ∨ ∃ e ∈ remaining, TNFQuotientCompatible e.2 m :=
  canonicalSound 162 parent 4 cut (by decide) parent_support parent_root parent_nohalt checked m hm
theorem cover {B : Nat} (hB : 162 ≤ B)
    (hRest : ∀ e ∈ remaining, Cover (WeightedBound B) e.2) : Cover (WeightedBound B) parent := by
  apply Cover.leaf
  intro m hm
  rcases sound m (compatible_quotient hm) with hb | ⟨e,he,hq⟩
  · intro k d hk hd
    exact Nat.le_trans (hb k d hk hd) hB
  · have hf := of_decide_eq_true (List.all_eq_true.mp root_entries e he)
    exact quotientSafe hf (hRest e he).sound m hq
#print axioms parent_literal
#print axioms remaining_count
#print axioms sound
#print axioms cover
end BB6.Agent29Raw36
