import CanonicalPartial
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43B0LA
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent8TNFPath
def p : PartialMachine :=
  refine (refine (pathEnd root 2 (path.take 3)).1 (3,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨false,false,0⟩)
def tree : PartialAudit := .split 9 (2,true) (byPartialMove [
  .unresolved,
  .unresolved,
  .closed (.cycle 14 1 false (0)),
  .closed (.cycle 1 10 true (1)),
  .unresolved,
  .unresolved,
  .closed (.cycle 0 10 true (0)),
  .closed (.cycle 1 9 true (1)),
  .closed (.far false 2 ⟨0,[0,1,0,1],[128,256,8,4,4096,4096,128,256,8,256,4096,4096,4096],[4096,256,4,2,4096,4096,4096,4096,4,2,4096,4096,4096],7216⟩),
  .closed (.cycle 3 7 true (1)),
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .closed (.cycle 10 8 true (-1)),
  .closed (.cycle 0 12 true (0)),
  .unresolved,
  .unresolved,
  .closed (.cycle 0 10 true (0)),
  .closed (.cycle 1 9 true (1)),
  .closed (.cycle 2 8 true (1)),
  .closed (.cycle 0 13 true (0)),
  .unresolved,
  .unresolved])
def remaining := canonicalResiduals p 4 tree
theorem root_entry : p initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt p :=
  weightedTNFNoAssignedHalt_refine _ _ _ (weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 3) firstOneCylinder_no_assigned_halt))
theorem support : TNFSupport p 4 := supportOK_sound _ _ (by decide)
theorem checked : canonicalCheck 1771 p 4 tree = true := by decide
theorem remaining_count : remaining.length = 8 := by decide
theorem root_entries : remaining.all (fun e => decide (e.2 initialSlot = some (some ⟨true,true,1⟩))) = true := by decide
theorem sound (m : Machine) (hm : TNFQuotientCompatible p m) :
    WeightedBound 1771 m ∨ ∃ e ∈ remaining, TNFQuotientCompatible e.2 m :=
  canonicalSound 1771 p 4 tree (by decide) support root_entry nohalt checked m hm
def equalTable (p q : PartialMachine) : Bool :=
  (List.finRange 6).all fun i => [false,true].all fun b => decide (p (i,b) = q (i,b))
theorem equalTable_sound {p q : PartialMachine} (h : equalTable p q = true) : p = q := by
  funext s
  rcases s with ⟨i,b⟩
  have hi := List.all_eq_true.mp h i (List.mem_finRange i)
  have hb : b ∈ [false,true] := by cases b <;> simp
  exact of_decide_eq_true (List.all_eq_true.mp hi b hb)
#print axioms remaining_count
#print axioms sound
end BB6.Agent25Raw43B0LA
