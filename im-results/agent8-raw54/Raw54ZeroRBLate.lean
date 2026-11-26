import Raw54Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.ZeroRBLate
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit

abbrev parent : PartialMachine := refine BB6.Agent8Raw54.e1 (4,false) (some ⟨false,true,1⟩)
theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem parent_nohalt : weightedTNFNoAssignedHalt parent :=
  weightedTNFNoAssignedHalt_refine _ _ _ (weightedTNFNoAssignedHalt_refine _ _ _
    (weightedTNFNoAssignedHalt_refine _ _ _
      (pathEnd_nohalt root 2 (path.take 3) firstOneCylinder_no_assigned_halt)))

namespace M390
def p0 : PartialMachine := refine parent (1,true) (some ⟨false,true,5⟩)
def p1 : PartialMachine := refine p0 (2,true) (some ⟨true,false,5⟩)
def p2 : PartialMachine := refine p1 (5,false) (some ⟨true,true,0⟩)
def p3 : PartialMachine := refine p2 (5,true) (some ⟨false,false,5⟩)

abbrev table : PartialMachine := p3
theorem root_ok : table initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt table :=
  weightedTNFNoAssignedHalt_refine _ _ _ (weightedTNFNoAssignedHalt_refine _ _ _
    (weightedTNFNoAssignedHalt_refine _ _ _ (weightedTNFNoAssignedHalt_refine _ _ _ parent_nohalt)))
theorem query : zipQueryOK 390 table 389 (0,true) = true := by decide
theorem rest : restOK table (0,true) = true := by decide
theorem checked : zipCheck 390 table (.last 389 (0,true)) = true := by
  change (zipQueryOK 390 table 389 (0,true) && restOK table (0,true)) = true
  rw [query,rest]
  rfl
theorem cover : ∀ m, compatible table m → WeightedBound 390 m :=
  (certifiedZip 390 table (.last 389 (0,true)) root_ok nohalt checked).sound
def witness : Machine := weightedTNFDefaultCompletion (refine table (0,true) none)
theorem witness_parent : compatible parent witness := by
  have h4 := weightedTNFDefaultCompletion_compatible (refine table (0,true) none)
  have h3 : compatible table witness := refine_preserves_compat table witness (0,true) none (by decide) h4
  have hc3 : compatible p2 witness := refine_preserves_compat p2 witness (5,true) (some ⟨false,false,5⟩) (by decide) h3
  have hc2 : compatible p1 witness := refine_preserves_compat p1 witness (5,false) (some ⟨true,true,0⟩) (by decide) hc3
  have hc1 : compatible p0 witness := refine_preserves_compat p0 witness (2,true) (some ⟨true,false,5⟩) (by decide) hc2
  have hc0 : compatible parent witness := refine_preserves_compat parent witness (1,true) (some ⟨false,true,5⟩) (by decide) hc1
  exact hc0
theorem witness_halts : HaltsAfter witness 389 := by
  obtain ⟨hr,hh,_⟩ := zipQueryOK_sound query
  have hm : compatible (refine table (0,true) none) witness := weightedTNFDefaultCompletion_compatible _
  cases he : knownRun table 389 with
  | none => simp [he] at hr
  | some c =>
    have hs : readSlot c = (0,true) := by simpa [he] using hr
    apply first_hole_halts table 389 c he
    · simpa [hs] using hh
    · simpa [hs] using hm
theorem witness_delay : 0 ∈ delays (zeroNext witness) 0 := by decide
theorem attained : ∃ m, compatible parent m ∧ HaltsAfter m 389 ∧ 0 ∈ delays (zeroNext m) 0 :=
  ⟨witness,witness_parent,witness_halts,witness_delay⟩
#print axioms cover
#print axioms attained
end M390

end BB6.Agent8Raw54.ZeroRBLate
