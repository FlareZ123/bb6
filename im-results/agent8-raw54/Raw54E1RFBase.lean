import Raw54Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.E1RF
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
abbrev parent : PartialMachine := refine BB6.Agent8Raw54.raw54 (4,true) (some ⟨false,true,5⟩)
theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem parent_nohalt : weightedTNFNoAssignedHalt parent :=
  weightedTNFNoAssignedHalt_refine _ _ _ (weightedTNFNoAssignedHalt_refine _ _ _
    (pathEnd_nohalt root 2 (path.take 3) firstOneCylinder_no_assigned_halt))
namespace Attainer
abbrev p0 := refine parent (0,true) (some ⟨false,false,2⟩)
abbrev p1 := refine p0 (2,true) (some ⟨false,true,2⟩)
abbrev p2 := refine p1 (4,false) (some ⟨true,false,5⟩)
abbrev p3 := refine p2 (5,false) (some ⟨true,true,2⟩)
abbrev table := refine p3 (5,true) (some ⟨true,false,0⟩)
theorem query : zipQueryOK 840 table 839 (1,true) = true := by decide
def witness : Machine := weightedTNFDefaultCompletion (refine table (1,true) none)
theorem witness_parent : compatible parent witness := by
  have h := weightedTNFDefaultCompletion_compatible (refine table (1,true) none)
  have h4 := refine_preserves_compat table witness (1,true) none (by decide) h
  have h3 := refine_preserves_compat p3 witness (5,true) (some ⟨true,false,0⟩) (by decide) h4
  have h2 := refine_preserves_compat p2 witness (5,false) (some ⟨true,true,2⟩) (by decide) h3
  have h1 := refine_preserves_compat p1 witness (4,false) (some ⟨true,false,5⟩) (by decide) h2
  have h0 := refine_preserves_compat p0 witness (2,true) (some ⟨false,true,2⟩) (by decide) h1
  exact refine_preserves_compat parent witness (0,true) (some ⟨false,false,2⟩) (by decide) h0
theorem witness_halts : HaltsAfter witness 839 := by
  obtain ⟨hr,hh,_⟩ := zipQueryOK_sound query
  have hm : compatible (refine table (1,true) none) witness := weightedTNFDefaultCompletion_compatible _
  cases he : knownRun table 839 with
  | none => simp [he] at hr
  | some c =>
    have hs : readSlot c = (1,true) := by simpa [he] using hr
    apply first_hole_halts table 839 c he
    · simpa [hs] using hh
    · simpa [hs] using hm
theorem witness_delay : 0 ∈ delays (zeroNext witness) 0 := by decide
theorem attained : ∃ m, compatible parent m ∧ HaltsAfter m 839 ∧ 0 ∈ delays (zeroNext m) 0 :=
  ⟨witness,witness_parent,witness_halts,witness_delay⟩
#print axioms attained
end Attainer
end BB6.Agent8Raw54.E1RF
