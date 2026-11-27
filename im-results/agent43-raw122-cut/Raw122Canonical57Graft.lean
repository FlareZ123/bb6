import Raw124Canonical58Membership
import Raw122SharpParent

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent43Raw122Canonical57Graft

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

/-- Use the exact parent table consumed by the accepted Raw122 parent Cover. -/
abbrev p122 : PartialMachine := BB6.Agent43Raw122.parent

/-- Raw122 occurs exactly once in the accepted Canonical64 source roster. -/
theorem p122_count64 :
    (BB6.Agent3Canonical64Raw120.roster64.filter
      (fun e => sameTable e.2 p122)).length = 1 := by decide

/-- Raw122 occurs exactly once in the actual, source-accepted Canonical57
    roster produced by the accepted Raw124 delta. -/
theorem p122_count57 :
    (BB6.Agent2Raw124Canonical58Membership.roster57.filter
      (fun e => sameTable e.2 p122)).length = 1 := by decide

theorem p122_root :
    p122 initialSlot = some (some ⟨true,true,1⟩) :=
  by decide

/-- Lift the accepted Raw122 parent Cover from 6,659,487 to the common
    Canonical57 reduction floor 6,766,859. -/
theorem p122_cover : Cover (WeightedBound 6766859) p122 := by
  apply Cover.leaf
  intro m hm
  intro k d hk hd
  exact Nat.le_trans
    (BB6.Agent43Raw122SharpParent.parent_bound m hm k d hk hd)
    (by decide : 6659487 ≤ 6766859)

theorem parents_root :
    ∀ p ∈ [p122], p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  simp only [List.mem_singleton] at hp
  subst p
  exact p122_root

theorem parents_cover :
    ∀ p ∈ [p122], Cover (WeightedBound 6766859) p := by
  intro p hp
  simp only [List.mem_singleton] at hp
  subst p
  exact p122_cover

/-- The exact 56-entry successor is obtained from the accepted Canonical57
    roster, not from a same-cardinality hand-reconstructed substitute. -/
noncomputable def roster56 :=
  removeParents [p122] BB6.Agent2Raw124Canonical58Membership.roster57

theorem count56 : roster56.length = 56 := by decide

theorem p122_count56 :
    (roster56.filter (fun e => sameTable e.2 p122)).length = 0 := by decide

theorem raw59_retained :
    (roster56.filter (fun e => sameTable e.2 BB6.Agent31Canonical59Membership.p59)).length = 1 := by decide

theorem raw113_absent :
    (roster56.filter (fun e => sameTable e.2 BB6.Agent31Canonical59Raw113Membership.p113)).length = 0 := by decide

theorem raw124_absent :
    (roster56.filter (fun e => sameTable e.2 BB6.Agent2Raw124Canonical58Membership.p124)).length = 0 := by decide

theorem sound_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster56, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := [p122])
    (roster := BB6.Agent2Raw124Canonical58Membership.roster57)
    BB6.Agent2Raw124Canonical58Membership.sound_integrated
    parents_root parents_cover

theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ roster56, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound_integrated hLeaves champ

theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster56,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_at_target (proposedTM63Moves + 7)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms p122_count64
#print axioms p122_count57
#print axioms p122_root
#print axioms p122_cover
#print axioms count56
#print axioms p122_count56
#print axioms raw59_retained
#print axioms raw113_absent
#print axioms raw124_absent
#print axioms sound_integrated
#print axioms exact_at_target
#print axioms exact_at_champion_score

end BB6.Agent43Raw122Canonical57Graft
