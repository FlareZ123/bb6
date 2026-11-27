import Raw124Canonical58Membership
import Raw59KernelSlice

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent2Canonical56Raw59AfterRaw124

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6.Agent31Canonical59Membership
open BB6.Agent31Canonical59Raw113Membership
open BB6ChampionArithmetic

/-- Start from the source-accepted Canonical57 roster obtained by removing
    Raw124 from the actual accepted Canonical58 roster. -/
noncomputable abbrev baseRoster := BB6.Agent2Raw124Canonical58Membership.roster57

/-- Remove Raw59 from Canonical57-Raw124 to obtain a 56-entry successor. -/
noncomputable def roster56 := removeParents [p59] baseRoster

theorem p59_count57 :
    (baseRoster.filter (fun e => sameTable e.2 p59)).length = 1 := by decide

theorem p59_count56 :
    (roster56.filter (fun e => sameTable e.2 p59)).length = 0 := by decide

theorem count56 : roster56.length = 56 := by decide

/-- Raw113 and Raw124 remain absent after the independent Raw59 cut. -/
theorem raw113_removed :
    (roster56.filter
      (fun e => sameTable e.2 BB6.Agent31Canonical59Raw113Membership.p113)).length = 0 := by
  decide

theorem raw124_removed :
    (roster56.filter
      (fun e => sameTable e.2 BB6.Agent2Raw124Canonical58Membership.p124)).length = 0 := by
  decide

theorem parents_pairwise_distinct :
    List.Pairwise (fun p q => sameTable p q = false) [p59] := by decide

theorem parents_root :
    ∀ p ∈ [p59], p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  simp only [List.mem_singleton] at hp
  subst p
  decide

/-- Recheck the source parent literal in this roster's own environment.
    The old producer's CanonicalSelectedRaw59 wrapper is unnecessary. -/
theorem p59_source_eq :
    p59 = A32Raw59Slice.BB6.Agent32Raw59.p59 :=
  sameTable_sound (by decide)

theorem p59_cover : Cover (WeightedBound 6766859) p59 := by
  rw [p59_source_eq]
  exact liftCover (by decide) A32Raw59Slice.BB6.Agent32Raw59Exact.cover

theorem parents_cover :
    ∀ p ∈ [p59], Cover (WeightedBound 6766859) p := by
  intro p hp
  simp only [List.mem_singleton] at hp
  subst p
  exact p59_cover

theorem sound_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster56, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := [p59]) (roster := baseRoster)
    BB6.Agent2Raw124Canonical58Membership.sound_integrated parents_root parents_cover

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

#print axioms p59_count57
#print axioms p59_count56
#print axioms count56
#print axioms raw113_removed
#print axioms raw124_removed
#print axioms parents_pairwise_distinct
#print axioms parents_root
#print axioms p59_source_eq
#print axioms p59_cover
#print axioms parents_cover
#print axioms sound_integrated
#print axioms exact_at_target
#print axioms exact_at_champion_score

end BB6.Agent2Canonical56Raw59AfterRaw124
