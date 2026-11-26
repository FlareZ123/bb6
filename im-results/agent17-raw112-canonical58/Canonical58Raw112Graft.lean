import CanonicalSelectedParentIntegrated
import Canonical59Raw112Membership

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent17Canonical58Raw112Graft

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6.Agent31Canonical59Membership
open BB6.Agent17Canonical59Raw112Membership
open BB6ChampionArithmetic

noncomputable def roster58 :=
  removeParents [p112] BB6.Agent32CanonicalSelectedIntegrated.rosterSelected

theorem p112_count59 :
    (BB6.Agent32CanonicalSelectedIntegrated.rosterSelected.filter
      (fun e => sameTable e.2 p112)).length = 1 :=
  p112_count59

theorem count58 : roster58.length = 58 := by decide

/-- Raw59 remains in the quotient complement; no Raw59 cut is inferred. -/
theorem raw59_retained :
    (roster58.filter (fun e => sameTable e.2 p59)).length = 1 := by decide

theorem parents_pairwise_distinct :
    List.Pairwise (fun p q => sameTable p q = false) [p112] := by decide

theorem parents_root :
    ∀ p ∈ [p112], p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  simp only [List.mem_singleton] at hp
  subst p
  exact p112_root

theorem parents_cover :
    ∀ p ∈ [p112], Cover (WeightedBound 6766859) p := by
  intro p hp
  simp only [List.mem_singleton] at hp
  subst p
  exact p112_cover

theorem sound_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster58, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := [p112])
    (roster := BB6.Agent32CanonicalSelectedIntegrated.rosterSelected)
    BB6.Agent32CanonicalSelectedIntegrated.sound_integrated
    parents_root parents_cover

theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ roster58, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound_integrated hLeaves champ

theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster58,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_at_target (proposedTM63Moves + 7)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms p112_count59
#print axioms count58
#print axioms raw59_retained
#print axioms parents_pairwise_distinct
#print axioms parents_root
#print axioms parents_cover
#print axioms sound_integrated
#print axioms exact_at_target
#print axioms exact_at_champion_score

end BB6.Agent17Canonical58Raw112Graft
