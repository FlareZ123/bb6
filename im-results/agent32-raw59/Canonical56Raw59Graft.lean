import Canonical57Raw112Graft
import CanonicalSelectedRaw59

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent32Canonical56Raw59Graft

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6.Agent31Canonical59Membership
open BB6.Agent31Canonical59Raw113Membership
open BB6.Agent17Canonical59Raw112Membership
open BB6.Agent32CanonicalSelectedRaw59
open BB6ChampionArithmetic

/-- The accepted Canonical57 roster already includes the Raw113 and Raw112 cuts. -/
abbrev baseRoster := BB6.Agent17Canonical57Raw112Graft.roster57

/-- Remove Raw59 only after the Raw112-after-Raw113 base and Raw59 Cover are both accepted. -/
noncomputable def roster56 := removeParents [p59] baseRoster

theorem p59_count57 :
    (baseRoster.filter (fun e => sameTable e.2 p59)).length = 1 :=
  BB6.Agent17Canonical57Raw112Graft.raw59_retained

theorem p59_count56 :
    (roster56.filter (fun e => sameTable e.2 p59)).length = 0 := by decide

theorem count56 : roster56.length = 56 := by decide

/-- Both earlier sequential cuts remain absent after removing Raw59. -/
theorem raw113_removed :
    (roster56.filter
      (fun e => sameTable e.2 BB6.Agent31Canonical59Raw113Membership.p113)).length = 0 := by
  decide

theorem raw112_removed :
    (roster56.filter
      (fun e => sameTable e.2 BB6.Agent17Canonical59Raw112Membership.p112)).length = 0 := by
  decide

theorem parents_pairwise_distinct :
    List.Pairwise (fun p q => sameTable p q = false) [p59] := by decide

theorem parents_root :
    ∀ p ∈ [p59], p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  simp only [List.mem_singleton] at hp
  subst p
  decide

theorem parents_cover :
    ∀ p ∈ [p59], Cover (WeightedBound 6766859) p := by
  intro p hp
  simp only [List.mem_singleton] at hp
  subst p
  exact BB6.Agent32CanonicalSelectedRaw59.p59_cover

theorem sound_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster56, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := [p59]) (roster := baseRoster)
    BB6.Agent17Canonical57Raw112Graft.sound_integrated parents_root parents_cover

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
#print axioms raw112_removed
#print axioms parents_pairwise_distinct
#print axioms parents_root
#print axioms parents_cover
#print axioms sound_integrated
#print axioms exact_at_target
#print axioms exact_at_champion_score

end BB6.Agent32Canonical56Raw59Graft
