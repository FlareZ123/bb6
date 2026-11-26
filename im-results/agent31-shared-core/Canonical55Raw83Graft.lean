import Canonical56Raw83Membership
import Canonical56Raw59Graft

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31Canonical55Raw83Graft

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent31StableParentBatch
open BB6.Agent31Canonical59Membership
open BB6.Agent17Canonical59Raw112Membership
open BB6.Agent31Canonical59Raw113Membership
open BB6.Agent32Canonical56Raw59Graft
open BB6.Agent31Canonical56Raw83Membership
open BB6ChampionArithmetic

abbrev baseRoster := BB6.Agent32Canonical56Raw59Graft.roster56

/-- Remove the source-accepted Raw83 parent from the exact Canonical56 complement. -/
noncomputable def roster55 := removeParents [p83] baseRoster

theorem p83_count56 :
    (baseRoster.filter (fun e => sameTable e.2 p83)).length = 1 :=
  BB6.Agent31Canonical56Raw83Membership.p83_count56

theorem p83_removed :
    (roster55.filter (fun e => sameTable e.2 p83)).length = 0 := by
  decide

theorem count55 : roster55.length = 55 := by
  decide

/-- The three previously consumed parent cylinders remain absent. -/
theorem raw59_removed :
    (roster55.filter
      (fun e => sameTable e.2 BB6.Agent31Canonical59Membership.p59)).length = 0 := by
  decide

theorem raw112_removed :
    (roster55.filter
      (fun e => sameTable e.2 BB6.Agent17Canonical59Raw112Membership.p112)).length = 0 := by
  decide

theorem raw113_removed :
    (roster55.filter
      (fun e => sameTable e.2 BB6.Agent31Canonical59Raw113Membership.p113)).length = 0 := by
  decide

theorem parents_pairwise_distinct :
    List.Pairwise (fun p q => sameTable p q = false) [p83] := by
  decide

theorem parents_root :
    ∀ p ∈ [p83], p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  simp only [List.mem_singleton] at hp
  subst p
  exact BB6.Agent31Canonical56Raw83Membership.p83_root

theorem parents_cover :
    ∀ p ∈ [p83], Cover (WeightedBound 6766859) p := by
  intro p hp
  simp only [List.mem_singleton] at hp
  subst p
  exact BB6.Agent31Canonical56Raw83Membership.p83_cover

theorem sound_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster55, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := [p83]) (roster := baseRoster)
    BB6.Agent32Canonical56Raw59Graft.sound_integrated
    parents_root parents_cover

theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ roster55, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound_integrated hLeaves champ

theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster55,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_at_target (proposedTM63Moves + 7)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms p83_count56
#print axioms p83_removed
#print axioms count55
#print axioms raw59_removed
#print axioms raw112_removed
#print axioms raw113_removed
#print axioms parents_pairwise_distinct
#print axioms parents_root
#print axioms parents_cover
#print axioms sound_integrated
#print axioms exact_at_target
#print axioms exact_at_champion_score

end BB6.Agent31Canonical55Raw83Graft
