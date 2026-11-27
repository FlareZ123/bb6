import Raw124Canonical58Membership
import FourSharpCover

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent2Canonical53FourSharp

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

noncomputable abbrev baseRoster := BB6.Agent2Raw124Canonical58Membership.roster57
abbrev sharpParents := BB6.Agent32FourSharp.parents

theorem unique_membership :
    ∀ p ∈ sharpParents,
      (baseRoster.filter (fun e => sameTable e.2 p)).length = 1 := by
  intro p hp
  simp only [sharpParents, BB6.Agent32FourSharp.parents, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> decide

theorem pairwise_distinct :
    List.Pairwise (fun p q => sameTable p q = false) sharpParents := by decide

theorem parents_root :
    ∀ p ∈ sharpParents,
      p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  simp only [sharpParents, BB6.Agent32FourSharp.parents, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> decide

theorem parents_cover :
    ∀ p ∈ sharpParents, Cover (WeightedBound 6766859) p :=
  BB6.Agent32FourSharp.parent_covers 6766859 (by decide)

noncomputable def roster53 :=
  removeParents sharpParents baseRoster

theorem count53 : roster53.length = 53 := by decide

theorem all_removed :
    ∀ p ∈ sharpParents,
      (roster53.filter (fun e => sameTable e.2 p)).length = 0 := by
  intro p hp
  simp only [sharpParents, BB6.Agent32FourSharp.parents, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> decide

theorem raw59_retained :
    (roster53.filter (fun e => sameTable e.2
      BB6.Agent31Canonical59Membership.p59)).length = 1 := by decide

theorem sound_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster53, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := sharpParents) (roster := baseRoster)
    BB6.Agent2Raw124Canonical58Membership.sound_integrated
    parents_root parents_cover

theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ roster53, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound_integrated hLeaves champ

theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster53,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_at_target (proposedTM63Moves + 7)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    hLeaves BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms unique_membership
#print axioms pairwise_distinct
#print axioms parents_root
#print axioms parents_cover
#print axioms count53
#print axioms all_removed
#print axioms raw59_retained
#print axioms sound_integrated
#print axioms exact_at_target
#print axioms exact_at_champion_score
end BB6.Agent2Canonical53FourSharp
