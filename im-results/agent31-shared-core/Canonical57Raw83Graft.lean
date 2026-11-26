import Canonical58Raw113Graft
import Canonical58Raw83Membership
import A10Raw83Exact

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31Canonical57Raw83Graft

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent31StableParentBatch
open BB6.Agent31Canonical58Raw113Graft
open BB6.Agent31Canonical58Raw83Membership
open BB6.Agent10Raw83
open BB6ChampionArithmetic

abbrev baseRoster := BB6.Agent31Canonical58Raw113Graft.roster58
noncomputable def roster57 := removeParents [p83] baseRoster

abbrev p83Source : PartialMachine := BB6.Agent10Raw83.parent

theorem p83_source_eq : p83 = p83Source :=
  sameTable_sound (by decide)

/-- Lift Raw83's exact 514 bound to the common champion-score floor. -/
theorem p83_cover : Cover (WeightedBound 6766859) p83 := by
  rw [p83_source_eq]
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent10Raw83.all_completions m hm k d hk hd) (by decide)

theorem count57 : roster57.length = 57 := by decide

theorem raw59_retained :
    (roster57.filter (fun e => sameTable e.2 p59)).length = 1 := by decide

theorem parents_pairwise_distinct :
    List.Pairwise (fun p q => sameTable p q = false) [p83] := by decide

theorem parents_root :
    ∀ p ∈ [p83], p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  simp only [List.mem_singleton] at hp
  subst p
  exact BB6.Agent31Canonical58Raw83Membership.p83_root

theorem parents_cover :
    ∀ p ∈ [p83], Cover (WeightedBound 6766859) p := by
  intro p hp
  simp only [List.mem_singleton] at hp
  subst p
  exact p83_cover

theorem sound_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster57, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := [p83]) (roster := baseRoster)
    BB6.Agent31Canonical58Raw113Graft.sound_integrated
    parents_root parents_cover

theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ roster57, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound_integrated hLeaves champ

theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster57,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_at_target (proposedTM63Moves + 7)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms p83_source_eq
#print axioms p83_cover
#print axioms count57
#print axioms raw59_retained
#print axioms parents_pairwise_distinct
#print axioms parents_root
#print axioms parents_cover
#print axioms sound_integrated
#print axioms exact_at_target
#print axioms exact_at_champion_score

end BB6.Agent31Canonical57Raw83Graft
