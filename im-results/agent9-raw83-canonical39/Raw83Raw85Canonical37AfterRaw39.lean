import Raw39Canonical39Successor
import A10Raw83Exact
import Raw85Bound

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Candidate combined whole-parent consumption of the independently accepted
Raw83 (514) and Raw85 (7014) four-hole cylinders from the exact accepted
Raw39 Canonical39 lineage. Their complete Covers are imported as original
Lean proof objects; counting this 39 -> 37 cut requires a new source-check
and authenticated linking, not a subtraction of separate conditional counts.
-/

namespace BB6.Agent9Raw83Raw85Canonical37AfterRaw39

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

noncomputable abbrev baseRoster :=
  BB6.Agent11Raw39Canonical39Successor.roster39
abbrev p83 : PartialMachine := BB6.Agent10Raw83.parent
abbrev p85 : PartialMachine := BB6.Agent21Raw85.parent
abbrev removedParents : List PartialMachine := [p83, p85]

theorem p83_count39 :
    (baseRoster.filter (fun e => sameTable e.2 p83)).length = 1 := by decide

theorem p85_count39 :
    (baseRoster.filter (fun e => sameTable e.2 p85)).length = 1 := by decide

theorem p83_p85_distinct : sameTable p83 p85 = false := by decide

theorem p83_root :
    p83 initialSlot = some (some ⟨true,true,1⟩) :=
  BB6.Agent10Raw83.parent_root

theorem p85_root :
    p85 initialSlot = some (some ⟨true,true,1⟩) :=
  BB6.Agent21Raw85.parent_root

theorem p83_cover : Cover (WeightedBound 6766859) p83 := by
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent10Raw83.all_completions m hm k d hk hd)
    (by decide : 514 ≤ 6766859)

theorem p85_cover : Cover (WeightedBound 6766859) p85 := by
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent21Raw85.all_completions m hm k d hk hd)
    (by decide : 7014 ≤ 6766859)

theorem parents_root :
    ∀ p ∈ removedParents,
      p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  simp only [removedParents, List.mem_cons, List.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact p83_root
  · exact p85_root

theorem parents_cover :
    ∀ p ∈ removedParents,
      Cover (WeightedBound 6766859) p := by
  intro p hp
  simp only [removedParents, List.mem_cons, List.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact p83_cover
  · exact p85_cover

noncomputable def roster37 := removeParents removedParents baseRoster

theorem count37 : roster37.length = 37 := by
  decide

theorem raw83_removed :
    (roster37.filter (fun e => sameTable e.2 p83)).length = 0 := by
  decide

theorem raw85_removed :
    (roster37.filter (fun e => sameTable e.2 p85)).length = 0 := by
  decide

theorem sound_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster37, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := removedParents)
    (roster := baseRoster)
    BB6.Agent11Raw39Canonical39Successor.sound_integrated
    parents_root parents_cover

theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster37,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_from_quotient_roster (by omega)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    sound_integrated hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms p83_count39
#print axioms p85_count39
#print axioms p83_p85_distinct
#print axioms p83_cover
#print axioms p85_cover
#print axioms count37
#print axioms raw83_removed
#print axioms raw85_removed
#print axioms sound_integrated
#print axioms exact_at_champion_score

end BB6.Agent9Raw83Raw85Canonical37AfterRaw39
