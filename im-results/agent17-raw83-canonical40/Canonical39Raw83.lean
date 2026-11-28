import Canonical40Extra57
import A10Raw83Exact

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Consume the independently source-accepted Raw83 four-hole parent directly
from the accepted Raw57 Canonical40 quotient.  This module proves the exact
sameTable membership, removes only that parent, and preserves the conditional
exact-BB(6) interface for the 39 retained representatives.
-/

namespace BB6.Agent17Canonical39Raw83

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

noncomputable abbrev baseRoster := BB6.Agent31Canonical40Extra57.roster40
abbrev p83 : PartialMachine := BB6.Agent10Raw83.parent
abbrev removedParents : List PartialMachine := [p83]

theorem parent_count40 :
    (baseRoster.filter (fun e => sameTable e.2 p83)).length = 1 := by
  decide

theorem parent_root :
    p83 initialSlot = some (some ⟨true,true,1⟩) := by
  decide

theorem source_cover :
    Cover (WeightedBound 6766859) p83 := by
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent10Raw83.all_completions m hm k d hk hd)
    (by decide)

theorem parents_root :
    ∀ p ∈ removedParents,
      p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  have he : p = p83 := by simpa [removedParents] using hp
  subst p
  exact parent_root

theorem parents_cover :
    ∀ p ∈ removedParents, Cover (WeightedBound 6766859) p := by
  intro p hp
  have he : p = p83 := by simpa [removedParents] using hp
  subst p
  exact source_cover

noncomputable def roster39 := removeParents removedParents baseRoster

theorem count39 : roster39.length = 39 := by
  decide

theorem removed_parent_absent :
    (roster39.filter (fun e => sameTable e.2 p83)).length = 0 := by
  decide

theorem sound_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster39, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := removedParents)
    (roster := baseRoster)
    BB6.Agent31Canonical40Extra57.sound_integrated
    parents_root parents_cover

theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ roster39, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound_integrated hLeaves champ

theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster39,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_at_target (proposedTM63Moves + 7)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms parent_count40
#print axioms parent_root
#print axioms source_cover
#print axioms count39
#print axioms removed_parent_absent
#print axioms sound_integrated
#print axioms exact_at_target
#print axioms exact_at_champion_score

end BB6.Agent17Canonical39Raw83
