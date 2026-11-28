import Canonical40Extra57
import Raw54Canonical40Membership

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Conditional source-level Canonical40→39 quotient for Raw54.
No Raw54 parent Cover is assumed to exist here; the Cover remains explicit.
-/

namespace BB6.Agent8Raw54Canonical40Conditional
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

abbrev p54 : PartialMachine := BB6.Agent8Raw54Canonical40Membership.p
noncomputable abbrev baseRoster := BB6.Agent31Canonical40Extra57.roster40
abbrev removedParents : List PartialMachine := [p54]

theorem parent_count40 :
    (baseRoster.filter (fun e => sameTable e.2 p54)).length = 1 :=
  BB6.Agent8Raw54Canonical40Membership.parent_present

theorem parents_pairwise_distinct :
    List.Pairwise (fun p q => sameTable p q = false) removedParents := by decide

theorem parents_root :
    ∀ p ∈ removedParents,
      p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  have he : p = p54 := by simpa [removedParents] using hp
  subst p
  exact BB6.Agent8Raw54Canonical40Membership.parent_root

theorem parents_cover (h : Cover (WeightedBound 6766859) p54) :
    ∀ p ∈ removedParents, Cover (WeightedBound 6766859) p := by
  intro p hp
  have he : p = p54 := by simpa [removedParents] using hp
  subst p
  exact h

noncomputable def roster39 := removeParents removedParents baseRoster

theorem count39 : roster39.length = 39 := by decide

theorem removed_parent_absent :
    (roster39.filter (fun e => sameTable e.2 p54)).length = 0 := by decide

theorem conditional_sound (hp : Cover (WeightedBound 6766859) p54) :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster39, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := removedParents)
    (roster := baseRoster)
    BB6.Agent31Canonical40Extra57.sound_integrated
    parents_root (parents_cover hp)

theorem conditional_exact_at_champion
    (hp : Cover (WeightedBound 6766859) p54)
    (hLeaves : ∀ e ∈ roster39,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_from_quotient_roster (by omega)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    (conditional_sound hp) hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms parent_count40
#print axioms parents_pairwise_distinct
#print axioms parents_root
#print axioms count39
#print axioms removed_parent_absent
#print axioms conditional_sound
#print axioms conditional_exact_at_champion
end BB6.Agent8Raw54Canonical40Conditional
