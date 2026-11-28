import Raw39Canonical39Successor
import Raw43Canonical39Membership

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Conditional cumulative successor: from the source-accepted Raw39 Canonical39
lineage, remove Raw43 once its parent Cover is supplied.  No Raw43 Cover is
assumed as an axiom; it is an explicit theorem premise.
-/

namespace BB6.Agent25Raw43Canonical39Conditional

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

abbrev p43 : PartialMachine := BB6.Agent25Raw43Canonical39Membership.p
noncomputable abbrev baseRoster :=
  BB6.Agent11Raw39Canonical39Successor.roster39
abbrev removedParents : List PartialMachine := [p43]

theorem parent_count39 :
    (baseRoster.filter (fun e => sameTable e.2 p43)).length = 1 :=
  BB6.Agent25Raw43Canonical39Membership.parent_present

theorem parent_root :
    p43 initialSlot = some (some ⟨true,true,1⟩) := by decide

theorem parents_pairwise_distinct :
    List.Pairwise (fun p q => sameTable p q = false) removedParents := by decide

theorem parents_root :
    ∀ p ∈ removedParents,
      p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  have he : p = p43 := by simpa [removedParents] using hp
  subst p
  exact parent_root

theorem parents_cover (h : Cover (WeightedBound 6766859) p43) :
    ∀ p ∈ removedParents, Cover (WeightedBound 6766859) p := by
  intro p hp
  have he : p = p43 := by simpa [removedParents] using hp
  subst p
  exact h

noncomputable def roster38 := removeParents removedParents baseRoster

theorem count38 : roster38.length = 38 := by decide

theorem removed_parent_absent :
    (roster38.filter (fun e => sameTable e.2 p43)).length = 0 := by decide

theorem conditional_sound (hp : Cover (WeightedBound 6766859) p43) :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster38, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := removedParents)
    (roster := baseRoster)
    BB6.Agent11Raw39Canonical39Successor.sound_integrated
    parents_root (parents_cover hp)

theorem conditional_exact_at_champion
    (hp : Cover (WeightedBound 6766859) p43)
    (hLeaves : ∀ e ∈ roster38,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_from_quotient_roster (by omega)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    (conditional_sound hp) hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms parent_count39
#print axioms count38
#print axioms removed_parent_absent
#print axioms conditional_sound
#print axioms conditional_exact_at_champion

end BB6.Agent25Raw43Canonical39Conditional
