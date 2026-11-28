import Raw112Canonical38OfficialMembership

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent9Raw112Canonical38OfficialConditional

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

abbrev p112 : PartialMachine :=
  BB6.Agent9Raw112Canonical38OfficialMembership.p112
noncomputable abbrev baseRoster :=
  BB6.Agent9Canonical38Raw39ThenRaw47.roster38
abbrev removedParents : List PartialMachine := [p112]

theorem parent_count38 :
    (baseRoster.filter (fun e => sameTable e.2 p112)).length = 1 :=
  BB6.Agent9Raw112Canonical38OfficialMembership.parent_count38

theorem parent_root :
    p112 initialSlot = some (some ⟨true,true,1⟩) :=
  BB6.Agent9Raw112Canonical38OfficialMembership.parent_root

theorem parents_root :
    ∀ p ∈ removedParents,
      p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  have he : p = p112 := by simpa [removedParents] using hp
  subst p
  exact parent_root

theorem parents_cover
    (h : Cover (WeightedBound (proposedTM63Moves + 7)) p112) :
    ∀ p ∈ removedParents,
      Cover (WeightedBound (proposedTM63Moves + 7)) p := by
  intro p hp
  have he : p = p112 := by simpa [removedParents] using hp
  subst p
  exact h

noncomputable def roster37 := removeParents removedParents baseRoster

theorem count37 : roster37.length = 37 := by
  decide

theorem removed_parent_absent :
    (roster37.filter (fun e => sameTable e.2 p112)).length = 0 := by
  decide

theorem conditional_sound
    (hp : Cover (WeightedBound (proposedTM63Moves + 7)) p112) :
    ∀ m, compatible root m →
      WeightedBound (proposedTM63Moves + 7) m ∨
        ∃ e ∈ roster37, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := removedParents)
    (roster := baseRoster)
    BB6.Agent9Canonical38Raw39ThenRaw47.sound38
    parents_root (parents_cover hp)

theorem conditional_exact_at_champion
    (hp : Cover (WeightedBound (proposedTM63Moves + 7)) p112)
    (hLeaves : ∀ e ∈ roster37,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_from_quotient_roster (by omega)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    (conditional_sound hp) hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms parent_count38
#print axioms count37
#print axioms removed_parent_absent
#print axioms conditional_sound
#print axioms conditional_exact_at_champion

end BB6.Agent9Raw112Canonical38OfficialConditional
