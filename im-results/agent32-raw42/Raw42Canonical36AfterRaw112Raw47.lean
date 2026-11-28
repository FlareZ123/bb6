import Raw47Canonical37AfterRaw112
import Raw42Canonical40Membership

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Conditional next edge after the accepted Raw112-first Canonical38 lineage and
its Raw47 successor.  Raw47 is supplied by the source-accepted
Raw47Canonical37AfterRaw112 module.  This theorem removes Raw42 from that
exact 37-member roster, conditional only on the still-open Raw42 parent Cover.
The named-child wrapper below converts its twelve exact child Covers into that
parent premise.
-/

namespace BB6.Agent17Raw42AfterRaw112Raw47

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

abbrev p42 : PartialMachine := BB6.Agent17Raw42Canonical40Membership.p
noncomputable abbrev baseRoster :=
  BB6.Agent29Raw47AfterRaw112.roster37
abbrev removedParents : List PartialMachine := [p42]

theorem parent_count37 :
    (baseRoster.filter (fun e => sameTable e.2 p42)).length = 1 := by
  decide

theorem parent_root :
    p42 initialSlot = some (some ⟨true,true,1⟩) := by
  decide

theorem parents_root :
    ∀ p ∈ removedParents,
      p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  have he : p = p42 := by simpa [removedParents] using hp
  subst p
  exact parent_root

theorem parents_cover
    (hp : Cover (WeightedBound 6766859) p42) :
    ∀ p ∈ removedParents, Cover (WeightedBound 6766859) p := by
  intro p hp'
  have he : p = p42 := by simpa [removedParents] using hp'
  subst p
  exact hp

noncomputable def roster36 := removeParents removedParents baseRoster

theorem count36 : roster36.length = 36 := by
  decide

theorem removed_parent_absent :
    (roster36.filter (fun e => sameTable e.2 p42)).length = 0 := by
  decide

theorem conditional_sound
    (hp : Cover (WeightedBound 6766859) p42) :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster36, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := removedParents)
    (roster := baseRoster)
    BB6.Agent29Raw47AfterRaw112.sound_integrated
    parents_root (parents_cover hp)

theorem conditional_exact_at_champion
    (hp : Cover (WeightedBound 6766859) p42)
    (hLeaves : ∀ e ∈ roster36,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_from_quotient_roster (by omega)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    (conditional_sound hp) hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms parent_count37
#print axioms parent_root
#print axioms count36
#print axioms removed_parent_absent
#print axioms conditional_sound
#print axioms conditional_exact_at_champion

end BB6.Agent17Raw42AfterRaw112Raw47
