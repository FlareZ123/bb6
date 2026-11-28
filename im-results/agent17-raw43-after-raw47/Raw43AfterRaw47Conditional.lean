import Raw47AfterRaw112Conditional
import Raw43Canonical40Membership

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Next exact roster edge after the Raw112 -> Raw47 lineage.

Raw43 is a retained Canonical40 representative.  This module checks directly
that it still occurs exactly once after removing Raw39, Raw112 and Raw47, and
forms the exact 37 -> 36 quotient.  Both Raw47 and Raw43 Covers remain explicit
premises here; this is a geometry/soundness interface for consuming a future
source-accepted Raw43 whole-parent proof without redoing the global lineage.
-/

namespace BB6.Agent17Raw43AfterRaw47Conditional

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

abbrev p47 : PartialMachine :=
  BB6.Agent9Raw47AfterRaw112Conditional.p47

abbrev p43 : PartialMachine :=
  BB6.Agent25Raw43Canonical40Membership.p

noncomputable abbrev baseRoster :=
  BB6.Agent9Raw47AfterRaw112Conditional.roster37

abbrev removedParents : List PartialMachine := [p43]

theorem p43_count37 :
    (baseRoster.filter (fun e => sameTable e.2 p43)).length = 1 := by
  decide

theorem p43_root :
    p43 initialSlot = some (some ⟨true, true, 1⟩) := by
  decide

theorem parents_root :
    ∀ p ∈ removedParents,
      p initialSlot = some (some ⟨true, true, 1⟩) := by
  intro p hp
  have he : p = p43 := by simpa [removedParents] using hp
  subst p
  exact p43_root

theorem parents_cover
    (h43 : Cover (WeightedBound 6766859) p43) :
    ∀ p ∈ removedParents, Cover (WeightedBound 6766859) p := by
  intro p hp
  have he : p = p43 := by simpa [removedParents] using hp
  subst p
  exact h43

noncomputable def roster36 := removeParents removedParents baseRoster

theorem count36 : roster36.length = 36 := by
  decide

theorem raw43_removed :
    (roster36.filter (fun e => sameTable e.2 p43)).length = 0 := by
  decide

theorem raw47_remains_removed :
    (roster36.filter (fun e => sameTable e.2 p47)).length = 0 := by
  decide

theorem conditional_sound
    (h47 : Cover (WeightedBound 6766859) p47)
    (h43 : Cover (WeightedBound 6766859) p43) :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster36, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := removedParents)
    (roster := baseRoster)
    (BB6.Agent9Raw47AfterRaw112Conditional.conditional_sound h47)
    parents_root (parents_cover h43)

theorem conditional_exact_at_champion
    (h47 : Cover (WeightedBound 6766859) p47)
    (h43 : Cover (WeightedBound 6766859) p43)
    (hLeaves : ∀ e ∈ roster36,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_from_quotient_roster (by omega)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    (conditional_sound h47 h43) hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms p43_count37
#print axioms p43_root
#print axioms count36
#print axioms raw43_removed
#print axioms raw47_remains_removed
#print axioms conditional_sound
#print axioms conditional_exact_at_champion

end BB6.Agent17Raw43AfterRaw47Conditional
