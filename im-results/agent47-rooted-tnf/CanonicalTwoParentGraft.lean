import Canonical78Roster
import CanonicalRosterRefinement
import ZipPrefixAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47CanonicalTwoParent
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent8TNFPath
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement

/-- Both parents are the actual five-move residuals of the canonical roster. -/
abbrev p107 : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨false,true,1⟩)
abbrev p114 : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨false,false,3⟩)

noncomputable def roster107 := graftRoster p107 [] BB6.Agent47Canonical78.roster
noncomputable def roster76 := graftRoster p114 [] roster107

theorem count107 : roster107.length = 77 := by decide
theorem count76 : roster76.length = 76 := by decide

theorem roster107_sound
    (h107 : ∀ m, compatible p107 m → WeightedBound 815 m) :
    ∀ m, compatible root m → WeightedBound 7014 m ∨
      ∃ e ∈ roster107, TNFQuotientCompatible e.2 m :=
  graftRoster_sound (by decide) BB6.Agent47Canonical78.roster_sound
    (fun m hm => Or.inl (by
      intro k d hk hd
      exact Nat.le_trans (h107 m hm k d hk hd) (by decide)))

theorem roster76_sound
    (h107 : ∀ m, compatible p107 m → WeightedBound 815 m)
    (h114 : ∀ m, compatible p114 m → WeightedBound 7014 m) :
    ∀ m, compatible root m → WeightedBound 7014 m ∨
      ∃ e ∈ roster76, TNFQuotientCompatible e.2 m :=
  graftRoster_sound (by decide) (roster107_sound h107)
    (fun m hm => Or.inl (h114 m hm))

theorem exact_at_target (B : Nat) (hB : 7014 ≤ B)
    (h107 : ∀ m, compatible p107 m → WeightedBound 815 m)
    (h114 : ∀ m, compatible p114 m → WeightedBound 7014 m)
    (hLeaves : ∀ e ∈ roster76, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB (roster76_sound h107 h114) hLeaves champ

#print axioms count107
#print axioms count76
#print axioms roster107_sound
#print axioms roster76_sound
#print axioms exact_at_target
end BB6.Agent47CanonicalTwoParent
