import CanonicalRaw114Accepted
import CanonicalRosterRefinement

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47Canonical76Raw58

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent8TNFPath
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement

/-- The third E1 sibling at the canonical first-hole address: E1 = 0RA.
    This is the exact table definition used by Agent4's Raw58 parent. -/
abbrev p58 : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨false,true,0⟩)

/-- The Raw58 sibling remains a representative after the accepted p107/p114
    cuts defining the canonical 77-roster. -/
theorem parent_present :
    ∃ e ∈ BB6.Agent47CanonicalRaw114Accepted.roster,
      sameTable e.2 p58 = true := by
  decide

/-- Empty-replacement graft of the Raw58 sibling removes exactly one entry. -/
noncomputable def roster :=
  graftRoster p58 [] BB6.Agent47CanonicalRaw114Accepted.roster

theorem count : roster.length = 76 := by
  decide

/-- If the five-child Raw58 parent proof closes at 7014, it composes with the
    accepted canonical77 dichotomy to leave 76 quotient representatives. -/
theorem sound
    (h58 : ∀ m, compatible p58 m → WeightedBound 7014 m) :
    ∀ m, compatible root m →
      WeightedBound 7014 m ∨
        ∃ e ∈ roster, TNFQuotientCompatible e.2 m :=
  graftRoster_sound (by decide)
    BB6.Agent47CanonicalRaw114Accepted.sound
    (fun m hm => Or.inl (h58 m hm))

/-- Conditional exactness after the Raw58 graft. The 76 retained Covers and
    the attaining blank-start witness remain explicit. -/
theorem exact_at_target (B : Nat) (hB : 7014 ≤ B)
    (h58 : ∀ m, compatible p58 m → WeightedBound 7014 m)
    (hLeaves : ∀ e ∈ roster, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB (sound h58) hLeaves champ

#print axioms parent_present
#print axioms count
#print axioms sound
#print axioms exact_at_target

end BB6.Agent47Canonical76Raw58
