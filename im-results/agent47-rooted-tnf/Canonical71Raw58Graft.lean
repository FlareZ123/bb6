import Canonical72Raw121Graft
import CanonicalRosterRefinement

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47Canonical71Raw58

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent8TNFPath
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement

/-- Exact Raw58 E1=0RA sibling of the canonical first-hole expansion. -/
abbrev p58 : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨false,true,0⟩)

/-- The Raw58 sibling remains in the 72-roster after raw107/raw114/raw117/
    raw112/raw110/raw121 parent cuts. -/
theorem parent_present :
    ∃ e ∈ BB6.Agent38Canonical72Raw121.roster,
      sameTable e.2 p58 = true := by
  decide

/-- Graft the Raw58 parent into the 72-roster. -/
noncomputable def roster :=
  graftRoster p58 [] BB6.Agent38Canonical72Raw121.roster

/-- If the finite membership check succeeds, Raw58 removes exactly one
    additional quotient representative. -/
theorem count : roster.length = 71 := by
  decide

/-- A source-accepted Raw58 parent Cover at 7014 composes with the existing
    72-roster dichotomy, whose common target is 6,766,859. -/
theorem sound
    (h58 : ∀ m, compatible p58 m → WeightedBound 7014 m) :
    ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster, TNFQuotientCompatible e.2 m := by
  apply graftRoster_sound
    (p := p58)
    (replacement := [])
    (roster := BB6.Agent38Canonical72Raw121.roster)
    (by decide)
  · intro m hm
    rcases BB6.Agent38Canonical72Raw121.sound m hm with hb | hres
    · exact Or.inl (by
        intro k d hk hd
        exact Nat.le_trans (hb k d hk hd) (by decide))
    · exact Or.inr hres
  · intro m hm
    exact Or.inl (by
      intro k d hk hd
      exact Nat.le_trans (h58 m hm k d hk hd) (by decide))

/-- Conditional exactness after the Raw58 graft: all 71 retained Covers and
    the attaining blank-start witness remain explicit premises. -/
theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
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

end BB6.Agent47Canonical71Raw58
