import CanonicalRaw114Accepted
import Raw125ResidualClosure

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent13CanonicalRaw125
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31FourHoleRoster

abbrev p125 := BB6.Agent13Raw125.p125
noncomputable def roster := graftRoster p125 [] BB6.Agent47CanonicalRaw114Accepted.roster

theorem parent_present : ∃ e ∈ BB6.Agent47CanonicalRaw114Accepted.roster,
    sameTable e.2 p125 = true := by
  have h : BB6.Agent47CanonicalRaw114Accepted.roster.any
      (fun e => sameTable e.2 p125) = true := by decide
  exact List.any_eq_true.mp h

theorem count : roster.length = 76 := by decide

theorem sound : ∀ m, compatible root m → WeightedBound 7014 m ∨
    ∃ e ∈ roster, TNFQuotientCompatible e.2 m :=
  graftRoster_sound BB6.Agent13Raw125.p125_root BB6.Agent47CanonicalRaw114Accepted.sound
    (fun m hm => Or.inl ((BB6.Agent13Raw125.raw125_cover 7014 (by decide)).sound m hm))

theorem exact_at_target (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ roster, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound hLeaves champ

#print axioms parent_present
#print axioms count
#print axioms sound
#print axioms exact_at_target
end BB6.Agent13CanonicalRaw125
