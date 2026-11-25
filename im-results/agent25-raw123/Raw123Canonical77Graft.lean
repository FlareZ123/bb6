import CanonicalRaw114Accepted
import A25Raw123Data

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent25Raw123Canonical77
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement

noncomputable def roster76 := graftRoster BB6.Agent25Raw123.p123 []
  BB6.Agent47CanonicalRaw114Accepted.roster

theorem parent_present :
    ∃ e ∈ BB6.Agent47CanonicalRaw114Accepted.roster,
      sameTable e.2 BB6.Agent25Raw123.p123 = true := by decide

theorem roster76_count : roster76.length = 76 := by decide

theorem roster76_sound : ∀ m, compatible root m →
    WeightedBound 9109 m ∨ ∃ e ∈ roster76, TNFQuotientCompatible e.2 m := by
  apply graftRoster_sound BB6.Agent25Raw123.p123_root
  · intro m hm
    rcases BB6.Agent47CanonicalRaw114Accepted.sound m hm with hb | hr
    · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    · exact Or.inr hr
  · intro m hm
    exact Or.inl (BB6.Agent25Raw123.all123 m hm)

theorem exact_at_target (B : Nat) (hB : 9109 ≤ B)
    (hLeaves : ∀ e ∈ roster76, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB roster76_sound hLeaves champ

#print axioms parent_present
#print axioms roster76_count
#print axioms roster76_sound
#print axioms exact_at_target
end BB6.Agent25Raw123Canonical77
