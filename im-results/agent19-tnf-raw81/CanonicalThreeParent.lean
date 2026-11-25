import CanonicalTwoParentGraft
import Raw71Data
import Raw77Data
import Raw81Data

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent19CanonicalThreeParent
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement

abbrev p71 := BB6.Agent10Raw71.p71
abbrev p77 := BB6.Agent10Raw77.p77
abbrev p81 := BB6.Agent10Raw81.p81
abbrev root := BB6.Agent50TNFPilot.root

def prune (r : List Entry) : List Entry :=
  graftRoster p81 [] (graftRoster p77 [] (graftRoster p71 [] r))

theorem prune_sound {r : List Entry}
    (hr : ∀ m, compatible root m → WeightedBound 7014 m ∨
      ∃ e ∈ r, TNFQuotientCompatible e.2 m) :
    ∀ m, compatible root m → WeightedBound 7014 m ∨
      ∃ e ∈ prune r, TNFQuotientCompatible e.2 m := by
  have h71 : ∀ m, compatible root m → WeightedBound 7014 m ∨
      ∃ e ∈ graftRoster p71 [] r, TNFQuotientCompatible e.2 m :=
    graftRoster_sound BB6.Agent10Raw71.p71_root hr (fun m hm => Or.inl (by
      intro k d hk hd
      exact Nat.le_trans (BB6.Agent10Raw71.all71 m hm k d hk hd) (by decide)))
  have h77 : ∀ m, compatible root m → WeightedBound 7014 m ∨
      ∃ e ∈ graftRoster p77 [] (graftRoster p71 [] r),
        TNFQuotientCompatible e.2 m :=
    graftRoster_sound BB6.Agent10Raw77.p77_root h71
      (fun m hm => Or.inl (BB6.Agent10Raw77.all77 m hm))
  exact graftRoster_sound BB6.Agent10Raw81.p81_root h77
    (fun m hm => Or.inl (BB6.Agent10Raw81.all81 m hm))

noncomputable def roster75 := prune BB6.Agent47Canonical78.roster
theorem count75 : roster75.length = 75 := by decide
theorem roster75_sound :
    ∀ m, compatible root m → WeightedBound 7014 m ∨
      ∃ e ∈ roster75, TNFQuotientCompatible e.2 m :=
  prune_sound BB6.Agent47Canonical78.roster_sound

theorem exact75_at_target (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ roster75, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB roster75_sound hLeaves champ

/-- Combine with the raw107/raw114 cut via explicit parent theorem inputs. -/
noncomputable def roster73 := prune BB6.Agent47CanonicalTwoParent.roster76
theorem count73 : roster73.length = 73 := by decide
theorem roster73_sound
    (h107 : ∀ m, compatible BB6.Agent47CanonicalTwoParent.p107 m →
      WeightedBound 815 m)
    (h114 : ∀ m, compatible BB6.Agent47CanonicalTwoParent.p114 m →
      WeightedBound 7014 m) :
    ∀ m, compatible root m → WeightedBound 7014 m ∨
      ∃ e ∈ roster73, TNFQuotientCompatible e.2 m :=
  prune_sound (BB6.Agent47CanonicalTwoParent.roster76_sound h107 h114)

theorem exact73_at_target (B : Nat) (hB : 7014 ≤ B)
    (h107 : ∀ m, compatible BB6.Agent47CanonicalTwoParent.p107 m →
      WeightedBound 815 m)
    (h114 : ∀ m, compatible BB6.Agent47CanonicalTwoParent.p114 m →
      WeightedBound 7014 m)
    (hLeaves : ∀ e ∈ roster73, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB
    (roster73_sound h107 h114) hLeaves champ

#print axioms prune_sound
#print axioms count75
#print axioms roster75_sound
#print axioms exact75_at_target
#print axioms count73
#print axioms roster73_sound
#print axioms exact73_at_target
end BB6.Agent19CanonicalThreeParent
