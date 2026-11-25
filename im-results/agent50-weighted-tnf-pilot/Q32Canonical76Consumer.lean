import CanonicalTwoParentGraft
import Q32SliceClosed
import Raw10BoxCore

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Q32Canonical76

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent50TNFPilot
open BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalTwoParent
open BB6.Agent44Q32Slice

/-- The literal q_i(2,32) parent: A0=1RB, B0=1RC, C0=0LA. -/
abbrev q32Parent : PartialMachine :=
  BB6Coverage.refine
    (BB6Coverage.refine BB6.Agent50TNFPilot.root
      (⟨1, by decide⟩, false)
      (some ⟨true, true, ⟨2, by decide⟩⟩))
    (⟨2, by decide⟩, false)
    (some ⟨false, false, ⟨0, by decide⟩⟩)

/-- The source-accepted twelve q32 slice cylinders are genuine descendants
    of the canonical parent, not merely unrelated safe tables. -/
def refinesb (child parent : PartialMachine) : Bool :=
  (List.finRange 6).all fun q =>
    [false, true].all fun b =>
      decide (parent (q,b) = none ∨ child (q,b) = parent (q,b))

abbrev q32Tables : List PartialMachine := BB6.Agent44Q32Slice.allTwelve

theorem q32Tables_refine_parent :
    ∀ p ∈ q32Tables, refinesb p q32Parent = true := by
  decide

/-- The parent is one exact member of the 76-residual two-parent roster. -/
theorem q32Parent_in_roster76 :
    ∃ e ∈ roster76, sameTable e.2 q32Parent = true := by
  decide

theorem q32Parent_exact_member :
    ∃ e ∈ roster76, e.2 = q32Parent := by
  obtain ⟨e, he, hs⟩ := q32Parent_in_roster76
  exact ⟨e, he, sameTable_sound hs⟩

noncomputable def parentEntries :=
  roster76.filter fun e => sameTable e.2 q32Parent

theorem parentEntries_count : parentEntries.length = 1 := by
  decide

/-- The 75 other canonical representatives remain explicit obligations. -/
noncomputable def otherRoster :=
  roster76.filter fun e => !(sameTable e.2 q32Parent)

theorem otherRoster_count : otherRoster.length = 75 := by
  decide

/-- Exact, disjoint box complement after removing the twelve safe q32
    cylinders from the full canonical parent. Each box is a real residual
    completion obligation; no uncovered transition assignment is discarded. -/
abbrev q32Remainder :=
  BB6.Agent49BoxBridge.remainder q32Parent q32Tables

theorem q32Remainder_exact (m : Machine) :
    (∃ r ∈ q32Remainder, BB6.Agent49Box.Fits r m) ↔
      compatible q32Parent m ∧
        ∀ p ∈ q32Tables, ¬ compatible p m :=
  BB6.Agent49BoxBridge.remainder_exact q32Parent q32Tables m

theorem q32Remainder_disjoint :
    q32Remainder.Pairwise BB6.Agent49Box.Disjoint :=
  BB6.Agent49BoxBridge.remainder_disjoint q32Parent q32Tables

/-- The twelve certified cylinders transfer from their local bound 144 to
    any larger target bound. -/
theorem q32Tables_safe_at (B : Nat) (h144 : 144 ≤ B) :
    ∀ p ∈ q32Tables, ∀ m, compatible p m → WeightedBound B m := by
  intro p hp m hm
  have h := BB6.Agent44Q32Slice.allTwelve_sound p hp m hm
  intro k d hk hd
  exact Nat.le_trans (h k d hk hd) h144

/-- A Cover for the canonical q32 parent is reduced exactly to the finite
    box complement. The twelve certified cylinders are consumed internally. -/
theorem q32_cover_from_remainder (B : Nat) (h144 : 144 ≤ B)
    (hOpen : ∀ r ∈ q32Remainder, ∀ m, BB6.Agent49Box.Fits r m →
      WeightedBound B m) :
    Cover (WeightedBound B) q32Parent :=
  BB6.Agent49BoxBridge.coverFromRemainder B q32Parent q32Tables
    (q32Tables_safe_at B h144) hOpen

/-- Conditional exactness consumer: one of the 76 canonical Covers is
    replaced by the twelve accepted q32 cylinders plus their exact box
    complement. The two existing parent certificates and other 75 Covers
    remain explicit premises, so this module does not import or duplicate
    their separate data-generation pipelines. -/
theorem exact_from_q32_remainder_at_target
    (B : Nat) (hB : 7014 ≤ B)
    (h107 : ∀ m, compatible BB6.Agent47CanonicalTwoParent.p107 m →
      WeightedBound 815 m)
    (h114 : ∀ m, compatible BB6.Agent47CanonicalTwoParent.p114 m →
      WeightedBound 7014 m)
    (hOpen : ∀ r ∈ q32Remainder, ∀ m, BB6.Agent49Box.Fits r m →
      WeightedBound B m)
    (hOther : ∀ e ∈ otherRoster, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B := by
  have h144 : 144 ≤ B := by omega
  apply BB6.Agent47CanonicalTwoParent.exact_at_target B hB h107 h114
  · intro e he
    by_cases hs : sameTable e.2 q32Parent = true
    · have heq : e.2 = q32Parent := sameTable_sound hs
      rw [heq]
      exact q32_cover_from_remainder B h144 hOpen
    · have hmem : e ∈ otherRoster :=
        List.mem_filter.mpr ⟨he, by simp [otherRoster, hs]⟩
      exact hOther e hmem
  · exact champ

#eval q32Remainder.length

#print axioms q32Tables_refine_parent
#print axioms q32Parent_in_roster76
#print axioms parentEntries_count
#print axioms otherRoster_count
#print axioms q32Remainder_exact
#print axioms q32Remainder_disjoint
#print axioms q32_cover_from_remainder
#print axioms exact_from_q32_remainder_at_champion_score

end BB6.Agent50Q32Canonical76
