import Q32SliceClosed
import Raw10BoxCore

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Q32Canonical76

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent50TNFPilot
open BB6.Agent44Q32Slice

/-- The literal q_i(2,32) parent: A0=1RB, B0=1RC, C0=0LA. -/
abbrev q32Parent : PartialMachine :=
  BB6Coverage.refine
    (BB6Coverage.refine BB6.Agent50TNFPilot.root
      (⟨1, by decide⟩, false)
      (some ⟨true, true, ⟨2, by decide⟩⟩))
    (⟨2, by decide⟩, false)
    (some ⟨false, false, ⟨0, by decide⟩⟩)

/-- The twelve source-derived q32 slice cylinders are genuine descendants
    of the canonical parent, not merely unrelated safe tables. -/
def refinesb (child parent : PartialMachine) : Bool :=
  (List.finRange 6).all fun q =>
    [false, true].all fun b =>
      decide (parent (q,b) = none ∨ child (q,b) = parent (q,b))

abbrev q32Tables : List PartialMachine := BB6.Agent44Q32Slice.allTwelve

theorem q32Tables_count : q32Tables.length = 12 := by
  decide

theorem q32Tables_refine_parent :
    ∀ p ∈ q32Tables, refinesb p q32Parent = true := by
  decide

/-- Exact, disjoint box complement after removing the twelve safe q32
    cylinders from the full parent. Each box is a real residual completion
    obligation; no uncovered transition assignment is discarded. -/
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

/-- Generic roster adapter: if a canonical residual roster contains this
    parent, its single parent Cover can be replaced by the twelve accepted
    q32 cylinders plus the exact remainder-box obligations. Every other
    roster entry is preserved unchanged. Instantiate R with roster76 in the
    separate canonical two-parent closure, where its membership proof lives. -/
theorem roster_cover_from_q32_remainder
    (R : List (List Move × PartialMachine))
    (B : Nat) (h144 : 144 ≤ B)
    (hOpen : ∀ r ∈ q32Remainder, ∀ m, BB6.Agent49Box.Fits r m →
      WeightedBound B m)
    (hOther : ∀ e ∈ R, e.2 ≠ q32Parent →
      Cover (WeightedBound B) e.2) :
    ∀ e ∈ R, Cover (WeightedBound B) e.2 := by
  intro e he
  by_cases hs : e.2 = q32Parent
  · rw [hs]
    exact q32_cover_from_remainder B h144 hOpen
  · exact hOther e he hs

#eval q32Remainder.length

#print axioms q32Tables_count
#print axioms q32Tables_refine_parent
#print axioms q32Remainder_exact
#print axioms q32Remainder_disjoint
#print axioms q32_cover_from_remainder
#print axioms roster_cover_from_q32_remainder

end BB6.Agent50Q32Canonical76
