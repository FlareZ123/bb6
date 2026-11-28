import F412Depth7Reduction
import F412Depth6A10RC
import F412Depth6A10RF

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent26F412Depth6Two
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent26F412Graft
open BB6.Agent26F412Depth7 BB6.Agent26F412ThreeHole

/-- Two additional depth-six A1 nonchampion alternatives, each covered by
    a complete finite descendant certificate tree. -/
def fDepth6Two : List (Fin 9 × Move) := [
  (⟨6, by decide⟩, ⟨false,true,2⟩),
  (⟨6, by decide⟩, ⟨false,true,5⟩)
]

theorem fDepth6Two_length : fDepth6Two.length = 2 := by decide
theorem fDepth6Two_in_remaining127 :
    ∀ e ∈ fDepth6Two, e ∈ fRemaining127 := by decide

theorem fDepth6Two_sound (B : Nat) (hB : 128 ≤ B)
    (e : Fin 9 × Move) (he : e ∈ fDepth6Two)
    (m : Machine) (hm : compatible (fChild e.1 e.2) m) :
    WeightedBound B m := by
  have cases :
    e = (⟨6, by decide⟩, ⟨false,true,2⟩) ∨
    e = (⟨6, by decide⟩, ⟨false,true,5⟩) := by
    simpa [fDepth6Two] using he
  rcases cases with h | h
  · subst e
    exact BB6.Agent26F412Depth6.A10RC.parent_sound B hB m
      (by simpa [BB6.Agent26F412Depth6.A10RC.am, pA1] using hm)
  · subst e
    exact BB6.Agent26F412Depth6.A10RF.parent_sound B hB m
      (by simpa [BB6.Agent26F412Depth6.A10RF.am, pA1] using hm)

/-- Actual finer complement after two complete level-six subtrees. -/
def fRemaining125 : List (Fin 9 × Move) :=
  fRemaining127.filter (fun e => !(decide (e ∈ fDepth6Two)))

theorem fRemaining125_length : fRemaining125.length = 125 := by decide
theorem fRemaining125_no_depth7_or8 :
    ∀ e ∈ fRemaining125, e.1.val ≠ 7 ∧ e.1.val ≠ 8 := by decide
theorem fRemaining125_no_two_depth6 :
    ∀ e ∈ fRemaining125,
      e ≠ (⟨6, by decide⟩, ⟨false,true,2⟩) ∧
      e ≠ (⟨6, by decide⟩, ⟨false,true,5⟩) := by decide

def FDisposition125 (B : Nat) (m : Machine) : Prop :=
  WeightedBound B m ∨
  ∃ e ∈ fRemaining125, compatible (fChild e.1 e.2) m

theorem fResidualSound125 (B : Nat) (hB : fMoves+1 ≤ B)
    (hclock : HaltsAfter fLiteral fMoves) :
    ∀ m, compatible fResidual m → FDisposition125 B m := by
  have h128 : 128 ≤ B := by unfold fMoves at hB; omega
  intro m hm
  rcases fResidualSound127 B hB hclock m hm with hb | ⟨e,he,hc⟩
  · exact Or.inl hb
  · by_cases hnew : e ∈ fDepth6Two
    · exact Or.inl (fDepth6Two_sound B h128 e hnew m hc)
    · refine Or.inr ⟨e, ?_, hc⟩
      simp [fRemaining125, he, hnew]

#print axioms fDepth6Two_sound
#print axioms fRemaining125_length
#print axioms fResidualSound125
end BB6.Agent26F412Depth6Two
