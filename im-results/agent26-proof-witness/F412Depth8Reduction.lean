import F412NGramReduction
import F412DeepHaltFour

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent26F412Depth8
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent26F412Graft
open BB6.Agent26F412NGram BB6.Agent26F412DeepHalt

/-- All four remaining last-hole stage alternatives. Each reaches its
    unique E1 hole in at most 30 primitive moves and hence has a bounded
    halt completion; every ordinary completion has no halt instruction. -/
def fDepth8Halt : List (Fin 9 × Move) := [
  (⟨8, by decide⟩, ⟨false,true,4⟩),
  (⟨8, by decide⟩, ⟨true,false,3⟩),
  (⟨8, by decide⟩, ⟨true,false,4⟩),
  (⟨8, by decide⟩, ⟨true,true,4⟩)
]

theorem fDepth8Halt_in_remaining63 :
    ∀ e ∈ fDepth8Halt, e ∈ fRemaining63 := by decide

theorem fDepth8Halt_weighted (B : Nat) (hB : 37 ≤ B)
    (e : Fin 9 × Move) (he : e ∈ fDepth8Halt) (m : Machine)
    (hm : compatible (fChild e.1 e.2) m) : WeightedBound B m := by
  have cases :
      e = (⟨8, by decide⟩, ⟨false,true,4⟩) ∨
      e = (⟨8, by decide⟩, ⟨true,false,3⟩) ∨
      e = (⟨8, by decide⟩, ⟨true,false,4⟩) ∨
      e = (⟨8, by decide⟩, ⟨true,true,4⟩) := by
    simpa [fDepth8Halt] using he
  rcases cases with h | h | h | h
  · subst e
    exact B1_0RE_sound B hB m (by simpa [pB1] using hm)
  · subst e
    exact B1_1LD_sound B hB m (by simpa [pB1] using hm)
  · subst e
    exact B1_1LE_sound B hB m (by simpa [pB1] using hm)
  · subst e
    exact B1_1RE_sound B hB m (by simpa [pB1] using hm)

/-- The complete residual F412 parent complement after all 67 branch
    certificates: 59 side cycles, four local-window invariants, four
    short last-hole leaves. -/
def fRemaining140 : List (Fin 9 × Move) :=
  fRemaining63.filter (fun e => !(decide (e ∈ fDepth8Halt)))

theorem fRemaining140_length : fRemaining140.length = 140 := by decide

/-- Every depth-eight sibling has been formally accounted for. -/
theorem fRemaining140_no_depth8 :
    ∀ e ∈ fRemaining140, e.1.val ≠ 8 := by decide

def FDisposition140 (B : Nat) (m : Machine) : Prop :=
  WeightedBound B m ∨
  ∃ e ∈ fRemaining140, compatible (fChild e.1 e.2) m

/-- Conditional refinement: eight new disjoint source-checkable cylinder
    certificates consume actual obligations, not only a descriptive union. -/
theorem fResidualSound140 (B : Nat) (hB : fMoves+1 ≤ B)
    (hclock : HaltsAfter fLiteral fMoves) :
    ∀ m, compatible fResidual m → FDisposition140 B m := by
  have h37 : 37 ≤ B := by
    unfold fMoves at hB
    omega
  intro m hm
  rcases fResidualSound63 B hB hclock m hm with hBound | ⟨e,he,hc⟩
  · exact Or.inl hBound
  · by_cases hn : e ∈ fDepth8Halt
    · exact Or.inl (fDepth8Halt_weighted B h37 e hn m hc)
    · refine Or.inr ⟨e, ?_, hc⟩
      simp [fRemaining140, he, hn]

#print axioms fRemaining140_length
#print axioms fRemaining140_no_depth8
#print axioms fDepth8Halt_weighted
#print axioms fResidualSound140

end BB6.Agent26F412Depth8
