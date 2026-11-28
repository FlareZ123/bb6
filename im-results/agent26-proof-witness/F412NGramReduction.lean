import F412NGramFour

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent26F412NGram
open BB6Coverage BB6.Agent26F412Graft

/-- Four previously unclassified long-running first-hole siblings, each
covered for *every* completion by a source-checkable N-gram invariant.
These entries are deliberately excluded from the 59 original side cycles. -/
def fNewNGram : List (Fin 9 × Move) := [
  (⟨6, by decide⟩, ⟨false,true,1⟩),
  (⟨8, by decide⟩, ⟨false,false,0⟩),
  (⟨8, by decide⟩, ⟨false,false,2⟩),
  (⟨8, by decide⟩, ⟨false,true,1⟩)
]

/-- Actual complement after 59 displacement cycles and four finite-window
invariants, not a mere union of certificates. -/
def fRemaining63 : List (Fin 9 × Move) :=
  fRemaining.filter (fun e => !(decide (e ∈ fNewNGram)))

theorem fNewNGram_distinct : fNewNGram.Nodup := by decide
theorem fNewNGram_in_remaining : ∀ e ∈ fNewNGram, e ∈ fRemaining := by decide
theorem fRemaining63_length : fRemaining63.length = 144 := by decide

theorem fNewNGram_weighted (B : Nat) (e : Fin 9 × Move)
    (he : e ∈ fNewNGram) (m : Machine)
    (hm : compatible (fChild e.1 e.2) m) : WeightedBound B m := by
  have cases :
      e = (⟨6, by decide⟩, ⟨false,true,1⟩) ∨
      e = (⟨8, by decide⟩, ⟨false,false,0⟩) ∨
      e = (⟨8, by decide⟩, ⟨false,false,2⟩) ∨
      e = (⟨8, by decide⟩, ⟨false,true,1⟩) := by
    simpa [fNewNGram] using he
  rcases cases with h | h | h | h
  · subst e
    exact weighted_never B m (never0 m (by simpa [p0] using hm))
  · subst e
    exact weighted_never B m (never1 m (by simpa [p1] using hm))
  · subst e
    exact weighted_never B m (never2 m (by simpa [p2] using hm))
  · subst e
    exact weighted_never B m (never3 m (by simpa [p3] using hm))

def FDisposition63 (B : Nat) (m : Machine) : Prop :=
  WeightedBound B m ∨
  ∃ e ∈ fRemaining63, compatible (fChild e.1 e.2) m

/-- Conditional parent completion now leaves 144 (formerly 148) explicit
first-hole siblings. The four reductions themselves do NOT depend on the
pending long F412 clock. -/
theorem fResidualSound63 (B : Nat) (hB : fMoves+1 ≤ B)
    (hclock : HaltsAfter fLiteral fMoves) :
    ∀ m, compatible fResidual m → FDisposition63 B m := by
  intro m hm
  rcases fResidualSound B hB hclock m hm with hBound | ⟨e,he,hc⟩
  · exact Or.inl hBound
  · by_cases hn : e ∈ fNewNGram
    · exact Or.inl (fNewNGram_weighted B e hn m hc)
    · refine Or.inr ⟨e, ?_, hc⟩
      simp [fRemaining63, he, hn]

#print axioms fRemaining63_length
#print axioms fNewNGram_weighted
#print axioms fResidualSound63

end BB6.Agent26F412NGram
