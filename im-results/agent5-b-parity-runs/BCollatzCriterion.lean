import BCollatzDiagonal

namespace BB6.BParityRuns

/-- Certified Machine B counter semantics reduces exactly to the sparse
    diagonal parity problem for the positive generalized 3x+7 map. -/
theorem counter_halts_iff_3x7 :
    BB6.BReduction.Halts (3,0,0) ↔
      ∃ n : Nat, (iterC (collatzA n) 8)%2=0 := by
  rw [OneDim.raw_criterion_local]
  constructor
  · rintro ⟨n,hn⟩
    refine ⟨n, ?_⟩
    rw [collatz_sample_bit n] at hn
    exact hn
  · rintro ⟨n,hn⟩
    refine ⟨n, ?_⟩
    rw [collatz_sample_bit n]
    exact hn

#print axioms counter_halts_iff_3x7
end BB6.BParityRuns
