import Agent18OneDimBridge
import BCollatzDiagonal

namespace BB6.BParityRuns
open BusyBeaver

/-- Raw blank-start six-state Machine B halts iff the self-indexed positive
    3x+7 map reaches an even element at one of its recursively chosen times. -/
theorem raw_halts_iff_3x7 :
    IsHalt BB6.Bridge.Source.target ↔
      ∃ n : Nat, (iterC (collatzA n) 8)%2=0 := by
  rw [BB6.Bridge.raw_halts_iff_two_branch]
  constructor
  · rintro ⟨n,hn⟩
    refine ⟨n, ?_⟩
    rw [collatz_sample_bit n] at hn
    exact hn
  · rintro ⟨n,hn⟩
    refine ⟨n, ?_⟩
    rw [collatz_sample_bit n]
    exact hn

#print axioms raw_halts_iff_3x7
end BB6.BParityRuns
