import SheepPowerBridge

/-! Actual blank-origin counter state for the published Sheep machine: (0,2).
The next certified counter transition enters the one-variable t=5 section. -/
namespace BB6.Agent22.Sheep
open SheepBridge
open BB6.Agent22 (iter iter_add)

theorem counter_initial_iff_section_entry :
    (∃ n, iter nextA n (some ((0,2) : State)) = none) ↔
    (∃ n, iter nextA n (some (entry 5)) = none) := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [iter] at hn
    | succ n =>
      refine ⟨n, ?_⟩
      have h := iter_add nextA 1 n (some ((0,2) : State))
      have he : 1+n=n+1 := by omega
      rw [he] at h
      rw [h] at hn
      simpa [iter, nextA, entry] using hn
  · rintro ⟨n,hn⟩
    refine ⟨n+1, ?_⟩
    have h := iter_add nextA 1 n (some ((0,2) : State))
    have he : 1+n=n+1 := by omega
    rw [he] at h
    rw [h]
    simpa [iter, nextA, entry] using hn

/-- The independently restated Sheep counter machine, from the *real*
blank-origin accelerated state (0,2), halts iff the forward return orbit
from t=5 enters a power of two. This is all-time and fully quantified. -/
theorem counter_blank_halts_iff_power :
    (∃ n, iter nextA n (some ((0,2) : State)) = none) ↔
    (∃ a, 2 ≤ a ∧ Reach 5 (2^a)) := by
  exact counter_initial_iff_section_entry.trans
    (counter_halts_iff_reaches_power 5 (by omega))

#print axioms BB6.Agent22.Sheep.counter_blank_halts_iff_power
end BB6.Agent22.Sheep
