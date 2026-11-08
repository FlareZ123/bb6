import RootShift
import Lean.Elab.Tactic.Omega

namespace BB6Coverage

@[simp] theorem shiftConfig_zero_lasso (c : Config) : shiftConfig 0 c = c := by
  cases c with
  | mk s h tape => simp [shiftConfig]

theorem translated_cycle_iter (m : Machine) (c : Config) (period : Nat)
    (offset : Int) (hcycle : run m period c = some (shiftConfig offset c))
    (k : Nat) :
    run m (period*k) c = some (shiftConfig (offset * (k : Int)) c) := by
  induction k with
  | zero =>
    simpa [run, shiftConfig]
  | succ k ih =>
    calc
      run m (period*(k+1)) c = (run m (period*k) c).bind (run m period) := by
        rw [Nat.mul_succ, run_append]
      _ = some (shiftConfig (offset * ((k+1 : Nat) : Int)) c) := by
        rw [ih]
        simp only [Option.bind_some, shift_run, hcycle, Option.map_some, shift_shift]
        congr 1
        congr 1
        simp [Int.natCast_succ, Int.mul_add, Int.add_comm]

theorem translated_cycle_live (m : Machine) (c : Config) (period : Nat)
    (hperiod : 0 < period) (offset : Int)
    (hcycle : run m period c = some (shiftConfig offset c)) :
    ∀ n : Nat, (run m n c).isSome = true := by
  intro n
  have hle : n ≤ period * (n+1) := by
    have hstep : n+1 ≤ period*(n+1) := by
      simpa using Nat.mul_le_mul_right (n+1) hperiod
    omega
  have hfar := translated_cycle_iter m c period offset hcycle (n+1)
  cases h : run m n c with
  | some x => rfl
  | none =>
    have heq : period*(n+1) = n + (period*(n+1)-n) := by omega
    have hnone : run m (period*(n+1)) c = none := by
      rw [heq, run_append, h]
      rfl
    rw [hnone] at hfar
    contradiction

theorem translated_prefix_never (m : Machine) (c : Config) (entry period : Nat)
    (hp : 0 < period) (offset : Int)
    (hentry : run m entry blank = some c)
    (hcycle : run m period c = some (shiftConfig offset c)) :
    NeverHalts m := by
  intro n
  by_cases hn : n ≤ entry
  · cases h : run m n blank with
    | some x => rfl
    | none =>
      have heq : entry = n + (entry-n) := by omega
      have hx : run m entry blank = none := by
        rw [heq, run_append, h]
        rfl
      rw [hx] at hentry
      contradiction
  · have hge : entry ≤ n := by omega
    have heq : n = entry + (n-entry) := by omega
    rw [heq, run_append, hentry]
    exact translated_cycle_live m c period hp offset hcycle (n-entry)

#print axioms translated_cycle_iter
#print axioms translated_cycle_live
#print axioms translated_prefix_never
end BB6Coverage
