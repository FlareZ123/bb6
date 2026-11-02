import Lean
import BRunValuation

namespace BB6.CryptidBRun

theorem step_if_two_mod_three (n : Nat) (h : n%3=2) : ∃ m, BStep n m := by
  obtain ⟨k, hk⟩ : ∃ k, n=3*k+2 := ⟨n/3, by omega⟩
  refine ⟨8*k+9, ?_⟩
  dsimp [BStep]
  omega

theorem run_snoc {j n z m : Nat} (h : BRun j n z)
    (hz : BStep z m) : BRun (j+1) n m := by
  induction h with
  | zero n => exact BRun.succ hz (BRun.zero m)
  | succ hs tail ih => exact BRun.succ hs (ih hz)

theorem eventually_non_B (n : Nat) :
    ∃ j z, BRun j n z ∧ z%3 ≠ 2 := by
  classical
  apply Classical.byContradiction
  intro no
  have notall : ∀ j z, BRun j n z → z % 3 = 2 := by
    intro j z hz
    by_cases hh : z % 3 = 2
    · exact hh
    · exact False.elim (no ⟨j,z,hz,hh⟩)
  have all : ∀ j, ∃ z, BRun j n z := by
    intro j
    induction j with
    | zero => exact ⟨n,BRun.zero n⟩
    | succ j ih =>
      obtain ⟨z,hz⟩ := ih
      have hmod := notall j z hz
      obtain ⟨m,hm⟩ := step_if_two_mod_three z hmod
      exact ⟨m,run_snoc hz hm⟩
  obtain ⟨z,hz⟩ := all (5*n+11)
  exact no_long_B_run n z hz

theorem step_nondecreasing {n m : Nat} (h : BStep n m) : n ≤ m := by
  dsimp [BStep] at h
  omega

theorem run_nondecreasing {j n z : Nat} (h : BRun j n z) : n ≤ z := by
  induction h with
  | zero n => omega
  | succ h rest ih => exact Nat.le_trans (step_nondecreasing h) ih

#print axioms eventually_non_B
#print axioms run_nondecreasing
end BB6.CryptidBRun
