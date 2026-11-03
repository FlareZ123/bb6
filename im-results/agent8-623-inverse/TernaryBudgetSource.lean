import BusyBeaver.BB6.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

/-!
  Sharp third-counter growth for original Cryptids #623 B-drain.
  Source pinned: c86f15861709b76042998c5211c7b2f83991621b.
  Conditional success theorem applies to any input; the infinite exact
  family saturates it. These statements do not decide blank-origin halting.
-/

namespace BB6.Agent8BudgetSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

/-- The evaluator's third-plus-three-times-residual budget. -/
theorem evalA_ternary_budget (a : Nat) :
    ∀ k m aa bb dd : Nat, evalA a k m = some (aa,bb,dd) →
      m + k ≤ dd + 3*bb + 2 := by
  induction a with
  | zero =>
    intro k m aa bb dd h
    rw [evalA] at h
    by_cases h2 : k%3=2
    · simp [h2] at h
      cases h
      omega
    · by_cases h0 : k%3=0
      · simp [h2,h0] at h
      · simp [h2,h0] at h
        cases h
        omega
  | succ a ih =>
    intro k m aa bb dd h
    rw [evalA] at h
    by_cases h2 : k%3=2
    · simp [h2] at h
      cases h
      omega
    · by_cases h0 : k%3=0
      · simp [h2,h0] at h
        cases h
        omega
      · simp [h2,h0] at h
        have hr := ih (k/3) (m+2*(k/3)+3) aa bb dd h
        omega

/-- Every successful B-drain raises its third counter by at least 3b. -/
theorem drainB_d3 (b : Nat) :
    ∀ a d aa dd : Nat, drainB a b d = some (.D aa dd) → d + 3*b ≤ dd := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro a d aa dd h
    rw [drainB] at h
    by_cases hb : b=0
    · simp [hb] at h
      cases h
      omega
    · simp only [if_neg hb] at h
      cases he : evalA a (b-1) (d+2*b+3) with
      | none => simp [he] at h
      | some p =>
        rcases p with ⟨a1,b1,d1⟩
        simp only [he,Option.bind_some] at h
        by_cases hlt : b1 < b
        · simp only [if_pos hlt] at h
          have hp := evalA_ternary_budget a (b-1) (d+2*b+3) a1 b1 d1 he
          have hr := ih b1 hlt a1 d1 aa dd h
          omega
        · simp [hlt] at h

/-- Infinite geometrically growing indices realizing equality in drainB_d3. -/
def tightB : Nat → Nat
  | 0 => 0
  | n+1 => 3*tightB n+3

theorem tightB_pow (n : Nat) : 2*tightB n+3=3^(n+1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [tightB,Nat.pow_succ]
    omega

/-- An all-parameter exact orbit family, not merely sampled trajectories. -/
theorem drainB_tight (n : Nat) : ∀ a d : Nat, tightB n + 1 ≤ a →
    drainB a (tightB n) d = some (.D (a+n) (d+3*tightB n)) := by
  induction n with
  | zero =>
    intro a d h
    simp [tightB,drainB]
  | succ n ih =>
    intro a d h
    have hdef : tightB (n+1) = 3*tightB n+3 := rfl
    rw [hdef] at h
    change drainB a (3*tightB n+3) d =
      some (.D (a+(n+1)) (d+3*(3*tightB n+3)))
    rw [drainB]
    simp only [if_neg (by omega : 3*tightB n+3≠0)]
    have hk : (3*tightB n+3)-1 = 3*tightB n+2 := by omega
    rw [hk]
    have hev : evalA a (3*tightB n+2) (d+2*(3*tightB n+3)+3) =
        some (a+1,tightB n,d+2*(3*tightB n+3)+3) := by
      rw [evalA]
      simp only [if_pos (by omega : (3*tightB n+2)%3=2)]
      have hdiv : (3*tightB n+2)/3 = tightB n := by omega
      simp [hdiv]
    rw [hev]
    simp only [Option.bind_some,if_pos (by omega : tightB n<3*tightB n+3)]
    rw [ih (a+1) (d+2*(3*tightB n+3)+3) (by omega)]
    simp only [Option.some.injEq, HighLevelState.D.injEq]
    constructor <;> omega

#print axioms evalA_ternary_budget
#print axioms drainB_d3
#print axioms tightB_pow
#print axioms drainB_tight
end BB6.Agent8BudgetSource
