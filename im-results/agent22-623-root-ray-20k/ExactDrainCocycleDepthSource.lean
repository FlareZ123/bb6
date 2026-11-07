import Agent22ExactDrainCocycleSource

/-!
# Depth bound for the exact #623 B-drain cocycle

Every successful evaluator output has second counter at most one third of
its input index. Consequently, the exact weighted B-drain residual r is
bounded by the ternary digit budget n whenever b < 3^n.
-/

namespace BB6.Agent22ExactDrainCocycleDepthSource

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent22ExactDrainCocycleSource

/-- The second output counter of evalA is at most floor(k/3). -/
theorem evalA_second_le_quotient (a : Nat) :
    ∀ k m aa bb dd : Nat,
      evalA a k m = some (aa, bb, dd) →
      bb ≤ k / 3 := by
  induction a with
  | zero =>
      intro k m aa bb dd heval
      rw [evalA] at heval
      by_cases hk2 : k % 3 = 2
      · simp [hk2] at heval
        cases heval
        omega
      · by_cases hk0 : k % 3 = 0
        · simp [hk2, hk0] at heval
        · simp [hk2, hk0] at heval
          cases heval
          omega
  | succ a ih =>
      intro k m aa bb dd heval
      rw [evalA] at heval
      by_cases hk2 : k % 3 = 2
      · simp [hk2] at heval
        cases heval
        omega
      · by_cases hk0 : k % 3 = 0
        · simp [hk2, hk0] at heval
          cases heval
          omega
        · simp [hk2, hk0] at heval
          have hi := ih (k / 3) (m + 2*(k / 3) + 3) aa bb dd heval
          omega

/-- The exact B-drain potential residual r is at most n whenever b<3^n.
    The source ternary budget is retained explicitly. -/
theorem drainB_weighted_depth (n : Nat) :
    ∀ a b d aa dd : Nat, b ≤ ternaryOnes a → b < 3^n →
      drainB a b d = some (.D aa dd) →
      ∃ r : Nat, r ≤ n ∧
        2*aa + dd = 2*a + d + 3*b + 2*r := by
  induction n with
  | zero =>
      intro a b d aa dd hbudget hpow h
      have hb0 : b = 0 := by omega
      subst b
      rw [drainB] at h
      simp at h
      cases h
      exact ⟨0, by omega, by omega⟩
  | succ n ih =>
      intro a b d aa dd hbudget hpow h
      by_cases hb0 : b = 0
      · subst b
        rw [drainB] at h
        simp at h
        cases h
        exact ⟨0, by omega, by omega⟩
      · have hstrict : b - 1 < ternaryOnes a := by omega
        rw [drainB] at h
        simp only [if_neg hb0] at h
        obtain ⟨a1, b1, d1, he, hp⟩ :=
          evalA_ones_budget a (b - 1) (d + 2*b + 3) hstrict
        have hq := evalA_second_le_quotient a (b - 1)
          (d + 2*b + 3) a1 b1 d1 he
        have hdec : b1 < b := by omega
        have hpowSub : b - 1 < 3^(n+1) := by omega
        have hdiv : (b - 1) / 3 < 3^n := by
          apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).2
          simpa [Nat.pow_succ, Nat.mul_comm] using hpowSub
        have hpow1 : b1 < 3^n := by omega
        simp only [he, Option.bind_some, if_pos hdec] at h
        obtain ⟨r, hr, hrEq⟩ := ih a1 b1 d1 aa dd hp hpow1 h
        have hweighted := evalA_weighted_exact a (b - 1)
          (d + 2*b + 3) a1 b1 d1 hstrict he
        refine ⟨r + 1, ?_, ?_⟩ <;> omega

#print axioms evalA_second_le_quotient
#print axioms drainB_weighted_depth

end BB6.Agent22ExactDrainCocycleDepthSource
