import Agent49ParitySource

/-!
Six-per-block exact upper gain for the source #623 ternary drain. The evaluator
has three sharp parameter regimes: universal, k>0, and k>=2. The third-counter
gain of a completed B-drain is <=6b for every b>=2; b=1 is the exceptional
sharp gain 7. The original Cryptids definitions are imported unchanged.
-/

namespace BB6.Agent8SixBudgetSource

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

theorem evalA_six_budget (a : Nat) :
    ∀k m aa bb dd, evalA a k m = some (aa,bb,dd) →
      dd+6*bb ≤ m+4*k+2 := by
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

theorem evalA_six_budget_pos (a k m aa bb dd : Nat)
    (hk : 0<k)
    (h : evalA a k m = some (aa,bb,dd)) :
    dd+6*bb ≤ m+4*k+1 := by
  rw [evalA] at h
  by_cases h2 : k%3=2
  · simp [h2] at h
    cases h
    omega
  · by_cases ha : a=0
    · simp [h2,ha] at h
      by_cases h0 : k%3=0
      · simp [h0] at h
      · simp [h0] at h
        cases h
        omega
    · simp only [if_neg h2, if_neg ha] at h
      by_cases h0 : k%3=0
      · simp [h0] at h
        cases h
        omega
      · simp only [if_neg h0] at h
        have hr := evalA_six_budget (a-1) (k/3) (m+2*(k/3)+3) aa bb dd h
        omega

theorem evalA_six_budget_ge2 (a k m aa bb dd : Nat)
    (hk : 2≤k)
    (h : evalA a k m = some (aa,bb,dd)) :
    dd+6*bb ≤ m+4*k := by
  rw [evalA] at h
  by_cases h2 : k%3=2
  · simp [h2] at h
    cases h
    omega
  · by_cases ha : a=0
    · simp [h2,ha] at h
      by_cases h0 : k%3=0
      · simp [h0] at h
      · simp [h0] at h
        cases h
        omega
    · simp only [if_neg h2, if_neg ha] at h
      by_cases h0 : k%3=0
      · simp [h0] at h
        cases h
        omega
      · simp only [if_neg h0] at h
        have hr := evalA_six_budget (a-1) (k/3) (m+2*(k/3)+3) aa bb dd h
        omega

theorem evalA_bb_three_le (a : Nat) :
    ∀ k m aa bb dd, evalA a k m = some (aa,bb,dd) →
      3*bb ≤ k := by
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

/-- Exact indexed upper gain: b=0 preserves d, b=1 gains at most 7,
and b>=2 gains at most 6b. All bounds concern full successful drains. -/
theorem drainB_six (b : Nat) :
    ∀ a d aa dd, drainB a b d = some (.D aa dd) →
      (b=0 → dd=d) ∧
      (b=1 → dd≤d+7) ∧
      (2≤b → dd≤d+6*b) := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
      intro a d aa dd h
      rw [drainB] at h
      by_cases hb : b=0
      · simp [hb] at h
        cases h
        constructor <;> omega
      · simp only [if_neg hb] at h
        cases hev : evalA a (b-1) (d+2*b+3) with
        | none => simp [hev] at h
        | some p =>
            rcases p with ⟨a1,b1,d1⟩
            simp only [hev,Option.bind_some] at h
            by_cases hlt : b1<b
            · simp only [if_pos hlt] at h
              have hrec := ih b1 hlt a1 d1 aa dd h
              have hbb := evalA_bb_three_le a (b-1) (d+2*b+3) a1 b1 d1 hev
              by_cases hb1 : b1=0
              · have hrec0 : dd=d1 := hrec.1 hb1
                have hupper0 := evalA_six_budget a (b-1) (d+2*b+3) a1 b1 d1 hev
                constructor
                · intro hh
                  omega
                constructor
                · intro hh
                  omega
                · intro hh
                  have hupper1 := evalA_six_budget_pos a (b-1)
                    (d+2*b+3) a1 b1 d1 (by omega) hev
                  omega
              · have hrec1 : dd ≤ d1+6*b1+1 := by
                  by_cases hone : b1=1
                  · have hr := hrec.2.1 hone
                    omega
                  · have hr := hrec.2.2 (by omega)
                    omega
                have hpositive := evalA_six_budget_ge2 a (b-1)
                  (d+2*b+3) a1 b1 d1 (by omega) hev
                constructor
                · intro hh
                  omega
                constructor
                · intro hh
                  omega
                · intro hh
                  omega
            · simp [hlt] at h

/-- A handy unconditional form of the indexed upper gain. -/
theorem drainB_six_plus_one (a b d aa dd : Nat)
    (h : drainB a b d = some (.D aa dd)) :
    dd≤d+6*b+1 := by
  have h6 := drainB_six b a d aa dd h
  by_cases h0 : b=0
  · have heq := h6.1 h0
    omega
  · by_cases h1 : b=1
    · have hu := h6.2.1 h1
      omega
    · have hu := h6.2.2 (by omega)
      omega

#print axioms evalA_six_budget
#print axioms evalA_six_budget_pos
#print axioms evalA_six_budget_ge2
#print axioms evalA_bb_three_le
#print axioms drainB_six
#print axioms drainB_six_plus_one

end BB6.Agent8SixBudgetSource
