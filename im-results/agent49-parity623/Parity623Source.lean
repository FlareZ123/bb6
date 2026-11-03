import BusyBeaver.BB6.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

/-!
# Original-source BB(6) #623 high-level blank-orbit parity
The following statements use DeepMind's *actual* Lean definitions of evalA,
drainB, highLevelNext and HighLevelState. Compile in an upstream Cryptids
checkout at the exact pinned commit using the repository's manual CI workflow.
No rule definitions are copied or replaced in this file. No sorry.
-/

namespace BB6.Agent49ParitySource

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

private abbrev State := HighLevelState
private abbrev next : State → Option State := highLevelNext

/-- A successful A-transition preserves the parity of a + (k + 1). -/
theorem evalA_parity (a : Nat) :
    ∀ k m aa bb dd : Nat, evalA a k m = some (aa, bb, dd) →
      (aa + bb) % 2 = (a + k + 1) % 2 := by
  induction a with
  | zero =>
    intro k m aa bb dd h
    rw [evalA] at h
    by_cases hk2 : k % 3 = 2
    · simp [hk2] at h
      cases h
      omega
    · by_cases hk0 : k % 3 = 0
      · simp [hk2, hk0] at h
      · simp [hk2, hk0] at h
        cases h
        omega
  | succ a ih =>
    intro k m aa bb dd h
    rw [evalA] at h
    by_cases hk2 : k % 3 = 2
    · simp [hk2] at h
      cases h
      omega
    · by_cases hk0 : k % 3 = 0
      · simp [hk2, hk0] at h
        cases h
        omega
      · simp [hk2, hk0] at h
        have hp := ih (k / 3) (m + 2 * (k / 3) + 3) aa bb dd h
        omega

/-- Every successful B-drain returns with first counter parity a + b. -/
theorem evalA_mass (a : Nat) :
    ∀ k m aa bb dd : Nat, evalA a k m = some (aa, bb, dd) →
      a + m ≤ aa + bb + dd := by
  induction a with
  | zero =>
    intro k m aa bb dd h
    rw [evalA] at h
    by_cases hk2 : k % 3 = 2
    · simp [hk2] at h
      cases h
      omega
    · by_cases hk0 : k % 3 = 0
      · simp [hk2, hk0] at h
      · simp [hk2, hk0] at h
        cases h
        omega
  | succ a ih =>
    intro k m aa bb dd h
    rw [evalA] at h
    by_cases hk2 : k % 3 = 2
    · simp [hk2] at h
      cases h
      omega
    · by_cases hk0 : k % 3 = 0
      · simp [hk2, hk0] at h
        cases h
        omega
      · simp [hk2, hk0] at h
        have hm := ih (k / 3) (m + 2 * (k / 3) + 3) aa bb dd h
        omega

theorem evalA_mass_positive (a k m aa bb dd : Nat)
    (ha : 0 < a)
    (h : evalA a k m = some (aa, bb, dd)) :
    a + m + 1 ≤ aa + bb + dd := by
  rw [evalA] at h
  have hn : a ≠ 0 := by omega
  by_cases hk2 : k % 3 = 2
  · simp [hk2] at h
    cases h
    omega
  · by_cases hk0 : k % 3 = 0
    · simp [hk2, hn, hk0] at h
      cases h
      omega
    · simp [hk2, hn, hk0] at h
      have hm := evalA_mass (a - 1) (k / 3) (m + 2 * (k / 3) + 3) aa bb dd h
      omega

theorem drainB_mass (b : Nat) :
    ∀ a d aa dd : Nat, drainB a b d = some (.D aa dd) →
      (a + b + d ≤ aa + dd) ∧ (0 < b → a + d + 2 * b + 3 ≤ aa + dd) := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro a d aa dd h
    rw [drainB] at h
    by_cases hb : b = 0
    · simp [hb] at h
      cases h
      constructor <;> omega
    · simp only [if_neg hb] at h
      cases he : evalA a (b - 1) (d + 2 * b + 3) with
      | none => simp [he] at h
      | some p =>
        rcases p with ⟨a1, b1, d1⟩
        simp only [he, Option.bind_some] at h
        by_cases hlt : b1 < b
        · simp only [if_pos hlt] at h
          have hm := evalA_mass a (b - 1) (d + 2 * b + 3) a1 b1 d1 he
          have hr := ih b1 hlt a1 d1 aa dd h
          constructor <;> omega
        · simp [hlt] at h

theorem drainB_parity (b : Nat) :
    ∀ a d aa dd : Nat, drainB a b d = some (.D aa dd) →
      aa % 2 = (a + b) % 2 := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro a d aa dd h
    rw [drainB] at h
    by_cases hb : b = 0
    · simp [hb] at h
      cases h
      omega
    · simp only [if_neg hb] at h
      cases he : evalA a (b - 1) (d + 2 * b + 3) with
      | none => simp [he] at h
      | some p =>
        rcases p with ⟨a1, b1, d1⟩
        simp only [he, Option.bind_some] at h
        by_cases hlt : b1 < b
        · simp only [if_pos hlt] at h
          have hp := evalA_parity a (b - 1) (d + 2 * b + 3) a1 b1 d1 he
          have hr := ih b1 hlt a1 d1 aa dd h
          omega
        · simp [hlt] at h

/-- Every surviving return from an even-a section remains in even a. -/
theorem next_preserves_even (a d aa dd : Nat)
    (ha : a % 2 = 0)
    (hstep : next (.D a d) = some (.D aa dd)) : aa % 2 = 0 := by
  simp only [next, highLevelNext] at hstep
  by_cases h0 : a = 0
  · simp only [if_pos h0] at hstep
    by_cases hd : d % 2 = 1
    · simp only [if_pos hd] at hstep
      have hp := drainB_parity 2 (d + 1) 2 aa dd hstep
      omega
    · simp only [if_neg hd] at hstep
      cases hstep
      omega
  · simp only [if_neg h0] at hstep
    by_cases h1 : d % 2 = 1 ∧ a ≥ d + 5
    · simp only [if_pos h1] at hstep
      have hp := drainB_parity (d + 3) (a - d - 5) 5 aa dd hstep
      omega
    · simp only [if_neg h1] at hstep
      by_cases h2 : d % 2 = 0 ∧ a ≥ d + 3
      · simp only [if_pos h2] at hstep
        have hp := drainB_parity (d + 2) (a - d - 2) 2 aa dd hstep
        omega
      · simp only [if_neg h2] at hstep
        have heven : a % 2 ≠ 1 := by omega
        simp only [if_neg heven] at hstep
        by_cases h4 : a = d + 2
        · simp only [if_pos h4] at hstep
          have hp := drainB_parity a 0 2 aa dd hstep
          omega
        · simp only [if_neg h4] at hstep
          by_cases h5 : d % 2 = 1
          · simp only [if_pos h5] at hstep
            have hp := drainB_parity (a - 1) (d + 4 - a) 3 aa dd hstep
            omega
          · simp only [if_neg h5] at hstep
            cases he : evalA (d + 1 - a) a (2 * a + 5) with
            | none => simp [he] at hstep
            | some p =>
              rcases p with ⟨p1, p2, p3⟩
              simp only [he, Option.bind_some] at hstep
              have hp := evalA_parity (d + 1 - a) a (2 * a + 5) p1 p2 p3 he
              have hr := drainB_parity p2 p1 p3 aa dd hstep
              omega

theorem next_strict_mass (a d aa dd : Nat)
    (hstep : next (.D a d) = some (.D aa dd)) :
    a + d + 7 ≤ aa + dd := by
  simp only [next, highLevelNext] at hstep
  by_cases h0 : a = 0
  · simp only [if_pos h0] at hstep
    by_cases hd : d % 2 = 1
    · simp only [if_pos hd] at hstep
      have hp := drainB_mass 2 (d + 1) 2 aa dd hstep
      omega
    · simp only [if_neg hd] at hstep
      cases hstep
      omega
  · simp only [if_neg h0] at hstep
    by_cases h1 : d % 2 = 1 ∧ a ≥ d + 5
    · simp only [if_pos h1] at hstep
      have hp := drainB_mass (d + 3) (a - d - 5) 5 aa dd hstep
      omega
    · simp only [if_neg h1] at hstep
      by_cases h2 : d % 2 = 0 ∧ a ≥ d + 3
      · simp only [if_pos h2] at hstep
        have hp := drainB_mass (d + 2) (a - d - 2) 2 aa dd hstep
        omega
      · simp only [if_neg h2] at hstep
        by_cases h3 : a % 2 = 1
        · simp [h3] at hstep
        · simp only [if_neg h3] at hstep
          by_cases h4 : a = d + 2
          · simp only [if_pos h4] at hstep
            have hp := drainB_mass a 0 2 aa dd hstep
            omega
          · simp only [if_neg h4] at hstep
            by_cases h5 : d % 2 = 1
            · simp only [if_pos h5] at hstep
              have hp := drainB_mass (a - 1) (d + 4 - a) 3 aa dd hstep
              omega
            · simp only [if_neg h5] at hstep
              cases he : evalA (d + 1 - a) a (2 * a + 5) with
              | none => simp [he] at hstep
              | some p =>
                rcases p with ⟨p1, p2, p3⟩
                simp only [he, Option.bind_some] at hstep
                have hpos : 0 < d + 1 - a := by omega
                have hp := evalA_mass_positive (d + 1 - a) a (2 * a + 5) p1 p2 p3 hpos he
                have hr := drainB_mass p2 p1 p3 aa dd hstep
                omega

def run : Nat → Option State
  | 0 => some (.D 0 7)
  | n + 1 => (run n).bind next

/-- All surviving high-level blank-origin section visits have an even first counter. -/
theorem run_preserves_even (n a d : Nat)
    (h : run n = some (.D a d)) : a % 2 = 0 := by
  induction n generalizing a d with
  | zero =>
    simp only [run] at h
    cases h
    decide
  | succ n ih =>
    simp only [run] at h
    cases hr : run n with
    | none => simp [hr] at h
    | some s =>
      rcases s with ⟨aa, dd⟩
      simp only [hr, Option.bind_some] at h
      exact next_preserves_even aa dd a d (ih aa dd hr) h

/-- Even first counter alone cannot guarantee survival. -/
theorem run_grows_at_least_seven (n a d : Nat)
    (h : run n = some (.D a d)) :
    7 * (n + 1) ≤ a + d := by
  induction n generalizing a d with
  | zero =>
    simp only [run] at h
    cases h
    omega
  | succ n ih =>
    simp only [run] at h
    cases hr : run n with
    | none => simp [hr] at h
    | some s =>
      rcases s with ⟨aa, dd⟩
      simp only [hr, Option.bind_some] at h
      have h1 := ih aa dd hr
      have h2 := next_strict_mass aa dd a d h
      omega

theorem growth_constant_sharp : next (.D 0 0) = some (.D 0 7) := by rfl

theorem synthetic_even_halter : next (.D 4 2) = none := by decide +kernel
theorem synthetic_even_halter_two : next (.D 6 1) = none := by decide +kernel

#print axioms evalA_parity
#print axioms drainB_parity
#print axioms next_preserves_even
#print axioms run_preserves_even
#print axioms run_grows_at_least_seven
#print axioms synthetic_even_halter


/-- The evaluator fails exactly when the next base-three digit after a run of a ones is zero. -/
def badDigits : Nat → Nat → Prop
  | 0, k => k % 3 = 0
  | a + 1, k => k % 3 = 1 ∧ badDigits a (k / 3)

theorem evalA_none_iff_badDigits (a : Nat) :
    ∀ k m : Nat, evalA a k m = none ↔ badDigits a k := by
  induction a with
  | zero =>
    intro k m
    rw [evalA, badDigits]
    by_cases h2 : k % 3 = 2
    · simp [h2]
    · by_cases h0 : k % 3 = 0
      · simp [h2, h0]
      · simp [h2, h0]
  | succ a ih =>
    intro k m
    rw [evalA, badDigits]
    by_cases h2 : k % 3 = 2
    · simp [h2]
    · by_cases h0 : k % 3 = 0
      · simp [h2, h0]
      · have h1 : k % 3 = 1 := by omega
        simp [h2, h0, h1, ih]

/-- The integer with a least-significant base-three digits all one. -/
def ternaryOnes : Nat → Nat
  | 0 => 0
  | a + 1 => 3 * ternaryOnes a + 1

theorem twice_ones_add_one_eq_pow (a : Nat) :
    2 * ternaryOnes a + 1 = 3 ^ a := by
  induction a with
  | zero => simp [ternaryOnes]
  | succ a ih =>
    simp only [ternaryOnes, Nat.pow_succ]
    omega

theorem badDigits_iff_ternaryCylinder (a : Nat) :
    ∀ k : Nat, badDigits a k ↔ k % (3 ^ (a + 1)) = ternaryOnes a := by
  induction a with
  | zero =>
    intro k
    simp [badDigits, ternaryOnes]
  | succ a ih =>
    intro k
    rw [badDigits, ternaryOnes]
    have hp : 3 ^ (a + 1 + 1) = 3 * 3 ^ (a + 1) := by
      rw [Nat.pow_succ]
      omega
    rw [hp, Nat.mod_mul, ih]
    have hmod : k % 3 < 3 := Nat.mod_lt _ (by omega)
    omega

theorem evalA_none_iff_ternaryCylinder (a k m : Nat) :
    evalA a k m = none ↔ k % 3 ^ (a + 1) = ternaryOnes a := by
  rw [evalA_none_iff_badDigits, badDigits_iff_ternaryCylinder]

theorem ternaryOnes_eq_half (a : Nat) :
    ternaryOnes a = (3 ^ a - 1) / 2 := by
  have h := twice_ones_add_one_eq_pow a
  omega

/-- All-a exact Diophantine criterion for intermediate evaluator halting. -/
theorem evalA_none_iff_ternaryCongruence (a k m : Nat) :
    evalA a k m = none ↔ k % 3 ^ (a + 1) = (3 ^ a - 1) / 2 := by
  rw [evalA_none_iff_ternaryCylinder, ternaryOnes_eq_half]

#print axioms evalA_none_iff_ternaryCongruence


theorem ternaryOnes_ge (a : Nat) : a ≤ ternaryOnes a := by
  induction a with
  | zero => simp [ternaryOnes]
  | succ a ih =>
    simp only [ternaryOnes]
    omega

theorem evalA_none_requires_a_le_k (a k m : Nat)
    (h : evalA a k m = none) : a ≤ k := by
  have hc := (evalA_none_iff_ternaryCylinder a k m).mp h
  have hbound : ternaryOnes a ≤ k := by
    rw [← hc]
    exact Nat.mod_le _ _
  have hg := ternaryOnes_ge a
  omega

/-- Direct-halt evaluator gate is impossible if its first counter exceeds k. -/
theorem evalA_succeeds_if_a_gt_k (a k m : Nat) (h : k < a) :
    ∃ aa bb dd, evalA a k m = some (aa, bb, dd) := by
  cases he : evalA a k m with
  | none =>
    have hab := evalA_none_requires_a_le_k a k m he
    omega
  | some p =>
    rcases p with ⟨aa, bb, dd⟩
    exact ⟨aa, bb, dd, rfl⟩

/-- The last next branch's direct evaluator cannot halt when d >= 2a. -/
theorem highLevel_last_evalA_safe_beyond_diagonal (a d : Nat)
    (h : 2 * a ≤ d) : ∃ aa bb dd,
    evalA (d + 1 - a) a (2 * a + 5) = some (aa, bb, dd) := by
  apply evalA_succeeds_if_a_gt_k
  omega

#print axioms highLevel_last_evalA_safe_beyond_diagonal


/-- Intermediate evaluator cannot increase its residual 110-block index. -/
theorem evalA_b_le_k (a : Nat) :
    ∀ k m aa bb dd : Nat, evalA a k m = some (aa, bb, dd) → bb ≤ k := by
  induction a with
  | zero =>
    intro k m aa bb dd h
    rw [evalA] at h
    by_cases h2 : k % 3 = 2
    · simp [h2] at h
      cases h
      omega
    · by_cases h0 : k % 3 = 0
      · simp [h2, h0] at h
      · simp [h2, h0] at h
        cases h
        omega
  | succ a ih =>
    intro k m aa bb dd h
    rw [evalA] at h
    by_cases h2 : k % 3 = 2
    · simp [h2] at h
      cases h
      omega
    · by_cases h0 : k % 3 = 0
      · simp [h2, h0] at h
        cases h
        omega
      · simp [h2, h0] at h
        have hi := ih (k / 3) (m + 2 * (k / 3) + 3) aa bb dd h
        omega

/-- The decrease guard built into source drainB is automatically satisfied on success. -/
theorem evalA_from_drain_strictly_reduces_b (a b d aa bb dd : Nat)
    (hb : 0 < b)
    (h : evalA a (b - 1) (d + 2 * b + 3) = some (aa, bb, dd)) : bb < b := by
  have hi := evalA_b_le_k a (b - 1) (d + 2 * b + 3) aa bb dd h
  omega

#print axioms evalA_from_drain_strictly_reduces_b

end BB6.Agent49ParitySource
