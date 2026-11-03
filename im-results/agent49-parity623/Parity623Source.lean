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


/-- Successful evaluator and a gap of two imply output a strictly exceeds b. -/
theorem evalA_safe_gap (a : Nat) : ∀ k m : Nat, k + 2 ≤ a →
    ∃ aa bb dd, evalA a k m = some (aa, bb, dd) ∧ bb < aa := by
  induction a with
  | zero =>
    intro k m hb
    omega
  | succ a ih =>
    intro k m hb
    rw [evalA]
    by_cases h2 : k % 3 = 2
    · simp only [if_pos h2]
      refine ⟨a + 2, k / 3, m, rfl, ?_⟩
      omega
    · by_cases h0 : k % 3 = 0
      · simp only [if_neg h2, Nat.succ_ne_zero, if_pos h0]
        refine ⟨a, k / 3, m + 2, rfl, ?_⟩
        omega
      · have hgap : k / 3 + 2 ≤ a := by omega
        obtain ⟨aa, bb, dd, he, hlt⟩ := ih (k / 3) (m + 2 * (k / 3) + 3) hgap
        simp only [if_neg h2, Nat.succ_ne_zero, if_neg h0]
        exact ⟨aa, bb, dd, he, hlt⟩

/-- Every positive-b B-drain with a>b returns safely and still has positive a. -/
theorem drainB_safe_gap (b : Nat) : ∀ a d : Nat, b < a →
    ∃ aa dd, drainB a b d = some (.D aa dd) ∧ 0 < aa := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro a d hg
    rw [drainB]
    by_cases hb : b = 0
    · simp only [if_pos hb]
      exact ⟨a, d, rfl, by omega⟩
    · simp only [if_neg hb]
      have hgap : b - 1 + 2 ≤ a := by omega
      obtain ⟨a1, b1, d1, he, hlt⟩ := evalA_safe_gap a (b-1) (d+2*b+3) hgap
      have hdec : b1 < b := evalA_from_drain_strictly_reduces_b a b d a1 b1 d1 (by omega) he
      obtain ⟨aa, dd, hr, hp⟩ := ih b1 hdec a1 d1 hlt
      simp only [he, Option.bind_some, if_pos hdec]
      exact ⟨aa, dd, hr, hp⟩

/-- Even, positive block counters permit the weaker one-unit input gap. -/
theorem evalA_safe_gap_even (a : Nat) : ∀ k m : Nat,
    2 ≤ k → k % 2 = 0 → k + 1 ≤ a →
    ∃ aa bb dd, evalA a k m = some (aa, bb, dd) ∧ bb < aa := by
  induction a with
  | zero =>
    intro k m hk he hg
    omega
  | succ a ih =>
    intro k m hk he hg
    rw [evalA]
    by_cases h2 : k % 3 = 2
    · simp only [if_pos h2]
      refine ⟨a + 2, k / 3, m, rfl, ?_⟩
      omega
    · by_cases h0 : k % 3 = 0
      · simp only [if_neg h2, Nat.succ_ne_zero, if_pos h0]
        refine ⟨a, k / 3, m + 2, rfl, ?_⟩
        omega
      · have hgap : k / 3 + 2 ≤ a := by omega
        obtain ⟨aa, bb, dd, hh, hlt⟩ := evalA_safe_gap a (k / 3) (m + 2 * (k / 3) + 3) hgap
        simp only [if_neg h2, Nat.succ_ne_zero, if_neg h0]
        exact ⟨aa, bb, dd, hh, hlt⟩

/-- Uniform halting-free outer half-plane for the full high-level #623 step. -/
theorem next_safe_outer_cone (a d : Nat)
    (ha : 0 < a) (he : a % 2 = 0) (hd : 2 * a ≤ d) :
    ∃ aa dd, next (.D a d) = some (.D aa dd) := by
  simp only [next, highLevelNext]
  have h0 : a ≠ 0 := by omega
  have h1 : ¬ (d % 2 = 1 ∧ a ≥ d + 5) := by omega
  have h2 : ¬ (d % 2 = 0 ∧ a ≥ d + 3) := by omega
  have hodd : a % 2 ≠ 1 := by omega
  have h4 : a ≠ d + 2 := by omega
  simp only [if_neg h0, if_neg h1, if_neg h2, if_neg hodd, if_neg h4]
  by_cases hdodd : d % 2 = 1
  · simp only [if_pos hdodd]
    have hg : a - 1 < d + 4 - a := by omega
    obtain ⟨aa, dd, hret, _⟩ := drainB_safe_gap (a - 1) (d + 4 - a) 3 hg
    exact ⟨aa, dd, hret⟩
  · simp only [if_neg hdodd]
    have hk : 2 ≤ a := by omega
    have hgap : a + 1 ≤ d + 1 - a := by omega
    obtain ⟨p1, p2, p3, heval, hg⟩ :=
      evalA_safe_gap_even (d + 1 - a) a (2 * a + 5) hk he hgap
    simp only [heval, Option.bind_some]
    obtain ⟨aa, dd, hret, _⟩ := drainB_safe_gap p2 p1 p3 hg
    exact ⟨aa, dd, hret⟩

#print axioms drainB_safe_gap
#print axioms next_safe_outer_cone


/-- All zero-a high-level states survive one accelerated step. -/
theorem next_zero_total (d : Nat) :
    ∃ aa dd, next (.D 0 d) = some (.D aa dd) := by
  simp only [next, highLevelNext]
  by_cases hodd : d % 2 = 1
  · simp only [if_pos hodd]
    by_cases h1 : d = 1
    · subst d
      exact ⟨0, 14, by decide +kernel⟩
    · have hd : 3 ≤ d := by omega
      have hg : 2 < d + 1 := by omega
      obtain ⟨aa, dd, hr, _⟩ := drainB_safe_gap 2 (d + 1) 2 hg
      exact ⟨aa, dd, hr⟩
  · simp only [if_neg hodd]
    exact ⟨d, 7, rfl⟩

/-- Any halting transition with even first counter must lie in the inner wedge. -/
theorem next_none_requires_inner_wedge (a d : Nat)
    (he : a % 2 = 0) (h : next (.D a d) = none) : 0 < a ∧ d < 2 * a := by
  have hpos : 0 < a := by
    by_cases h0 : a = 0
    · subst a
      obtain ⟨aa, dd, hr⟩ := next_zero_total d
      rw [hr] at h
      contradiction
    · omega
  have hinner : d < 2 * a := by
    by_cases hz : d < 2 * a
    · exact hz
    · have hc : 2 * a ≤ d := by omega
      obtain ⟨aa, dd, hr⟩ := next_safe_outer_cone a d hpos he hc
      rw [hr] at h
      contradiction
  exact ⟨hpos, hinner⟩

#print axioms next_none_requires_inner_wedge

/-- Far-left half-plane is safe independently of parity. -/
theorem next_safe_far_left (a d : Nat)
    (h : 2 * d + 10 ≤ a) : ∃ aa dd, next (.D a d) = some (.D aa dd) := by
  simp only [next, highLevelNext]
  have h0 : a ≠ 0 := by omega
  simp only [if_neg h0]
  by_cases hodd : d % 2 = 1
  · have h1 : d % 2 = 1 ∧ a ≥ d + 5 := ⟨hodd, by omega⟩
    simp only [if_pos h1]
    have hg : d + 3 < a - d - 5 := by omega
    obtain ⟨aa, dd, hr, _⟩ := drainB_safe_gap (d + 3) (a - d - 5) 5 hg
    exact ⟨aa, dd, hr⟩
  · have h1 : ¬ (d % 2 = 1 ∧ a ≥ d + 5) := by omega
    have h2 : d % 2 = 0 ∧ a ≥ d + 3 := by omega
    simp only [if_neg h1, if_pos h2]
    have hg : d + 2 < a - d - 2 := by omega
    obtain ⟨aa, dd, hr, _⟩ := drainB_safe_gap (d + 2) (a - d - 2) 2 hg
    exact ⟨aa, dd, hr⟩

/-- Every even-a halting step is confined to a narrow, explicit diagonal corridor. -/
theorem next_none_requires_corridor (a d : Nat)
    (he : a % 2 = 0) (h : next (.D a d) = none) :
    0 < a ∧ d < 2 * a ∧ a < 2 * d + 10 := by
  have hw := next_none_requires_inner_wedge a d he h
  have hc : a < 2 * d + 10 := by
    by_cases hb : a < 2 * d + 10
    · exact hb
    · have hs : 2 * d + 10 ≤ a := by omega
      obtain ⟨aa, dd, hr⟩ := next_safe_far_left a d hs
      rw [hr] at h
      contradiction
  exact ⟨hw.1, hw.2, hc⟩

#print axioms next_none_requires_corridor

/-- With k >= 2, a one-unit input gap forces a strict evaluator output gap. -/
theorem evalA_safe_gap_one (a k m : Nat) (hk : 2 ≤ k) (h : k+1 ≤ a) :
    ∃ aa bb dd, evalA a k m = some (aa, bb, dd) ∧ bb < aa := by
  rw [evalA]
  have ha : a ≠ 0 := by omega
  by_cases h2 : k % 3 = 2
  · simp only [if_pos h2]
    refine ⟨a+1,k/3,m,rfl,?_⟩
    omega
  · by_cases h0 : k % 3 = 0
    · simp only [if_neg h2, if_neg ha, if_pos h0]
      refine ⟨a-1,k/3,m+2,rfl,?_⟩
      omega
    · have hk4 : 4 ≤ k := by omega
      have hg : k/3+2 ≤ a-1 := by omega
      obtain ⟨aa,bb,dd,he,hp⟩ := evalA_safe_gap (a-1) (k/3) (m+2*(k/3)+3) hg
      simp only [if_neg h2, if_neg ha, if_neg h0]
      exact ⟨aa,bb,dd,he,hp⟩

theorem evalA_one (a m : Nat) (ha : 2 ≤ a) :
    evalA a 1 m = some (a-2, 0, m+5) := by
  have h0 : a ≠ 0 := by omega
  have h1 : a-1 ≠ 0 := by omega
  rw [evalA]
  simp only [show 1%3 ≠ 2 by decide, if_neg, h0, show 1%3 ≠ 0 by decide]
  rw [evalA]
  simp only [show 0%3 ≠ 2 by decide, if_neg, h1, show 0%3 = 0 by decide, if_pos]
  congr 1 <;> omega

theorem evalA_four (a m : Nat) (ha : 3 ≤ a) :
    evalA a 4 m = some (a-3,0,m+10) := by
  have h0 : a ≠ 0 := by omega
  rw [evalA]
  simp only [show 4%3 ≠ 2 by decide, if_neg, h0, show 4%3 ≠ 0 by decide]
  have h1 : 2 ≤ a-1 := by omega
  rw [evalA_one (a-1) (m+2*(4/3)+3) h1]
  congr 1 <;> omega

/-- The evaluator either produces a strict first-counter advantage or zero remaining blocks. -/
theorem evalA_safe_third_two (a k m : Nat) (h : k/3+2 ≤ a) :
    ∃ aa bb dd, evalA a k m = some (aa,bb,dd) ∧ (bb<aa ∨ bb=0) := by
  have ha : a ≠ 0 := by omega
  by_cases h2 : k%3=2
  · rw [evalA]
    simp only [if_pos h2]
    refine ⟨a+1,k/3,m,rfl,Or.inl ?_⟩
    omega
  · by_cases h0 : k%3=0
    · rw [evalA]
      simp only [if_neg h2, if_neg ha, if_pos h0]
      refine ⟨a-1,k/3,m+2,rfl,Or.inl ?_⟩
      omega
    · have h1 : k%3=1 := by omega
      by_cases hk : 2 ≤ k/3
      · have hi : k/3+1 ≤ a-1 := by omega
        obtain ⟨aa,bb,dd,he,hp⟩ := evalA_safe_gap_one (a-1) (k/3) (m+2*(k/3)+3) hk hi
        rw [evalA]
        simp only [if_neg h2, if_neg ha, if_neg h0]
        exact ⟨aa,bb,dd,he,Or.inl hp⟩
      · have hcase : k=1 ∨ k=4 := by omega
        rcases hcase with hcase | hcase
        · subst k
          have h2a : 2 ≤ a := by omega
          exact ⟨a-2,0,m+5,evalA_one a m h2a,Or.inr rfl⟩
        · subst k
          have h3a : 3 ≤ a := by omega
          exact ⟨a-3,0,m+10,evalA_four a m h3a,Or.inr rfl⟩

/-- A B-drain is safe whenever its first counter exceeds one-third of the initial block index by two. -/
theorem drainB_safe_third_two (a b d : Nat) (hb : 0 < b)
    (h : (b-1)/3+2 ≤ a) :
    ∃ aa dd, drainB a b d = some (.D aa dd) := by
  rw [drainB]
  have hn : b ≠ 0 := by omega
  simp only [if_neg hn]
  obtain ⟨a1,b1,d1,he,hp⟩ := evalA_safe_third_two a (b-1) (d+2*b+3) h
  have hdec : b1 < b := by
    have hv := evalA_b_le_k a (b-1) (d+2*b+3) a1 b1 d1 he
    omega
  rcases hp with hlt | hz
  · obtain ⟨aa,dd,hr,_⟩ := drainB_safe_gap b1 a1 d1 hlt
    simp only [he, Option.bind_some, if_pos hdec]
    exact ⟨aa,dd,hr⟩
  · subst b1
    simp only [he, Option.bind_some, if_pos hdec]
    exact ⟨a1,d1,by rw [drainB]; simp⟩

/-- Parity-dependent right-hand guaranteed-survival cones. -/
theorem next_safe_right_third_two (a d : Nat)
    (hodd : d%2=1 → d+7+(d+2)/3 ≤ a)
    (heven : d%2=0 → d+4+(d+1)/3 ≤ a) :
    ∃ aa dd, next (.D a d) = some (.D aa dd) := by
  simp only [next]
  have ha : a ≠ 0 := by
    by_cases hd : d%2=1
    · have hb := hodd hd
      omega
    · have hd0 : d%2=0 := by omega
      have hb := heven hd0
      omega
  simp only [if_neg ha]
  by_cases hd : d%2=1
  · have h1 : d%2=1 ∧ a ≥ d+5 := ⟨hd, by have hh:=hodd hd; omega⟩
    simp only [if_pos h1]
    have hgap : ((d+3)-1)/3+2 ≤ a-d-5 := by have hh:=hodd hd; omega
    exact drainB_safe_third_two (a-d-5) (d+3) 5 (by omega) hgap
  · have hd0 : d%2=0 := by omega
    have h1 : ¬ (d%2=1 ∧ a ≥ d+5) := by omega
    have h2 : d%2=0 ∧ a ≥ d+3 := ⟨hd0, by have hh:=heven hd0; omega⟩
    simp only [if_neg h1, if_pos h2]
    have hgap : ((d+2)-1)/3+2 ≤ a-d-2 := by have hh:=heven hd0; omega
    exact drainB_safe_third_two (a-d-2) (d+2) 2 (by omega) hgap

theorem evalA_then_drain_safe_third_two (a k m : Nat) (h : k/3+2 ≤ a) :
    ∃ aa dd, (evalA a k m).bind (fun p => drainB p.1 p.2.1 p.2.2) = some (.D aa dd) := by
  obtain ⟨a1,b1,d1,he,hp⟩ := evalA_safe_third_two a k m h
  simp only [he, Option.bind_some]
  rcases hp with hlt | hz
  · obtain ⟨aa,dd,hr,_⟩ := drainB_safe_gap b1 a1 d1 hlt
    exact ⟨aa,dd,hr⟩
  · subst b1
    exact ⟨a1,d1,by rw [drainB]; simp⟩

/-- Positive even-a left-hand guaranteed-survival cone. -/
theorem next_safe_left_third_two (a d : Nat)
    (ha : 0<a) (he : a%2=0) (hd : a+a/3+1 ≤ d) :
    ∃ aa dd, next (.D a d) = some (.D aa dd) := by
  simp only [next]
  have h0 : a ≠ 0 := by omega
  have h1 : ¬ (d%2=1 ∧ a≥d+5) := by omega
  have h2 : ¬ (d%2=0 ∧ a≥d+3) := by omega
  have hodd : a%2 ≠ 1 := by omega
  have h4 : a ≠ d+2 := by omega
  simp only [if_neg h0, if_neg h1, if_neg h2, if_neg hodd, if_neg h4]
  by_cases hdo : d%2=1
  · simp only [if_pos hdo]
    have hbn : 0 < a-1 := by omega
    have hgap : ((a-1)-1)/3+2 ≤ d+4-a := by omega
    exact drainB_safe_third_two (d+4-a) (a-1) 3 hbn hgap
  · simp only [if_neg hdo]
    have hgap : a/3+2 ≤ d+1-a := by omega
    exact evalA_then_drain_safe_third_two (d+1-a) a (2*a+5) hgap

/-- Necessary halting corridor for every even-a section state, not a rooted decision. -/
theorem next_none_requires_tight_corridor (a d : Nat)
    (he : a%2=0) (h : next (.D a d) = none) :
    0<a ∧ d<a+a/3+1 ∧
      (if d%2=1 then a<d+7+(d+2)/3 else a<d+4+(d+1)/3) := by
  have ha : 0<a := by
    by_cases z : a=0
    · subst a
      obtain ⟨aa,dd,hret⟩ := next_zero_total d
      rw [hret] at h
      contradiction
    · omega
  have hl : d<a+a/3+1 := by
    by_cases hh : d<a+a/3+1
    · exact hh
    have hs : a+a/3+1 ≤ d := by omega
    obtain ⟨aa,dd,hr⟩ := next_safe_left_third_two a d ha he hs
    rw [hr] at h
    contradiction
  have hr : (if d%2=1 then a<d+7+(d+2)/3 else a<d+4+(d+1)/3) := by
    by_cases hd : d%2=1
    · simp only [if_pos hd]
      by_cases hh : a<d+7+(d+2)/3
      · exact hh
      have hs : d+7+(d+2)/3 ≤ a := by omega
      have hf : d%2=0 → d+4+(d+1)/3≤a := by omega
      obtain ⟨aa,dd,hret⟩ := next_safe_right_third_two a d (by intro _; exact hs) hf
      rw [hret] at h
      contradiction
    · simp only [if_neg hd]
      by_cases hh : a<d+4+(d+1)/3
      · exact hh
      have hd0 : d%2=0 := by omega
      have hs : d+4+(d+1)/3 ≤ a := by omega
      have hf : d%2=1 → d+7+(d+2)/3≤a := by omega
      obtain ⟨aa,dd,hret⟩ := next_safe_right_third_two a d hf (by intro _; exact hs)
      rw [hret] at h
      contradiction
  exact ⟨ha,hl,hr⟩

#print axioms next_none_requires_tight_corridor

/-- Under a power-of-three budget, evalA either exhausts the residual blocks or preserves a smaller power budget. -/
theorem evalA_exp (a : Nat) : ∀ k m : Nat, k < 3^a →
    ∃ aa bb dd, evalA (a+1) k m = some (aa,bb,dd) ∧
      (bb=0 ∨ ∃ t, aa=t+1 ∧ bb<3^t) := by
  induction a with
  | zero =>
    intro k m hk
    have hz : k=0 := by simpa using hk
    subst k
    refine ⟨0,0,m+2,?_,Or.inl rfl⟩
    simp [evalA]
  | succ a ih =>
    intro k m hk
    have hkdiv : k/3 < 3^a := by
      rw [Nat.pow_succ] at hk
      omega
    rw [evalA]
    by_cases h2 : k%3=2
    · simp only [if_pos h2]
      have hp : 3^a ≤ 3^(a+2) := by
        have hpos : 0 < 3^a := Nat.pow_pos (by omega)
        have hpow : 3^(a+2) = (3^a)*9 := by
          rw [show a+2 = (a+1)+1 by omega, Nat.pow_succ, Nat.pow_succ]
          omega
        omega
      refine ⟨a+3,k/3,m,by congr 1 <;> omega,Or.inr ⟨a+2,by omega,?_⟩⟩
      omega
    · have hnonzero : a+1+1 ≠ 0 := by omega
      by_cases h0 : k%3=0
      · simp only [if_neg h2, if_neg hnonzero, if_pos h0]
        refine ⟨a+1,k/3,m+2,by congr 1 <;> omega,Or.inr ⟨a,rfl,hkdiv⟩⟩
      · obtain ⟨aa,bb,dd,he,hp⟩ := ih (k/3) (m+2*(k/3)+3) hkdiv
        simp only [if_neg h2, if_neg hnonzero, if_neg h0]
        exact ⟨aa,bb,dd,by simpa only [show a+1+1-1=a+1 by omega] using he,hp⟩

/-- Exponential budget yields a universal halting-free B-drain. -/
theorem drainB_exp (b : Nat) : ∀ a d : Nat, b ≤ 3^a →
    ∃ aa dd, drainB (a+1) b d = some (.D aa dd) := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro a d hpow
    rw [drainB]
    by_cases hb : b=0
    · simp only [if_pos hb]
      exact ⟨a+1,d,rfl⟩
    · simp only [if_neg hb]
      have hk : b-1 < 3^a := by omega
      obtain ⟨a1,b1,d1,he,hp⟩ := evalA_exp a (b-1) (d+2*b+3) hk
      have hdec : b1 < b := by
        have hv := evalA_b_le_k (a+1) (b-1) (d+2*b+3) a1 b1 d1 he
        omega
      rcases hp with hz | ⟨t,ht,hp⟩
      · subst b1
        simp only [he, Option.bind_some, if_pos hdec]
        exact ⟨a1,d1,by rw [drainB]; simp⟩
      · subst a1
        obtain ⟨aa,dd,hr⟩ := ih b1 hdec t d1 (by omega)
        simp only [he, Option.bind_some, if_pos hdec]
        exact ⟨aa,dd,hr⟩

theorem evalA_then_drain_exp (a k m : Nat) (h : k<3^a) :
    ∃ aa dd, (evalA (a+1) k m).bind (fun p => drainB p.1 p.2.1 p.2.2) = some (.D aa dd) := by
  obtain ⟨a1,b1,d1,he,hp⟩ := evalA_exp a k m h
  simp only [he, Option.bind_some]
  rcases hp with hz | ⟨t,ht,hpow⟩
  · subst b1
    exact ⟨a1,d1,by rw [drainB]; simp⟩
  · subst a1
    obtain ⟨aa,dd,hr⟩ := drainB_exp b1 t d1 (by omega)
    exact ⟨aa,dd,hr⟩

theorem pow_three_plus_three (n : Nat) : 3^n ≤ 3^(n+3) := by
  have hp : 0<3^n := Nat.pow_pos (by omega)
  have hs : 3^(n+3) = 27 * 3^n := by
    rw [show n+3=(n+2)+1 by omega,
      show n+2=(n+1)+1 by omega, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ]
    omega
  omega

/-- Safe left region outside a logarithmic neighborhood of a=d. -/
theorem next_safe_left_exp (a d : Nat)
    (ha : 0<a) (he : a%2=0) (hd : a≤d) (hpow : a<3^(d-a)) :
    ∃ aa dd, next (.D a d) = some (.D aa dd) := by
  simp only [next]
  have h0 : a ≠ 0 := by omega
  have h1 : ¬ (d%2=1 ∧ a≥d+5) := by omega
  have h2 : ¬ (d%2=0 ∧ a≥d+3) := by omega
  have hodd : a%2 ≠ 1 := by omega
  have h4 : a ≠ d+2 := by omega
  simp only [if_neg h0, if_neg h1, if_neg h2, if_neg hodd, if_neg h4]
  by_cases hdo : d%2=1
  · simp only [if_pos hdo]
    have hbound : a-1≤3^(d+3-a) := by
      have hpowstep := pow_three_plus_three (d-a)
      have eq : d+3-a=(d-a)+3 := by omega
      rw [eq]
      omega
    have hr := drainB_exp (a-1) (d+3-a) 3 hbound
    have heq : d+4-a=(d+3-a)+1 := by omega
    rw [heq]
    exact hr
  · simp only [if_neg hdo]
    have heq : d+1-a=(d-a)+1 := by omega
    rw [heq]
    exact evalA_then_drain_exp (d-a) a (2*a+5) hpow

/-- Safe right region outside a logarithmic neighborhood of a=d. -/
theorem next_safe_right_exp (a d : Nat)
    (hodd : d%2=1 → d+6≤a ∧ d+3≤3^(a-d-6))
    (heven : d%2=0 → d+3≤a ∧ d+2≤3^(a-d-3)) :
    ∃ aa dd, next (.D a d) = some (.D aa dd) := by
  simp only [next]
  have h0 : a ≠ 0 := by
    by_cases hd : d%2=1
    · have hh:=(hodd hd).1
      omega
    · have hd0 : d%2=0 := by omega
      have hh:=(heven hd0).1
      omega
  simp only [if_neg h0]
  by_cases hd : d%2=1
  · have hh := hodd hd
    have h1 : d%2=1 ∧ a≥d+5 := ⟨hd, by omega⟩
    simp only [if_pos h1]
    have heq : a-d-5=(a-d-6)+1 := by omega
    rw [heq]
    exact drainB_exp (d+3) (a-d-6) 5 hh.2
  · have hd0 : d%2=0 := by omega
    have hh:=heven hd0
    have h1 : ¬ (d%2=1 ∧ a≥d+5) := by omega
    have h2 : d%2=0 ∧ a≥d+3 := ⟨hd0,hh.1⟩
    simp only [if_neg h1, if_pos h2]
    have heq : a-d-2=(a-d-3)+1 := by omega
    rw [heq]
    exact drainB_exp (d+2) (a-d-3) 2 hh.2

/-- A necessary logarithmic-width halting gateway for every even-a section. -/
theorem next_none_requires_log_gate (a d : Nat)
    (he : a%2=0) (h : next (.D a d) = none) :
    0<a ∧ (a≤d → 3^(d-a) ≤ a) ∧
    (d%2=1 → a<d+6 ∨ 3^(a-d-6)<d+3) ∧
    (d%2=0 → a<d+3 ∨ 3^(a-d-3)<d+2) := by
  have ha : 0<a := by
    by_cases hz : a=0
    · subst a
      obtain ⟨aa,dd,hret⟩ := next_zero_total d
      rw [hret] at h
      contradiction
    · omega
  have hl : a≤d → 3^(d-a) ≤ a := by
    intro hd
    by_cases hp : a<3^(d-a)
    · obtain ⟨aa,dd,hret⟩ := next_safe_left_exp a d ha he hd hp
      rw [hret] at h
      contradiction
    · omega
  have hodd : d%2=1 → a<d+6 ∨ 3^(a-d-6)<d+3 := by
    intro hd
    by_cases hsmall : a<d+6
    · exact Or.inl hsmall
    · right
      by_cases hp : 3^(a-d-6)<d+3
      · exact hp
      · have hs : d+6≤a ∧ d+3≤3^(a-d-6) := by omega
        have heven : d%2=0 → d+3≤a ∧ d+2≤3^(a-d-3) := by omega
        obtain ⟨aa,dd,hret⟩ := next_safe_right_exp a d (by intro _; exact hs) heven
        rw [hret] at h
        contradiction
  have heven : d%2=0 → a<d+3 ∨ 3^(a-d-3)<d+2 := by
    intro hd
    by_cases hsmall : a<d+3
    · exact Or.inl hsmall
    · right
      by_cases hp : 3^(a-d-3)<d+2
      · exact hp
      · have hs : d+3≤a ∧ d+2≤3^(a-d-3) := by omega
        have hodd : d%2=1 → d+6≤a ∧ d+3≤3^(a-d-6) := by omega
        obtain ⟨aa,dd,hret⟩ := next_safe_right_exp a d hodd (by intro _; exact hs)
        rw [hret] at h
        contradiction
  exact ⟨ha,hl,hodd,heven⟩

#print axioms next_none_requires_log_gate
#print axioms drainB_exp



/-- Every terminal accelerated section on the actual blank-start orbit obeys the logarithmic gate. -/
theorem blank_run_requires_log_gate (n a d : Nat)
    (hseen : run n = some (.D a d)) (hhalt : next (.D a d) = none) :
    0 < a ∧ (a ≤ d → 3^(d-a) ≤ a) ∧
    (d%2=1 → a<d+6 ∨ 3^(a-d-6)<d+3) ∧
    (d%2=0 → a<d+3 ∨ 3^(a-d-3)<d+2) := by
  exact next_none_requires_log_gate a d (run_preserves_even n a d hseen) hhalt

#print axioms blank_run_requires_log_gate


/-- Two extra ternary digits only increase the all-ones budget. -/
theorem ones_le_plus_two (a : Nat) : ternaryOnes a ≤ ternaryOnes (a+2) := by
  have heq : a+2 = (a+1)+1 := by omega
  rw [heq, ternaryOnes, ternaryOnes]
  omega

/-- A strict initial ternary-ones budget is preserved by every successful evaluator branch. -/
theorem evalA_ones_budget (a : Nat) : ∀ k m : Nat, k < ternaryOnes a →
    ∃ aa bb dd, evalA a k m = some (aa,bb,dd) ∧ bb ≤ ternaryOnes aa := by
  induction a with
  | zero =>
    intro k m hk
    simp [ternaryOnes] at hk
  | succ a ih =>
    intro k m hk
    rw [evalA]
    have ha : a+1 ≠ 0 := by omega
    by_cases h2 : k%3=2
    · simp only [if_pos h2]
      have hbound : k/3 ≤ ternaryOnes a := by
        simp only [ternaryOnes] at hk
        omega
      refine ⟨a+2,k/3,m,by congr 1 <;> omega,?_⟩
      have hm := ones_le_plus_two a
      omega
    · by_cases h0 : k%3=0
      · simp only [if_neg h2, if_neg ha, if_pos h0]
        have hbound : k/3 ≤ ternaryOnes a := by
          simp only [ternaryOnes] at hk
          omega
        exact ⟨a,k/3,m+2,by congr 1 <;> omega,hbound⟩
      · have hnew : k/3 < ternaryOnes a := by
          simp only [ternaryOnes] at hk
          omega
        obtain ⟨aa,bb,dd,he,hp⟩ := ih (k/3) (m+2*(k/3)+3) hnew
        simp only [if_neg h2, if_neg ha, if_neg h0]
        exact ⟨aa,bb,dd,he,hp⟩

/-- Every drain below the exact first-bad base-three threshold survives. -/
theorem drainB_safe_ones (b : Nat) : ∀ a d : Nat, b ≤ ternaryOnes a →
    ∃ aa dd, drainB a b d = some (.D aa dd) := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro a d hbound
    rw [drainB]
    by_cases hb : b=0
    · simp only [if_pos hb]
      exact ⟨a,d,rfl⟩
    · simp only [if_neg hb]
      have hk : b-1 < ternaryOnes a := by omega
      obtain ⟨a1,b1,d1,he,hp⟩ := evalA_ones_budget a (b-1) (d+2*b+3) hk
      have hdec : b1 < b := by
        have hi := evalA_b_le_k a (b-1) (d+2*b+3) a1 b1 d1 he
        omega
      obtain ⟨aa,dd,hr⟩ := ih b1 hdec a1 d1 hp
      simp only [he, Option.bind_some, if_pos hdec]
      exact ⟨aa,dd,hr⟩

/-- The first bad evaluator argument is exactly the base-three word of all ones. -/
theorem evalA_bad_ones (a : Nat) : ∀ m : Nat, evalA a (ternaryOnes a) m=none := by
  induction a with
  | zero =>
    intro m
    simp [evalA,ternaryOnes]
  | succ a ih =>
    intro m
    rw [evalA]
    have ha : a+1 ≠ 0 := by omega
    have h2 : ternaryOnes (a+1)%3 ≠ 2 := by simp [ternaryOnes]
    have h0 : ternaryOnes (a+1)%3 ≠ 0 := by simp [ternaryOnes]
    simp only [if_neg h2, if_neg ha, if_neg h0]
    have hdiv : ternaryOnes (a+1)/3=ternaryOnes a := by
      rw [ternaryOnes]
      omega
    rw [hdiv]
    have hs : a+1-1=a := by omega
    rw [hs]
    exact ih (m+2*(ternaryOnes a)+3)

/-- Every first-threshold B-drain fails, regardless of the third counter. -/
theorem drainB_first_halt (a d : Nat) :
    drainB a (ternaryOnes a+1) d = none := by
  rw [drainB]
  have hb : ternaryOnes a+1≠0 := by omega
  simp only [if_neg hb]
  have he : evalA a (ternaryOnes a+1-1) (d+2*(ternaryOnes a+1)+3)=none := by
    simpa only [Nat.add_sub_cancel] using
      (evalA_bad_ones a (d+2*(ternaryOnes a+1)+3))
  simp only [show ternaryOnes a+1-1 = ternaryOnes a by omega, evalA_bad_ones, Option.bind_none]

/-- Exact first-failure classification at and below the first threshold. -/
theorem drainB_first_failure_iff (a b d : Nat) (hbound : b ≤ ternaryOnes a+1) :
    drainB a b d = none ↔ b=ternaryOnes a+1 := by
  constructor
  · intro h
    by_cases hb : b=ternaryOnes a+1
    · exact hb
    · have hl : b≤ternaryOnes a := by omega
      obtain ⟨aa,dd,hr⟩ := drainB_safe_ones b a d hl
      rw [hr] at h
      contradiction
  · intro hb
    subst b
    exact drainB_first_halt a d

#print axioms drainB_safe_ones
#print axioms drainB_first_halt
#print axioms drainB_first_failure_iff


theorem ones_le_plus_three (a : Nat) : ternaryOnes a ≤ ternaryOnes (a+3) := by
  have heq : a+3 = ((a+1)+1)+1 := by omega
  rw [heq, ternaryOnes, ternaryOnes, ternaryOnes]
  omega

/-- Under the exact ternary-ones budget, evaluator plus complete drain survives. -/
theorem evalA_then_drain_ones (a k m : Nat) (h : k<ternaryOnes a) :
    ∃ aa dd, (evalA a k m).bind (fun p => drainB p.1 p.2.1 p.2.2) = some (.D aa dd) := by
  obtain ⟨a1,b1,d1,he,hp⟩ := evalA_ones_budget a k m h
  simp only [he, Option.bind_some]
  exact drainB_safe_ones b1 a1 d1 hp

/-- Sharper universal safe left side using the exact first-drain failure threshold. -/
theorem next_safe_left_ones (a d : Nat) (ha : 0<a) (he : a%2=0)
    (hd : a≤d) (hbudget : a<ternaryOnes (d+1-a)) :
    ∃ aa dd, next (.D a d) = some (.D aa dd) := by
  simp only [next]
  have h0 : a ≠ 0 := by omega
  have h1 : ¬ (d%2=1 ∧ a≥d+5) := by omega
  have h2 : ¬ (d%2=0 ∧ a≥d+3) := by omega
  have hodd : a%2 ≠ 1 := by omega
  have h4 : a ≠ d+2 := by omega
  simp only [if_neg h0, if_neg h1, if_neg h2, if_neg hodd, if_neg h4]
  by_cases hdo : d%2=1
  · simp only [if_pos hdo]
    have hi : d+4-a=(d+1-a)+3 := by omega
    have ht := ones_le_plus_three (d+1-a)
    rw [← hi] at ht
    have hbudget2 : a-1 ≤ ternaryOnes (d+4-a) := by omega
    exact drainB_safe_ones (a-1) (d+4-a) 3 hbudget2
  · simp only [if_neg hdo]
    exact evalA_then_drain_ones (d+1-a) a (2*a+5) hbudget

/-- Sharper universal safe right side using the exact first-drain threshold. -/
theorem next_safe_right_ones (a d : Nat)
    (hodd : d%2=1 → d+5≤a ∧ d+3≤ternaryOnes (a-d-5))
    (heven : d%2=0 → d+3≤a ∧ d+2≤ternaryOnes (a-d-2)) :
    ∃ aa dd, next (.D a d) = some (.D aa dd) := by
  simp only [next]
  have h0 : a ≠ 0 := by
    by_cases hd : d%2=1
    · have hh := (hodd hd).1
      omega
    · have hd0 : d%2=0 := by omega
      have hh := (heven hd0).1
      omega
  simp only [if_neg h0]
  by_cases hd : d%2=1
  · have hh:=hodd hd
    have h1 : d%2=1 ∧ a≥d+5 := ⟨hd,hh.1⟩
    simp only [if_pos h1]
    exact drainB_safe_ones (d+3) (a-d-5) 5 hh.2
  · have hd0 : d%2=0 := by omega
    have hh:=heven hd0
    have h1 : ¬ (d%2=1 ∧ a≥d+5) := by omega
    have h2 : d%2=0 ∧ a≥d+3 := ⟨hd0,hh.1⟩
    simp only [if_neg h1, if_pos h2]
    exact drainB_safe_ones (d+2) (a-d-2) 2 hh.2

/-- A necessary even-a halting corridor stated with exact ternary budget cutoffs. -/
theorem next_none_requires_ones_gate (a d : Nat)
    (he : a%2=0) (h : next (.D a d)=none) :
    0<a ∧ (a≤d → ternaryOnes (d+1-a) ≤ a) ∧
    (d%2=1 → a<d+5 ∨ ternaryOnes (a-d-5)<d+3) ∧
    (d%2=0 → a<d+3 ∨ ternaryOnes (a-d-2)<d+2) := by
  have ha : 0<a := by
    by_cases z : a=0
    · subst a
      obtain ⟨aa,dd,hret⟩ := next_zero_total d
      rw [hret] at h
      contradiction
    · omega
  have hl : a≤d → ternaryOnes (d+1-a)≤a := by
    intro hd
    by_cases hh : a<ternaryOnes (d+1-a)
    · obtain ⟨aa,dd,hret⟩ := next_safe_left_ones a d ha he hd hh
      rw [hret] at h
      contradiction
    · omega
  have hr : d%2=1 → a<d+5 ∨ ternaryOnes (a-d-5)<d+3 := by
    intro hd
    by_cases hs : a<d+5
    · exact Or.inl hs
    · right
      by_cases ht : ternaryOnes (a-d-5)<d+3
      · exact ht
      · have hh : d+5≤a ∧ d+3≤ternaryOnes (a-d-5) := by omega
        have hf : d%2=0 → d+3≤a ∧ d+2≤ternaryOnes (a-d-2) := by omega
        obtain ⟨aa,dd,hret⟩ := next_safe_right_ones a d (by intro _; exact hh) hf
        rw [hret] at h
        contradiction
  have hr2 : d%2=0 → a<d+3 ∨ ternaryOnes (a-d-2)<d+2 := by
    intro hd
    by_cases hs : a<d+3
    · exact Or.inl hs
    · right
      by_cases ht : ternaryOnes (a-d-2)<d+2
      · exact ht
      · have hh : d+3≤a ∧ d+2≤ternaryOnes (a-d-2) := by omega
        have hf : d%2=1 → d+5≤a ∧ d+3≤ternaryOnes (a-d-5) := by omega
        obtain ⟨aa,dd,hret⟩ := next_safe_right_ones a d hf (by intro _; exact hh)
        rw [hret] at h
        contradiction
  exact ⟨ha,hl,hr,hr2⟩

/-- The actual blank-origin orbit inherits the universal ternary budget terminal gate. -/
theorem blank_run_requires_ones_gate (n a d : Nat)
    (hseen : run n = some (.D a d)) (hhalt : next (.D a d)=none) :
    0<a ∧ (a≤d → ternaryOnes (d+1-a) ≤ a) ∧
    (d%2=1 → a<d+5 ∨ ternaryOnes (a-d-5)<d+3) ∧
    (d%2=0 → a<d+3 ∨ ternaryOnes (a-d-2)<d+2) := by
  exact next_none_requires_ones_gate a d (run_preserves_even n a d hseen) hhalt

#print axioms next_none_requires_ones_gate
#print axioms blank_run_requires_ones_gate


/-- A single exponential estimate simultaneously encloses both sides of every even-a halting gateway. -/
theorem next_none_requires_pow_gap (a d : Nat)
    (he : a%2=0) (h : next (.D a d)=none) :
    3^(d-a-5) ≤ 2*(a+d)+5 ∧ 3^(a-d-5) ≤ 2*(a+d)+5 := by
  have hg := next_none_requires_ones_gate a d he h
  constructor
  · by_cases hd : a≤d
    · have ht := hg.2.1 hd
      have hp := twice_ones_add_one_eq_pow (d+1-a)
      have hle : d-a-5 ≤ d+1-a := by omega
      have hpow := Nat.pow_le_pow_right (by omega : 0<3) hle
      omega
    · have hzero : d-a-5=0 := by omega
      rw [hzero]
      simp
  · by_cases hd : a≤d
    · have hzero : a-d-5=0 := by omega
      rw [hzero]
      simp
    · by_cases hodd : d%2=1
      · have hr := hg.2.2.1 hodd
        rcases hr with hs | ht
        · have hz : a-d-5=0 := by omega
          rw [hz]
          simp
        · have hp := twice_ones_add_one_eq_pow (a-d-5)
          omega
      · have heven : d%2=0 := by omega
        have hr := hg.2.2.2 heven
        rcases hr with hs | ht
        · have hz : a-d-5=0 := by omega
          rw [hz]
          simp
        · have hp := twice_ones_add_one_eq_pow (a-d-2)
          have hex : a-d-5≤a-d-2 := by omega
          have hm := Nat.pow_le_pow_right (by omega : 0<3) hex
          omega

/-- Every hypothetically terminal blank-origin section satisfies the uniform power-gap bound. -/
theorem blank_run_requires_pow_gap (n a d : Nat)
    (hseen : run n = some (.D a d)) (hhalt : next (.D a d)=none) :
    3^(d-a-5) ≤ 2*(a+d)+5 ∧ 3^(a-d-5) ≤ 2*(a+d)+5 := by
  exact next_none_requires_pow_gap a d (run_preserves_even n a d hseen) hhalt

#print axioms next_none_requires_pow_gap
#print axioms blank_run_requires_pow_gap


/-- At mass scale 3^k, an even-a terminal step is within k+4 cells of the diagonal. -/
theorem next_none_requires_k_gap (a d k : Nat)
    (he : a%2=0) (h : next (.D a d)=none)
    (hscale : 2*(a+d)+5 < 3^k) :
    a < d+k+5 ∧ d < a+k+5 := by
  have hp := next_none_requires_pow_gap a d he h
  constructor
  · by_cases hc : a < d+k+5
    · exact hc
    · have hi : k ≤ a-d-5 := by omega
      have hm := Nat.pow_le_pow_right (by omega : 0<3) hi
      omega
  · by_cases hc : d < a+k+5
    · exact hc
    · have hi : k ≤ d-a-5 := by omega
      have hm := Nat.pow_le_pow_right (by omega : 0<3) hi
      omega

/-- Mass-scale width for genuine blank-origin terminal sections. -/
theorem blank_run_requires_k_gap (n a d k : Nat)
    (hseen : run n = some (.D a d)) (hhalt : next (.D a d)=none)
    (hscale : 2*(a+d)+5 < 3^k) :
    a < d+k+5 ∧ d < a+k+5 := by
  exact next_none_requires_k_gap a d k (run_preserves_even n a d hseen) hhalt hscale

#print axioms next_none_requires_k_gap
#print axioms blank_run_requires_k_gap


/-- Any first finite termination of the blank-section recursion has an actual surviving predecessor. -/
theorem run_none_has_predecessor (n : Nat) (h : run n=none) :
    ∃ m a d, run m=some (.D a d) ∧ next (.D a d)=none := by
  induction n with
  | zero => simp [run] at h
  | succ n ih =>
    cases hp : run n with
    | none => exact ih hp
    | some s =>
      rcases s with ⟨a,d⟩
      refine ⟨n,a,d,hp,?_⟩
      simpa only [run,hp,Option.bind_some] using h

/-- Any finite termination of the genuine section run has a predecessor in the proven ternary gate. -/
theorem run_none_implies_gate (n : Nat) (h : run n=none) :
    ∃ m a d, run m=some (.D a d) ∧ next (.D a d)=none ∧
      0<a ∧ (a≤d → ternaryOnes (d+1-a)≤a) ∧
      (d%2=1 → a<d+5 ∨ ternaryOnes (a-d-5)<d+3) ∧
      (d%2=0 → a<d+3 ∨ ternaryOnes (a-d-2)<d+2) := by
  obtain ⟨m,a,d,hseen,hhalt⟩ := run_none_has_predecessor n h
  refine ⟨m,a,d,hseen,hhalt,?_⟩
  exact blank_run_requires_ones_gate m a d hseen hhalt

#print axioms run_none_implies_gate

end BB6.Agent49ParitySource
