import Agent8DigitChargeSource

/-!
A source-connected global quadratic Lyapunov inequality for the accelerated
blank-root section map of the original Cryptids #623 machine.

No transition rule is copied: evalA, drainB, and highLevelNext are imported
from the pinned original machine. The drain bounds below are proved for every
successful drain, including the zero-first-counter residue exceptions.
-/

namespace BB6.Agent22GlobalQuadraticSource

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent8DigitChargeSource

def quadraticNorm (a d : Nat) : Nat := a*a + a*d + d*d

/-- A uniform weighted lower bound for every successful original evalA.
The additive 2 is sharp at the zero-first-counter residue-2 exception. -/
theorem evalA_weighted_lower (a : Nat) :
    ∀ k m aa bb dd : Nat, evalA a k m = some (aa, bb, dd) →
      2*a + k + m ≤ 2*aa + 3*bb + dd + 2 := by
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
          have hi := ih (k / 3) (m + 2 * (k / 3) + 3) aa bb dd h
          omega

/-- The same evaluator always leaves at least m+k-2 in its third-plus-three
second-coordinate potential. -/
theorem evalA_third_lower (a : Nat) :
    ∀ k m aa bb dd : Nat, evalA a k m = some (aa, bb, dd) →
      m + k - 2 ≤ dd + 3*bb := by
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
          have hi := ih (k / 3) (m + 2 * (k / 3) + 3) aa bb dd h
          omega

/-- Every successful B-drain has a source-level weighted lower bound. -/
theorem drainB_weighted_lower (b : Nat) :
    ∀ a d aa dd : Nat, drainB a b d = some (.D aa dd) →
      2*a + d + 3*b ≤ 2*aa + dd := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
      intro a d aa dd h
      rw [drainB] at h
      by_cases hb : b = 0
      · simp [hb] at h
        cases h
        omega
      · simp only [if_neg hb] at h
        cases he : evalA a (b - 1) (d + 2*b + 3) with
        | none => simp [he] at h
        | some p =>
            rcases p with ⟨a1, b1, d1⟩
            simp only [he, Option.bind_some] at h
            by_cases hlt : b1 < b
            · simp only [if_pos hlt] at h
              have hm := evalA_weighted_lower a (b - 1) (d + 2*b + 3) a1 b1 d1 he
              have hr := ih b1 hlt a1 d1 aa dd h
              omega
            · simp [hlt] at h

/-- Every completed drain contributes at least its exact 3*b block mass
to the third counter. -/
theorem drainB_third_lower (a b d aa dd : Nat)
    (h : drainB a b d = some (.D aa dd)) :
    d + 3*b ≤ dd := by
  obtain ⟨c, hcode, hdd⟩ := drainB_charge_witness a b d aa dd h
  omega

theorem drainB_bounds (a b d aa dd : Nat)
    (h : drainB a b d = some (.D aa dd)) :
    2*a + d + 3*b ≤ 2*aa + dd ∧ d + 3*b ≤ dd :=
  ⟨drainB_weighted_lower b a d aa dd h,
   drainB_third_lower a b d aa dd h⟩

/-- The Eisenstein norm identity turns two independent output bounds into
a lower bound for the quadratic norm. -/
theorem quadratic_from_bounds (A D S D0 : Nat)
    (hS : S ≤ 2*A + D) (hD : D0 ≤ D) :
    S^2 + 3*D0^2 ≤ 4*quadraticNorm A D := by
  have hSsq : S^2 ≤ (2*A + D)^2 := by
    nlinarith
  have hDsq : D0^2 ≤ D^2 := by
    nlinarith
  calc
    S^2 + 3*D0^2 ≤ (2*A + D)^2 + 3*D^2 := by omega
    _ = 4*quadraticNorm A D := by
      unfold quadraticNorm
      ring

lemma q_left_odd (a d : Nat) :
    4*(quadraticNorm a d + 49) ≤
      (2*a+d+4)^2 + 3*(3*d+14)^2 := by
  unfold quadraticNorm
  nlinarith

lemma q_left_even (a d : Nat) :
    4*(quadraticNorm a d + 49) ≤
      (2*a+d+4)^2 + 3*(3*d+8)^2 := by
  unfold quadraticNorm
  nlinarith

lemma q_right_odd (a d : Nat) (ha : 2 ≤ a) (hd : 1 ≤ d) :
    4*(quadraticNorm a d + 49) ≤
      (2*d+a+8)^2 + 3*(3*a)^2 := by
  unfold quadraticNorm
  nlinarith

lemma q_right_even (a d : Nat) (ha : 2 ≤ a) (had : a ≤ d) :
    4*(quadraticNorm a d + 49) ≤
      (2*d+a+5)^2 + 3*(3*a+3)^2 := by
  unfold quadraticNorm
  nlinarith

lemma q_diagonal (a : Nat) (ha : 2 ≤ a) :
    4*(quadraticNorm a (a-2) + 49) ≤
      (3*a+2)^2 + 3*(3*a+2)^2 := by
  unfold quadraticNorm
  have hdecomp : a = (a-2)+2 := by omega
  rw [hdecomp]
  nlinarith

lemma q_zero_odd (d : Nat) (hd : 1 ≤ d) :
    4*(quadraticNorm 0 d + 49) ≤
      (2*d+10)^2 + 3*8^2 := by
  unfold quadraticNorm
  nlinarith

/-- Every successful transition from an even-first-counter section state
strictly increases the exact quadratic norm a^2+a*d+d^2 by at least 49.

This is global: it does not assume membership in the previously used
canonical-ray cone or a ternary-ones budget. -/
theorem highLevel_quadratic_growth (a d aa dd : Nat)
    (ha : a % 2 = 0)
    (hstep : highLevelNext (.D a d) = some (.D aa dd)) :
    quadraticNorm a d + 49 ≤ quadraticNorm aa dd := by
  simp only [highLevelNext] at hstep
  by_cases h0 : a = 0
  · simp only [if_pos h0] at hstep
    by_cases hd : d % 2 = 1
    · simp only [if_pos hd] at hstep
      have hb := drainB_bounds (d+1) 2 2 aa dd hstep
      have hS : 2*d+10 ≤ 2*aa+dd := by
        have := hb.1
        omega
      have hD : 8 ≤ dd := by
        have := hb.2
        omega
      have hq := quadratic_from_bounds aa dd (2*d+10) 8 hS hD
      have harith : 4*(quadraticNorm 0 d + 49) ≤ (2*d+10)^2 + 3*8^2 :=
        q_zero_odd d (by omega)
      have hfinal : 4*(quadraticNorm 0 d + 49) ≤ 4*quadraticNorm aa dd :=
        le_trans harith hq
      nlinarith
    · simp only [if_neg hd] at hstep
      injection hstep with hs
      injection hs with haa hdd
      subst aa
      subst dd
      unfold quadraticNorm
      omega
  · simp only [if_neg h0] at hstep
    by_cases h1 : d % 2 = 1 ∧ a ≥ d+5
    · simp only [if_pos h1] at hstep
      have hb := drainB_bounds (a-d-5) (d+3) 5 aa dd hstep
      have hS : 2*a+d+4 ≤ 2*aa+dd := by
        have := hb.1
        omega
      have hD : 3*d+14 ≤ dd := by
        have := hb.2
        omega
      have hq := quadratic_from_bounds aa dd (2*a+d+4) (3*d+14) hS hD
      have harith : 4*(quadraticNorm a d + 49) ≤
          (2*a+d+4)^2 + 3*(3*d+14)^2 := q_left_odd a d
      have hfinal : 4*(quadraticNorm a d + 49) ≤ 4*quadraticNorm aa dd :=
        le_trans harith hq
      nlinarith
    · simp only [if_neg h1] at hstep
      by_cases h2 : d % 2 = 0 ∧ a ≥ d+3
      · simp only [if_pos h2] at hstep
        have hb := drainB_bounds (a-d-2) (d+2) 2 aa dd hstep
        have hS : 2*a+d+4 ≤ 2*aa+dd := by
          have := hb.1
          omega
        have hD : 3*d+8 ≤ dd := by
          have := hb.2
          omega
        have hq := quadratic_from_bounds aa dd (2*a+d+4) (3*d+8) hS hD
        have harith : 4*(quadraticNorm a d + 49) ≤
            (2*a+d+4)^2 + 3*(3*d+8)^2 := q_left_even a d
        have hfinal : 4*(quadraticNorm a d + 49) ≤ 4*quadraticNorm aa dd :=
          le_trans harith hq
        nlinarith
      · simp only [if_neg h2] at hstep
        have haOdd : a % 2 ≠ 1 := by omega
        simp only [if_neg haOdd] at hstep
        by_cases h3 : a = d+2
        · simp only [if_pos h3] at hstep
          have hb := drainB_bounds 0 a 2 aa dd hstep
          have hS : 3*a+2 ≤ 2*aa+dd := by
            have := hb.1
            omega
          have hD : 3*a+2 ≤ dd := by
            have := hb.2
            omega
          have hq := quadratic_from_bounds aa dd (3*a+2) (3*a+2) hS hD
          have ha2 : 2 ≤ a := by omega
          have harith : 4*(quadraticNorm a (a-2) + 49) ≤
              (3*a+2)^2 + 3*(3*a+2)^2 := q_diagonal a ha2
          have hfinal : 4*(quadraticNorm a (a-2) + 49) ≤ 4*quadraticNorm aa dd :=
            le_trans harith hq
          nlinarith
        · simp only [if_neg h3] at hstep
          by_cases hd : d % 2 = 1
          · simp only [if_pos hd] at hstep
            have hxa : d+4-a ≥ 0 := by omega
            have hb := drainB_bounds (d+4-a) (a-1) 3 aa dd hstep
            have hS : 2*d+a+8 ≤ 2*aa+dd := by
              have := hb.1
              omega
            have hD : 3*a ≤ dd := by
              have := hb.2
              omega
            have hq := quadratic_from_bounds aa dd (2*d+a+8) (3*a) hS hD
            have ha2 : 2 ≤ a := by omega
            have hd1 : 1 ≤ d := by omega
            have harith : 4*(quadraticNorm a d + 49) ≤
                (2*d+a+8)^2 + 3*(3*a)^2 := q_right_odd a d ha2 hd1
            have hfinal : 4*(quadraticNorm a d + 49) ≤ 4*quadraticNorm aa dd :=
              le_trans harith hq
            nlinarith
          · simp only [if_neg hd] at hstep
            have hdEven : d % 2 = 0 := by omega
            have hnotfar : ¬(d % 2 = 0 ∧ a ≥ d+3) := h2
            have haLt : a < d+3 := by
              by_contra hn
              exact hnotfar ⟨hdEven, by omega⟩
            have had : a ≤ d := by omega
            have ha2 : 2 ≤ a := by omega
            have harg : 0 < d+1-a := by omega
            cases he : evalA (d+1-a) a (2*a+5) with
            | none => simp [he] at hstep
            | some p =>
                rcases p with ⟨x, b, m⟩
                simp only [he, Option.bind_some] at hstep
                have hew := evalA_weighted_lower (d+1-a) a (2*a+5) x b m he
                have het := evalA_third_lower (d+1-a) a (2*a+5) x b m he
                have hb := drainB_bounds x b m aa dd hstep
                have hS : 2*d+a+5 ≤ 2*aa+dd := by
                  have := hb.1
                  omega
                have hD : 3*a+3 ≤ dd := by
                  have := hb.2
                  omega
                have hq := quadratic_from_bounds aa dd (2*d+a+5) (3*a+3) hS hD
                have harith : 4*(quadraticNorm a d + 49) ≤
                    (2*d+a+5)^2 + 3*(3*a+3)^2 := q_right_even a d ha2 had
                have hfinal : 4*(quadraticNorm a d + 49) ≤ 4*quadraticNorm aa dd :=
                  le_trans harith hq
                nlinarith

#print axioms evalA_weighted_lower
#print axioms evalA_third_lower
#print axioms drainB_weighted_lower
#print axioms drainB_third_lower
#print axioms highLevel_quadratic_growth

end BB6.Agent22GlobalQuadraticSource
