import Lean
import Lean.Elab.Tactic.Omega

namespace BB6.Agent4MassBounds

/-- Raw weighted mass of the low stopping target. -/
def lowRawMass (m : Nat) : Nat :=
  1 + 2 * (2^(2*m+3) - (3*m+4))

/-- Raw weighted mass of the high stopping target. -/
def highRawMass (j m : Nat) : Nat :=
  (2*j+3) + 2 * (2^(2*m+2)*(j+3) - (j+3*m+5))

theorem low_score (m : Nat) : 3*m+4 ≤ 2^(2*m+3) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have hp : 2^(2*(m+1)+3) = 4 * 2^(2*m+3) := by
        rw [show 2*(m+1)+3 = (2*m+3)+2 by omega, Nat.pow_add]
        simp [Nat.mul_comm]
      rw [hp]
      omega

theorem power_linear_bound (m : Nat) : 4*m+4 ≤ 2^(2*m+2) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have hp : 2^(2*(m+1)+2) = 4 * 2^(2*m+2) := by
        rw [show 2*(m+1)+2 = (2*m+2)+2 by omega, Nat.pow_add]
        simp [Nat.mul_comm]
      rw [hp]
      omega

theorem high_score (j m : Nat) : j+3*m+5 ≤ 2^(2*m+2)*(j+3) := by
  have hN : 4*m+4 ≤ 2^(2*m+2) := power_linear_bound m
  have hNpos : 1 ≤ 2^(2*m+2) := by omega
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hNpos
  have h3 : 3*m+5 ≤ 3*2^(2*m+2) := by omega
  rw [Nat.mul_add]
  omega

/-- Closed form for the low target mass, with Nat subtraction justified. -/
theorem lowRawMass_eq (m : Nat) :
    lowRawMass m = 2^(2*m+4) - (6*m+7) := by
  have hs := low_score m
  have hp : 2^(2*m+4) = 2 * 2^(2*m+3) := by
    calc
      2^(2*m+4) = 2^(2*m+3) * 2 := by rw [show 2*m+4 = (2*m+3)+1 by omega, Nat.pow_succ]
      _ = 2 * 2^(2*m+3) := by omega
  unfold lowRawMass
  rw [hp]
  omega

/-- Closed form for the high target mass, with Nat subtraction justified. -/
theorem highRawMass_eq (j m : Nat) :
    highRawMass j m = 2^(2*m+3)*(j+3) - (6*m+7) := by
  let N := 2^(2*m+2)
  have hs : j+3*m+5 ≤ N*(j+3) := by
    simpa [N] using high_score j m
  have hp : 2^(2*m+3) = 2*N := by
    dsimp [N]
    calc
      2^(2*m+3) = 2^(2*m+2) * 2 := by rw [show 2*m+3 = (2*m+2)+1 by omega, Nat.pow_succ]
      _ = 2 * 2^(2*m+2) := by simp [Nat.mul_comm]
  have hprod : N*(j+3) = N*j + 3*N := by
    rw [Nat.mul_add]
    simp [Nat.mul_comm]
  have hsub : (N*j+3*N) - (j+3*m+5) + (j+3*m+5) = N*j+3*N := by
    rw [← hprod]
    exact Nat.sub_add_cancel hs
  have hdouble : (2*N)*(j+3) = 2*(N*(j+3)) := by ac_rfl
  unfold highRawMass
  rw [hp, hdouble, hprod]
  omega

/-- For m≥4, the low target already has raw mass at least 4065. -/
theorem pow_linear_from_four (m : Nat) (hm : 4 ≤ m) :
    4096 + 6*(m-4) ≤ 2^(m+8) := by
  have hforall : ∀ n : Nat, 4096 + 6*n ≤ 2^(n+12) := by
    intro n
    induction n with
    | zero => decide
    | succ n ih =>
        have hp : 2^(n+1+12) = 2 * 2^(n+12) := by
          rw [show n+1+12 = (n+12)+1 by omega, Nat.pow_succ]
          exact Nat.mul_comm _ _
        rw [hp]
        omega
  have h := hforall (m-4)
  have he : (m-4)+12 = m+8 := by omega
  rw [he] at h
  exact h

theorem high_pow_linear_from_four (m : Nat) (hm : 4 ≤ m) :
    2048 + 6*(m-4) ≤ 2^(m+7) := by
  have hforall : ∀ n : Nat, 2048 + 6*n ≤ 2^(n+11) := by
    intro n
    induction n with
    | zero => decide
    | succ n ih =>
        have hp : 2^(n+1+11) = 2 * 2^(n+11) := by
          rw [show n+1+11 = (n+11)+1 by omega, Nat.pow_succ]
          exact Nat.mul_comm _ _
        rw [hp]
        omega
  have h := hforall (m-4)
  have he : (m-4)+11 = m+7 := by omega
  rw [he] at h
  exact h

theorem low_mass_ge_4065 (m : Nat) (hm : 4 ≤ m) :
    4065 ≤ lowRawMass m := by
  rw [lowRawMass_eq]
  have hp := pow_linear_from_four m hm
  have hexp : m+8 ≤ 2*m+4 := by omega
  have hpow : 2^(m+8) ≤ 2^(2*m+4) := Nat.pow_le_pow_right (by decide) hexp
  omega

theorem high_mass_ge_6113 (j m : Nat) (hm : 4 ≤ m) :
    6113 ≤ highRawMass j m := by
  rw [highRawMass_eq]
  have hp := high_pow_linear_from_four m hm
  have hexp : m+7 ≤ 2*m+3 := by omega
  have hpow : 2^(m+7) ≤ 2^(2*m+3) := Nat.pow_le_pow_right (by decide) hexp
  have hmul := Nat.mul_le_mul_left 3 (Nat.le_trans hp hpow)
  have hj3 : 3 ≤ j+3 := by omega
  have hprod : 3*2^(2*m+3) ≤ 2^(2*m+3)*(j+3) := by
    calc
      3*2^(2*m+3) ≤ (j+3)*2^(2*m+3) := Nat.mul_le_mul_right _ hj3
      _ = 2^(2*m+3)*(j+3) := Nat.mul_comm _ _
  omega

/-- Thus every low target with raw mass≤2000 has m≤3. -/
theorem low_raw_mass_box (m : Nat) (h : lowRawMass m ≤ 2000) : m ≤ 3 := by
  by_cases hm : 4 ≤ m
  · have hbig := low_mass_ge_4065 m hm
    omega
  · omega

/-- Every high target with raw mass≤2000 lies in the finite box
    m≤3, j≤250. This is the exact parameter-domain bound for the probe. -/
theorem high_raw_mass_box (j m : Nat) (h : highRawMass j m ≤ 2000) :
    m ≤ 3 ∧ j ≤ 250 := by
  by_cases hm : 4 ≤ m
  · have hbig := high_mass_ge_6113 j m hm
    omega
  · have hm3 : m ≤ 3 := by omega
    rw [highRawMass_eq] at h
    have hpow : 8 ≤ 2^(2*m+3) := by
      have hexp : 3 ≤ 2*m+3 := by omega
      calc
        8 = 2^3 := by decide
        _ ≤ 2^(2*m+3) := Nat.pow_le_pow_right (by decide) hexp
    have hmul := Nat.mul_le_mul_right (j+3) hpow
    have hlin : 6*m+7 ≤ 25 := by omega
    constructor
    · exact hm3
    · omega


theorem high_raw_mass_m0 (j : Nat) : highRawMass j 0 = 8*j+17 := by
  rw [highRawMass_eq]
  omega

theorem high_raw_mass_m1 (j : Nat) : highRawMass j 1 = 32*j+83 := by
  rw [highRawMass_eq]
  omega

theorem high_raw_mass_m2 (j : Nat) : highRawMass j 2 = 128*j+365 := by
  rw [highRawMass_eq]
  omega

theorem high_raw_mass_m3 (j : Nat) : highRawMass j 3 = 512*j+1511 := by
  rw [highRawMass_eq]
  omega

/-- Exact per-row finite parameter bounds for the raw-mass-2000 high box. -/
theorem high_raw_mass_box_exact (j m : Nat) (h : highRawMass j m ≤ 2000) :
    (m=0 ∧ j≤247) ∨ (m=1 ∧ j≤59) ∨
    (m=2 ∧ j≤12) ∨ (m=3 ∧ j=0) := by
  have hm3 : m≤3 := (high_raw_mass_box j m h).1
  have hmCases : m=0 ∨ m=1 ∨ m=2 ∨ m=3 := by omega
  rcases hmCases with rfl | rfl | rfl | rfl
  · rw [high_raw_mass_m0] at h
    exact Or.inl ⟨rfl, by omega⟩
  · rw [high_raw_mass_m1] at h
    exact Or.inr (Or.inl ⟨rfl, by omega⟩)
  · rw [high_raw_mass_m2] at h
    exact Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩))
  · rw [high_raw_mass_m3] at h
    have hj : j=0 := by omega
    exact Or.inr (Or.inr (Or.inr ⟨rfl,hj⟩))

theorem low_raw_mass_m0 : lowRawMass 0 = 9 := by rw [lowRawMass_eq]
theorem low_raw_mass_m1 : lowRawMass 1 = 51 := by rw [lowRawMass_eq]
theorem low_raw_mass_m2 : lowRawMass 2 = 237 := by rw [lowRawMass_eq]
theorem low_raw_mass_m3 : lowRawMass 3 = 999 := by rw [lowRawMass_eq]

theorem low_raw_mass_box_exact (m : Nat) (h : lowRawMass m ≤ 2000) :
    m=0 ∨ m=1 ∨ m=2 ∨ m=3 := by
  have hm := low_raw_mass_box m h
  omega

#print axioms lowRawMass_eq
#print axioms highRawMass_eq
#print axioms low_mass_ge_4065
#print axioms high_mass_ge_6113
#print axioms low_raw_mass_box
#print axioms high_raw_mass_box
#print axioms high_raw_mass_box_exact
#print axioms high_raw_mass_m0
#print axioms high_raw_mass_m1
#print axioms high_raw_mass_m2
#print axioms high_raw_mass_m3
#print axioms low_raw_mass_box_exact

end BB6.Agent4MassBounds
