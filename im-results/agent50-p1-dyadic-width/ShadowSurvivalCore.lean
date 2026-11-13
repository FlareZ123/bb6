import Std

namespace BB6.Agent50Survival

def LegalDepth (C z t : Nat) : Prop :=
  2^t ∣ z ∧ (C + t + z / 2^t) % 2 = 1

theorem no_child_type0_iff (z : Nat) :
    (∀ t, ¬ LegalDepth 0 z t) ↔ z % 4 = 2 := by
  constructor
  · intro h
    by_cases hzOdd : z % 2 = 1
    · have hdiv : 2^0 ∣ z := by simp
      have hpar : (0 + 0 + z / 2^0) % 2 = 1 := by simpa using hzOdd
      have hleg : LegalDepth 0 z 0 := ⟨hdiv, hpar⟩
      exact False.elim (h 0 hleg)
    · have hzEven : z % 2 = 0 := by omega
      have hmod : z % 4 = 0 ∨ z % 4 = 2 := by omega
      rcases hmod with hz4 | hz4
      · have hdiv : 2 ∣ z := Nat.dvd_of_mod_eq_zero hzEven
        have hpar : (1 + z / 2) % 2 = 1 := by omega
        have hleg : LegalDepth 0 z 1 := by
          change 2^1 ∣ z ∧ (0 + 1 + z / 2^1) % 2 = 1
          exact ⟨by simpa using hdiv, by simpa using hpar⟩
        exact False.elim (h 1 hleg)
      · exact hz4
  · intro hz4 t hleg
    change 2^t ∣ z ∧ (0 + t + z / 2^t) % 2 = 1 at hleg
    rcases hleg with ⟨hdiv, hpar⟩
    cases t with
    | zero =>
        have hodd : z % 2 = 1 := by simpa using hpar
        omega
    | succ t =>
        cases t with
        | zero =>
            change (1 + z / 2) % 2 = 1 at hpar
            omega
        | succ t =>
            have hpow : 2^2 ∣ 2^(t+2) := Nat.pow_dvd_pow 2 (by omega)
            have hpow' : 4 ∣ 2^(t+2) := by simpa using hpow
            have hfour : 4 ∣ z := Nat.dvd_trans hpow' hdiv
            have hzero : z % 4 = 0 := Nat.dvd_iff_mod_eq_zero.mp hfour
            omega

theorem no_child_type1_iff (z : Nat) :
    (∀ t, ¬ LegalDepth 1 z t) ↔ z % 2 = 1 := by
  constructor
  · intro h
    by_cases hzOdd : z % 2 = 1
    · exact hzOdd
    · have hzEven : z % 2 = 0 := by omega
      have hdiv : 2^0 ∣ z := by simp
      have hpar : (1 + z) % 2 = 1 := by omega
      have hleg : LegalDepth 1 z 0 := by
        change 2^0 ∣ z ∧ (1 + 0 + z / 2^0) % 2 = 1
        exact ⟨hdiv, by simpa using hpar⟩
      exact False.elim (h 0 hleg)
  · intro hzOdd t hleg
    change 2^t ∣ z ∧ (1 + t + z / 2^t) % 2 = 1 at hleg
    rcases hleg with ⟨hdiv, hpar⟩
    cases t with
    | zero =>
        have hpar' : (1 + z) % 2 = 1 := by simpa using hpar
        omega
    | succ t =>
        have hpow : 2 ∣ 2^(t+1) := by
          have h := Nat.pow_dvd_pow 2 (by omega : 1 ≤ t+1)
          simpa using h
        have hdiv2 : 2 ∣ z := Nat.dvd_trans hpow hdiv
        have hzEven : z % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdiv2
        omega

def inv4 (b : Nat) : Nat := if b % 4 = 1 then 1 else 3

def badResidue4 (a b : Nat) : Nat :=
  ((6 - a % 4) * inv4 b) % 4

theorem odd_slope_bad_residue_mod4 (a b r : Nat) (hb : b % 2 = 1) :
    (a + b*r) % 4 = 2 ↔ r % 4 = badResidue4 a b := by
  have hb4 : b % 4 = 1 ∨ b % 4 = 3 := by omega
  have hred : (a + b*r) % 4 = ((a % 4) + (b % 4)*(r % 4)) % 4 := by
    simp [Nat.add_mod, Nat.mul_mod]
  rcases hb4 with hb1 | hb3
  · rw [hred, hb1]
    simp [badResidue4, inv4, hb1]
    omega
  · rw [hred, hb3]
    simp [badResidue4, inv4, hb3]
    omega

def badResidue2 (a : Nat) : Nat := 1 - a % 2

theorem odd_slope_bad_residue_mod2 (a b r : Nat) (hb : b % 2 = 1) :
    (a + b*r) % 2 = 1 ↔ r % 2 = badResidue2 a := by
  have hred : (a + b*r) % 2 = ((a % 2) + (b % 2)*(r % 2)) % 2 := by
    simp [Nat.add_mod, Nat.mul_mod]
  rw [hred, hb]
  simp [badResidue2]
  omega

#print axioms no_child_type0_iff
#print axioms no_child_type1_iff
#print axioms odd_slope_bad_residue_mod4
#print axioms odd_slope_bad_residue_mod2

end BB6.Agent50Survival
