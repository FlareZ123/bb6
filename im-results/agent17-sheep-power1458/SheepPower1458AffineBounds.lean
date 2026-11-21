import GenericHighNoParent
import SheepPower1458Core

namespace SheepPower1458

/-- Package the existing signed-power gap for an arbitrary affine node. -/
theorem no_generic_high_affine (D E A a n v : Nat)
    (hA : 2 ≤ A)
    (hbase : 1 < SheepGenericHigh.Q D E A ∧
      SheepGenericHigh.Q D E A % 2 = 1 ∧
      SheepGenericHigh.Q D E A < 2^A ∧ 2*D ≤ 2^A)
    (ha : A ≤ a)
    (heq : D*(2^(a+1)+1)*v + 2*a*D + E = 2^n + 3*D) : False := by
  have hgap := SheepGenericHigh.large_odd_gap D E A hA hbase a ha
  exact SheepGenericHigh.no_large_generic_equation D E a n v (by omega) hgap heq

/-- A uniform exceptional-source obstruction for the bounded affine-node
coefficients in the five 1458-stratum inverse trees. -/
theorem no_special_affine (D S a N : Nat)
    (hDpos : 0 < D) (hD : D ≤ 4_000_000) (hS : S ≤ 4_000_000)
    (hN : 55 ≤ N)
    (heq : 3*D*2^a + D*(a+2) + S = 2^N) : False := by
  by_cases ha : a ≤ 31
  · have hpow : 2^a ≤ 2^31 :=
      Nat.pow_le_pow_right (by decide) ha
    have h3D : 3*D ≤ 12_000_000 := by omega
    have hterm1 : 3*D*2^a ≤ 12_000_000*2^31 := by
      calc
        3*D*2^a ≤ 12_000_000*2^a :=
          Nat.mul_le_mul_right (2^a) h3D
        _ ≤ 12_000_000*2^31 :=
          Nat.mul_le_mul_left 12_000_000 hpow
    have ha2 : a+2 ≤ 33 := by omega
    have hterm2 : D*(a+2) ≤ 4_000_000*33 := by
      calc
        D*(a+2) ≤ 4_000_000*(a+2) :=
          Nat.mul_le_mul_right (a+2) hD
        _ ≤ 4_000_000*33 :=
          Nat.mul_le_mul_left 4_000_000 ha2
    have hbound :
        3*D*2^a + D*(a+2) + S ≤
          12_000_000*2^31 + 4_000_000*33 + 4_000_000 := by
      exact Nat.add_le_add (Nat.add_le_add hterm1 hterm2) hS
    have hsmall :
        12_000_000*2^31 + 4_000_000*33 + 4_000_000 < 2^55 := by
      decide
    have hleft : 3*D*2^a + D*(a+2) + S < 2^55 :=
      Nat.lt_of_le_of_lt hbound hsmall
    have hpowN : 2^55 ≤ 2^N :=
      Nat.pow_le_pow_right (by decide) hN
    omega
  · have ha32 : 32 ≤ a := by omega
    have hlinear : 0 < D*(a+2)+S ∧ D*(a+2)+S < 2^a := by
      have hseq : ∀ k : Nat, 4_000_000*(k+35) < 2^(k+32) := by
        intro k
        induction k with
        | zero => decide
        | succ k ih =>
          have hpow : 2^(k+1+32) = 2*2^(k+32) := by
            calc
              2^(k+1+32) = 2^((k+32)+1) := by congr 1 <;> omega
              _ = 2^(k+32)*2 := by rw [Nat.pow_succ]
              _ = 2*2^(k+32) := by omega
          have hlin :
              4_000_000*(k+1+35) =
                4_000_000*(k+35)+4_000_000 := by omega
          have hpositive : 4_000_000 ≤ 4_000_000*(k+35) := by
            omega
          rw [hlin, hpow]
          omega
      have hk := hseq (a-32)
      have h1 : (a-32)+32 = a := by omega
      have h2 : (a-32)+35 = a+3 := by omega
      have hpow : 4_000_000*(a+3) < 2^a := by
        simpa [h1, h2] using hk
      have hbound : D*(a+2)+S ≤ 4_000_000*(a+3) := by
        have hterm :
            D*(a+2) ≤ 4_000_000*(a+2) := by
          exact Nat.mul_le_mul_right (a+2) hD
        calc
          D*(a+2)+S ≤ 4_000_000*(a+2)+4_000_000 :=
            Nat.add_le_add hterm hS
          _ = 4_000_000*(a+3) := by omega
      have hpos : 0 < D*(a+2)+S := by
        have hmul : 0 < D*(a+2) :=
          Nat.mul_pos hDpos (by omega)
        omega
      exact ⟨hpos, Nat.lt_of_le_of_lt hbound hpow⟩
    by_cases han : a ≤ N
    · have hpowdiv : 2^a ∣ 2^N := by
        refine ⟨2^(N-a), ?_⟩
        calc
          2^N = 2^(a+(N-a)) := by congr 1; omega
          _ = 2^a * 2^(N-a) := by rw [Nat.pow_add]
      have hpowmod : 2^N % 2^a = 0 :=
        Nat.mod_eq_zero_of_dvd hpowdiv
      have hmuldiv : 2^a ∣ 3*D*2^a := by
        refine ⟨3*D, ?_⟩
        ac_rfl
      have hmulmod : (3*D*2^a) % 2^a = 0 :=
        Nat.mod_eq_zero_of_dvd hmuldiv
      have hsum :
          (3*D*2^a + (D*(a+2)+S)) % 2^a = 0 := by
        rw [← Nat.add_assoc, heq]
        exact hpowmod
      have hLmod : (D*(a+2)+S) % 2^a = 0 := by
        rw [Nat.add_mod, hmulmod] at hsum
        simpa [Nat.mod_mod] using hsum
      have hLzero : D*(a+2)+S = 0 := by
        rw [Nat.mod_eq_of_lt hlinear.2] at hLmod
        exact hLmod
      omega
    · have hNa : N < a := by omega
      have hpow : 2^(N+1) ≤ 2^a :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have hmain : 2^N < 3*D*2^a := by
        have h3D : 3 ≤ 3*D := by omega
        calc
          2^N < 3*2^(N+1) := by
            have hpowpos : 0 < 2^N := Nat.pow_pos (by decide)
            rw [Nat.pow_succ]
            omega
          _ ≤ 3*2^a := Nat.mul_le_mul_left 3 hpow
          _ ≤ 3*D*2^a := Nat.mul_le_mul_right (2^a) h3D
      omega

#print axioms no_generic_high_affine
#print axioms no_special_affine

end SheepPower1458
