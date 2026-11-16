import Lean

namespace Agent10T0Parent

/-- A deliberately elementary quadratic lower bound for powers of two. -/
private theorem pow2_ge_four_sq (n : Nat) (hn : 10 ≤ n) :
    4 * n ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base =>
      norm_num
  | succ n hn ih =>
      have hnn : 10 * n ≤ n ^ 2 := by
        simpa [pow_two] using Nat.mul_le_mul_right n hn
      have hpoly : 4 * (n + 1) ^ 2 ≤ 8 * n ^ 2 := by
        nlinarith [hnn]
      calc
        4 * (n + 1) ^ 2 ≤ 8 * n ^ 2 := hpoly
        _ ≤ 2 ^ n * 2 := by nlinarith [ih]
        _ = 2 ^ (n + 1) := by simp [Nat.pow_succ, Nat.mul_comm]

/--
The two large-power inequalities needed by the t=0 entry contradiction
follow directly from the source-band lower bound and the entry-offset
factorization delta = 2^q * e.
-/
theorem t0_entry_even_parent_power_bounds
    (K q r e delta : Nat)
    (hK : 10 ≤ K)
    (hq : q ≤ K - 1)
    (he_pos : 0 < e)
    (he : delta = 2 ^ q * e)
    (hdelta_hi : delta ≤ 2 * K + 3)
    (hband_r :
      8 * 2 ^ K + (2 * K + 7) + 3 ≤ (2 * K + 7) * 2 ^ (r + 2)) :
    4 * K + 8 < 2 ^ (r + 3) ∧ 4 * K + 8 < 2 ^ (K - q + 2) := by
  have hpowK : 4 * K ^ 2 ≤ 2 ^ K := pow2_ge_four_sq K hK
  have hKK : 10 * K ≤ K ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul_right K hK
  have hRlower :
      16 * 2 ^ K + 2 * (2 * K + 7) + 6 ≤ (2 * K + 7) * 2 ^ (r + 3) := by
    calc
      16 * 2 ^ K + 2 * (2 * K + 7) + 6 =
          2 * (8 * 2 ^ K + (2 * K + 7) + 3) := by ring
      _ ≤ 2 * ((2 * K + 7) * 2 ^ (r + 2)) :=
        Nat.mul_le_mul_left 2 hband_r
      _ = (2 * K + 7) * 2 ^ (r + 3) := by
        rw [Nat.pow_succ]
        ring
  have hRstrict :
      (2 * K + 7) * (4 * K + 8) <
        16 * 2 ^ K + 2 * (2 * K + 7) + 6 := by
    nlinarith [hpowK, hK]
  have hpow_r : 4 * K + 8 < 2 ^ (r + 3) := by
    by_contra h
    have hle : 2 ^ (r + 3) ≤ 4 * K + 8 := by omega
    have hmul :
        (2 * K + 7) * 2 ^ (r + 3) ≤ (2 * K + 7) * (4 * K + 8) :=
      Nat.mul_le_mul_left (2 * K + 7) hle
    omega
  have hq_bound : 2 ^ q ≤ 2 * K + 3 := by
    have hle : 2 ^ q ≤ 2 ^ q * e :=
      Nat.le_mul_of_pos_right (2 ^ q) he_pos
    rw [← he] at hle
    omega
  have hpow12 : 4 * 2 ^ (K - q) = 2 ^ (K - q + 2) := by
    calc
      4 * 2 ^ (K - q) = 2 ^ 2 * 2 ^ (K - q) := by norm_num
      _ = 2 ^ (2 + (K - q)) := (Nat.pow_add 2 2 (K - q)).symm
      _ = 2 ^ (K - q + 2) := by congr 1 <;> omega
  have hpowC : 2 ^ q * 2 ^ (K - q) = 2 ^ K := by
    calc
      2 ^ q * 2 ^ (K - q) = 2 ^ (q + (K - q)) :=
        (Nat.pow_add 2 q (K - q)).symm
      _ = 2 ^ K := by congr 1 <;> omega
  have hpowKplus2 : 2 ^ (K + 2) = 4 * 2 ^ K := by
    calc
      2 ^ (K + 2) = 2 ^ K * 2 ^ 2 := Nat.pow_add 2 K 2
      _ = 4 * 2 ^ K := by norm_num [Nat.mul_comm]
  have hpowK2 : 2 ^ (K + 2) = 2 ^ q * 2 ^ (K - q + 2) := by
    calc
      2 ^ (K + 2) = 4 * 2 ^ K := hpowKplus2
      _ = 4 * (2 ^ q * 2 ^ (K - q)) := by rw [hpowC]
      _ = 2 ^ q * (4 * 2 ^ (K - q)) := by ring
      _ = 2 ^ q * 2 ^ (K - q + 2) := by rw [hpow12]
  have hpowK2low : 16 * K ^ 2 ≤ 2 ^ (K + 2) := by
    calc
      16 * K ^ 2 = 4 * (4 * K ^ 2) := by ring
      _ ≤ 4 * 2 ^ K := Nat.mul_le_mul_left 4 hpowK
      _ = 2 ^ (K + 2) := hpowKplus2.symm
  have hpoly : (2 * K + 3) * (4 * K + 8) < 16 * K ^ 2 := by
    nlinarith [hKK, hK]
  have hpow_kq : 4 * K + 8 < 2 ^ (K - q + 2) := by
    by_contra h
    have hle : 2 ^ (K - q + 2) ≤ 4 * K + 8 := by omega
    have hprod :
        2 ^ q * 2 ^ (K - q + 2) ≤ (2 * K + 3) * (4 * K + 8) :=
      Nat.mul_le_mul hq_bound hle
    have hupper : 2 ^ (K + 2) < 16 * K ^ 2 := by
      calc
        2 ^ (K + 2) = 2 ^ q * 2 ^ (K - q + 2) := hpowK2
        _ ≤ (2 * K + 3) * (4 * K + 8) := hprod
        _ < 16 * K ^ 2 := hpoly
    omega
  exact ⟨hpow_r, hpow_kq⟩

#print axioms t0_entry_even_parent_power_bounds

end Agent10T0Parent
