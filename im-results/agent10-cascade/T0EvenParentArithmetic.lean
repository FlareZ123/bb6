import Lean

namespace Agent10T0Parent

/-- Equal residues modulo m and distance strictly below m force equality. -/
private theorem nat_eq_of_mod_eq_of_close
    (a b m : Nat) (hm : 0 < m)
    (hmod : a % m = b % m)
    (hab : a < b + m) (hba : b < a + m) : a = b := by
  omega

/--
Arithmetic core of the t=0 adjacent-fatal even-entry exclusion.

Here q is the number of same-level even resets from the level-K entry,
delta is the entry deficit offset in the even-parent band, and r is the
fatal even-tail depth. The hypotheses are exactly the source-band bounds
and the equation obtained by substituting the t=0 fatal equation into the
entry-deficit identity.
-/
theorem t0_entry_even_parent_arithmetic_no_solution
    (K q r delta : Nat)
    (hK : 266 ≤ K)
    (hq : q ≤ K - 1)
    (hdelta_lo : K + 3 ≤ delta)
    (hdelta_hi : delta ≤ 2 * K + 3)
    (hpow_r : 4 * K + 8 < 2 ^ (r + 3))
    (hpow_kq : 4 * K + 8 < 2 ^ (K - q + 2))
    (heq :
      (2 * K + 7) * 2 ^ (q + r + 3) + 2 ^ q * (2 * K + 1) =
        2 ^ (K + q + 4) + 12 * 2 ^ K + 3 * delta) : False := by
  have hqK : q ≤ K := by omega
  have hpowA : 2 ^ q * 2 ^ (r + 3) = 2 ^ (q + r + 3) := by
    calc
      2 ^ q * 2 ^ (r + 3) = 2 ^ (q + (r + 3)) :=
        (Nat.pow_add 2 q (r + 3)).symm
      _ = 2 ^ (q + r + 3) := by congr 1 <;> omega
  have hpowB : 2 ^ q * 2 ^ (K + 4) = 2 ^ (K + q + 4) := by
    calc
      2 ^ q * 2 ^ (K + 4) = 2 ^ (q + (K + 4)) :=
        (Nat.pow_add 2 q (K + 4)).symm
      _ = 2 ^ (K + q + 4) := by congr 1 <;> omega
  have hpowC : 2 ^ q * 2 ^ (K - q) = 2 ^ K := by
    calc
      2 ^ q * 2 ^ (K - q) = 2 ^ (q + (K - q)) :=
        (Nat.pow_add 2 q (K - q)).symm
      _ = 2 ^ K := by congr 1 <;> omega
  have hfact :
      2 ^ q * ((2 * K + 7) * 2 ^ (r + 3) + (2 * K + 1)) =
        2 ^ q * (2 ^ (K + 4) + 12 * 2 ^ (K - q)) + 3 * delta := by
    calc
      _ = (2 * K + 7) * (2 ^ q * 2 ^ (r + 3)) + 2 ^ q * (2 * K + 1) := by ring
      _ = (2 * K + 7) * 2 ^ (q + r + 3) + 2 ^ q * (2 * K + 1) := by rw [hpowA]
      _ = 2 ^ (K + q + 4) + 12 * 2 ^ K + 3 * delta := heq
      _ = 2 ^ q * (2 ^ (K + 4) + 12 * 2 ^ (K - q)) + 3 * delta := by
        rw [← hpowB, ← hpowC]
        ring
  have hdivsum :
      2 ^ q ∣ 2 ^ q * (2 ^ (K + 4) + 12 * 2 ^ (K - q)) + 3 * delta := by
    rw [← hfact]
    exact ⟨(2 * K + 7) * 2 ^ (r + 3) + (2 * K + 1), rfl⟩
  have hdivshift : 2 ^ q ∣ 2 ^ q * (2 ^ (K + 4) + 12 * 2 ^ (K - q)) :=
    ⟨2 ^ (K + 4) + 12 * 2 ^ (K - q), rfl⟩
  have hdiv : 2 ^ q ∣ 3 * delta :=
    (Nat.dvd_add_iff_left hdivshift).mp hdivsum
  have hcop : Nat.Coprime (2 ^ q) 3 := Nat.Coprime.pow_left q (by decide)
  have hdiv_delta : 2 ^ q ∣ delta := hcop.dvd_of_dvd_mul_left hdiv
  obtain ⟨e, he⟩ := hdiv_delta
  have hfact' :
      2 ^ q * ((2 * K + 7) * 2 ^ (r + 3) + (2 * K + 1)) =
        2 ^ q * ((2 ^ (K + 4) + 12 * 2 ^ (K - q)) + 3 * e) := by
    calc
      _ = 2 ^ q * (2 ^ (K + 4) + 12 * 2 ^ (K - q)) + 3 * delta := hfact
      _ = 2 ^ q * (2 ^ (K + 4) + 12 * 2 ^ (K - q)) + 3 * (2 ^ q * e) := by rw [he]
      _ = 2 ^ q * ((2 ^ (K + 4) + 12 * 2 ^ (K - q)) + 3 * e) := by ring
  have hL :
      (2 * K + 7) * 2 ^ (r + 3) + (2 * K + 1) =
        (2 ^ (K + 4) + 12 * 2 ^ (K - q)) + 3 * e :=
    Nat.mul_left_cancel (Nat.two_pow_pos q) hfact'
  have he_pos : 0 < e := by
    by_contra h
    have he0 : e = 0 := by omega
    simp [he0] at he
    omega
  have he_hi : e ≤ 2 * K + 3 := by
    have hle : e ≤ 2 ^ q * e := Nat.le_mul_of_pos_left e (Nat.two_pow_pos q)
    rw [← he] at hle
    omega
  have hpow12 : 4 * 2 ^ (K - q) = 2 ^ (K - q + 2) := by
    calc
      4 * 2 ^ (K - q) = 2 ^ 2 * 2 ^ (K - q) := by norm_num
      _ = 2 ^ (2 + (K - q)) := (Nat.pow_add 2 2 (K - q)).symm
      _ = 2 ^ (K - q + 2) := by congr 1 <;> omega
  have h12 : 12 * 2 ^ (K - q) = 3 * 2 ^ (K - q + 2) := by
    calc
      12 * 2 ^ (K - q) = 3 * (4 * 2 ^ (K - q)) := by ring
      _ = 3 * 2 ^ (K - q + 2) := by rw [hpow12]
  by_cases hcase : r + 3 ≤ K - q + 2
  · have hdiv1 : 2 ^ (r + 3) ∣ 2 ^ (K + 4) :=
      Nat.pow_dvd_pow 2 (by omega)
    have hdivpow : 2 ^ (r + 3) ∣ 2 ^ (K - q + 2) :=
      Nat.pow_dvd_pow 2 hcase
    have hdiv2 : 2 ^ (r + 3) ∣ 12 * 2 ^ (K - q) := by
      rw [h12]
      rcases hdivpow with ⟨w, hw⟩
      refine ⟨3 * w, ?_⟩
      rw [hw]
      ring
    have hmod1 : 2 ^ (K + 4) % 2 ^ (r + 3) = 0 :=
      Nat.mod_eq_zero_of_dvd hdiv1
    have hmod2 : (12 * 2 ^ (K - q)) % 2 ^ (r + 3) = 0 :=
      Nat.mod_eq_zero_of_dvd hdiv2
    have hmod : (3 * e) % 2 ^ (r + 3) = (2 * K + 1) % 2 ^ (r + 3) := by
      have h := congrArg (fun x => x % 2 ^ (r + 3)) hL
      simpa [Nat.add_mod, Nat.mul_mod, hmod1, hmod2] using h.symm
    have hnear1 : 3 * e < (2 * K + 1) + 2 ^ (r + 3) := by omega
    have hnear2 : 2 * K + 1 < 3 * e + 2 ^ (r + 3) := by omega
    have heq3 : 3 * e = 2 * K + 1 :=
      nat_eq_of_mod_eq_of_close (3 * e) (2 * K + 1) (2 ^ (r + 3))
        (by positivity) hmod hnear1 hnear2
    by_cases hq0 : q = 0
    · have hdelta : delta = e := by simpa [hq0] using he
      rw [hdelta] at hdelta_lo
      omega
    · by_cases hq1 : q = 1
      · have hpow_k2 : 2 ^ (K + 2) = 4 * 2 ^ K := by
          calc
            2 ^ (K + 2) = 2 ^ K * 2 ^ 2 := Nat.pow_add 2 K 2
            _ = 4 * 2 ^ K := by norm_num [Nat.mul_comm]
        have hpow_k4 : 2 ^ (K + 4) = 16 * 2 ^ K := by
          calc
            2 ^ (K + 4) = 2 ^ (K + 2) * 2 ^ 2 := by
              calc
                2 ^ (K + 4) = 2 ^ ((K + 2) + 2) := by congr 1 <;> omega
                _ = 2 ^ (K + 2) * 2 ^ 2 := Nat.pow_add 2 (K + 2) 2
            _ = 16 * 2 ^ K := by rw [hpow_k2]; norm_num [Nat.mul_assoc]
        have hpow_kminus1 : 12 * 2 ^ (K - 1) = 6 * 2 ^ K := by
          have hk : (K - 1) + 1 = K := by omega
          rw [← hk, Nat.pow_succ]
          ring
        have hpow_rhs : 2 ^ (K + 4) + 12 * 2 ^ (K - 1) = 11 * 2 ^ (K + 1) := by
          calc
            2 ^ (K + 4) + 12 * 2 ^ (K - 1) = 16 * 2 ^ K + 6 * 2 ^ K := by
              rw [hpow_k4, hpow_kminus1]
            _ = 11 * 2 ^ (K + 1) := by
              rw [Nat.pow_succ]
              ring
        have hEq : (2 * K + 7) * 2 ^ (r + 3) = 11 * 2 ^ (K + 1) := by
          have hL' := hL
          rw [hq1, hpow_rhs, heq3] at hL'
          omega
        have hsum : (r + 3) + (K + 1 - (r + 3)) = K + 1 := by omega
        have hpow_split :
            2 ^ (K + 1) = 2 ^ (r + 3) * 2 ^ (K + 1 - (r + 3)) := by
          rw [← hsum, Nat.pow_add]
        have hcEq : 2 * K + 7 = 11 * 2 ^ (K + 1 - (r + 3)) := by
          have hfac :
              2 ^ (r + 3) * (2 * K + 7) =
                2 ^ (r + 3) * (11 * 2 ^ (K + 1 - (r + 3))) := by
            calc
              2 ^ (r + 3) * (2 * K + 7) = (2 * K + 7) * 2 ^ (r + 3) := by ring
              _ = 11 * 2 ^ (K + 1) := hEq
              _ = 11 * (2 ^ (r + 3) * 2 ^ (K + 1 - (r + 3))) := by
                rw [hpow_split]
              _ = 2 ^ (r + 3) * (11 * 2 ^ (K + 1 - (r + 3))) := by ring
          exact Nat.mul_left_cancel (Nat.two_pow_pos (r + 3)) hfac
        by_cases hdiff : K + 1 - (r + 3) = 0
        · rw [hdiff] at hcEq
          norm_num at hcEq
          omega
        · have hdiff_pos : 1 ≤ K + 1 - (r + 3) := by omega
          have hpow_dvd : 2 ∣ 2 ^ (K + 1 - (r + 3)) := by
            have h := Nat.pow_dvd_pow 2 hdiff_pos
            simpa using h
          have hdivc : 2 ∣ 2 * K + 7 := by
            rw [hcEq]
            rcases hpow_dvd with ⟨w, hw⟩
            refine ⟨11 * w, ?_⟩
            rw [hw]
            ring
          rcases hdivc with ⟨w, hw⟩
          omega
      · have hqge2 : 2 ≤ q := by omega
        have hpow_dvd : 4 ∣ 2 ^ q := by
          have h := Nat.pow_dvd_pow 2 hqge2
          simpa using h
        have hpowq : 4 ≤ 2 ^ q := Nat.le_of_dvd (Nat.two_pow_pos q) hpow_dvd
        have h4e : 4 * e ≤ delta := by
          calc
            4 * e ≤ 2 ^ q * e := Nat.mul_le_mul_right e hpowq
            _ = delta := he.symm
        nlinarith [heq3, h4e, hdelta_hi, hK]
  · have hcase' : K - q + 3 ≤ r + 3 := by omega
    let M : Nat := 2 ^ (K - q + 2)
    have hMpos : 0 < M := by dsimp [M]; positivity
    have hMlarge : 4 * K + 8 < M := by dsimp [M]; exact hpow_kq
    have hmodulus : 2 ^ (K - q + 3) = 2 * M := by
      dsimp [M]
      have h : K - q + 3 = (K - q + 2) + 1 := by omega
      rw [h, Nat.pow_succ]
      ring
    have hdivpow1 : 2 ^ (K - q + 3) ∣ 2 ^ (r + 3) :=
      Nat.pow_dvd_pow 2 hcase'
    have hdivL : 2 ^ (K - q + 3) ∣ (2 * K + 7) * 2 ^ (r + 3) := by
      rcases hdivpow1 with ⟨w, hw⟩
      refine ⟨(2 * K + 7) * w, ?_⟩
      rw [hw]
      ring
    have hdivpow2 : 2 ^ (K - q + 3) ∣ 2 ^ (K + 4) :=
      Nat.pow_dvd_pow 2 (by omega)
    have hmodL : ((2 * K + 7) * 2 ^ (r + 3)) % (2 * M) = 0 := by
      rw [← hmodulus]
      exact Nat.mod_eq_zero_of_dvd hdivL
    have hmodR : 2 ^ (K + 4) % (2 * M) = 0 := by
      rw [← hmodulus]
      exact Nat.mod_eq_zero_of_dvd hdivpow2
    have h12M : 12 * 2 ^ (K - q) = 3 * M := by
      calc
        12 * 2 ^ (K - q) = 3 * 2 ^ (K - q + 2) := h12
        _ = 3 * M := by rfl
    have hMlt : M < 2 * M := by omega
    have h3M : (3 * M) % (2 * M) = M := by
      calc
        (3 * M) % (2 * M) = (2 * M + M) % (2 * M) := by congr 1 <;> omega
        _ = ((2 * M) % (2 * M) + M % (2 * M)) % (2 * M) := by rw [Nat.add_mod]
        _ = M := by simp [Nat.mod_eq_of_lt hMlt]
    have hmod : (M + 3 * e) % (2 * M) = (2 * K + 1) % (2 * M) := by
      have h := congrArg (fun x => x % (2 * M)) hL
      have hleft :
          ((2 * K + 7) * 2 ^ (r + 3) + (2 * K + 1)) % (2 * M) =
            (2 * K + 1) % (2 * M) := by
        simp [Nat.add_mod, hmodL]
      have hright :
          (2 ^ (K + 4) + 12 * 2 ^ (K - q) + 3 * e) % (2 * M) =
            (M + 3 * e) % (2 * M) := by
        simp [Nat.add_mod, hmodR, h12M, h3M, Nat.mod_eq_of_lt hMlt]
      rw [hleft, hright] at h
      exact h.symm
    have hnear1 : 2 * K + 1 < M + 3 * e := by omega
    have hnear2 : M + 3 * e < (2 * K + 1) + 2 * M := by omega
    have hEq := nat_eq_of_mod_eq_of_close (M + 3 * e) (2 * K + 1) (2 * M)
      (by omega) hmod hnear2 (by omega)
    omega

#print axioms t0_entry_even_parent_arithmetic_no_solution

end Agent10T0Parent
