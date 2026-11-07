import Lean.Elab.Tactic.Omega

namespace H0TwoAdic

def N (c : Nat) : Nat := 4 * 2^c + c - 10

def H0 (c : Nat) : Nat := (4 * 2^(N c) + 13) - (8 * 2^c + c)

private theorem pow_two_linear (c : Nat) : c+1 ≤ 2^c := by
  induction c with
  | zero => decide
  | succ c ih =>
    rw [Nat.pow_succ]
    omega

private theorem N_large (c : Nat) (hc : 2 ≤ c) : c+2 ≤ N c := by
  have hp : 2^2 ≤ 2^c := Nat.pow_le_pow_right (by omega) hc
  have hpow : 4 ≤ 2^c := by simpa using hp
  simp only [N]
  omega

private theorem H0_identity (c : Nat) (hc : 2 ≤ c) :
    H0 c + (8 * 2^c + c) = 4 * 2^(N c) + 13 := by
  have hN := N_large c hc
  have hp : 2^(c+2) ≤ 2^(N c) := Nat.pow_le_pow_right (by omega) hN
  rw [Nat.pow_add] at hp
  have hb := pow_two_linear c
  have hbound : 8 * 2^c + c ≤ 4 * 2^(N c) + 13 := by omega
  simp only [H0]
  omega

private theorem pow_divides (E n : Nat) (he : E ≤ n) : (2^E) ∣ 2^n := by
  obtain ⟨k,hk⟩ : ∃ k, n = E + k := ⟨n-E, by omega⟩
  rw [hk, Nat.pow_add]
  exact ⟨2^k, rfl⟩

private theorem mul_pow_mod_zero (E n k : Nat) (hn : E ≤ n) :
    k*2^n % 2^E = 0 := by
  have hp := pow_divides E n hn
  apply Nat.mod_eq_zero_of_dvd
  rcases hp with ⟨t, ht⟩
  refine ⟨k*t, ?_⟩
  rw [ht]
  ac_rfl

/-- Stable 2-adic tail: after E input bits, the huge exponential terms
    disappear mod 2^E, leaving a one-to-one affine residue. -/
theorem H0_plus_input_mod (E c : Nat) (hc : max 2 E ≤ c) :
    (H0 c + c) % 2^E = 13 % 2^E := by
  have hc2 : 2 ≤ c := by omega
  have hcE : E ≤ c := by omega
  have hN : E ≤ N c := by have h:= N_large c hc2; omega
  have heq := H0_identity c hc2
  have hdivA : 4 * 2^(N c) % 2^E = 0 := mul_pow_mod_zero E (N c) 4 hN
  have hdivB : 8 * 2^c % 2^E = 0 := mul_pow_mod_zero E c 8 hcE
  have hcalc : (H0 c + c + 8 * 2^c) % 2^E = 13 % 2^E := by
    have hrew : H0 c + c + 8 * 2^c = 4 * 2^(N c) + 13 := by omega
    rw [hrew, Nat.add_mod, hdivA]
    simp
  have heqmod : (H0 c + c) % 2^E = (H0 c + c + 8 * 2^c) % 2^E := by
    calc
      (H0 c + c) % 2^E = ((H0 c + c) % 2^E + 0) % 2^E := by simp
      _ = ((H0 c + c) % 2^E + (8 * 2^c) % 2^E) % 2^E := by rw [hdivB]
      _ = (H0 c + c + 8 * 2^c) % 2^E := (Nat.add_mod _ _ _).symm
  exact heqmod.trans hcalc

private theorem mod_sum_bounded (m x z : Nat)
    (hx : x<m) (hz : z<m) :
    (x+z)%m = if x+z<m then x+z else x+z-m := by
  split
  · next h => exact Nat.mod_eq_of_lt h
  · next h =>
    rw [Nat.mod_eq_sub_mod (by omega : m ≤ x+z)]
    exact Nat.mod_eq_of_lt (by omega)

private theorem mod_cancel_bounded (m x y z:Nat)
    (hx:x<m)(hy:y<m)(hz:z<m)
    (h:(x+z)%m=(y+z)%m) : x=y := by
  rw [mod_sum_bounded m x z hx hz,mod_sum_bounded m y z hy hz] at h
  split at h <;> split at h <;> omega

/-- Every residue modulo every power of two occurs at a synthetically
    halting H0 seed, with an explicit sufficiently large witness. -/
theorem H0_all_two_power_residues (E r : Nat) :
    ∃ c, max 2 E ≤ c ∧ H0 c % 2^E = r % 2^E := by
  let M := 2^E
  let x := r % M
  let c := 13 + M * (E+2) - x
  have hM : 0 < M := Nat.pow_pos (by decide)
  have hx : x < M := Nat.mod_lt _ hM
  have hprod : E+2 ≤ M*(E+2) := by
    have h := Nat.mul_le_mul_right (E+2) (by omega : 1≤M)
    simpa only [Nat.one_mul] using h
  have hprodplus : M*(E+2) = M*(E+1)+M := by
    calc
      M*(E+2) = M*((E+1)+1) := by congr 1 <;> omega
      _ = M*(E+1)+M := by simp [Nat.mul_add]
  have hprodE : E+1 ≤ M*(E+1) := by
    have h := Nat.mul_le_mul_right (E+1) (by omega : 1≤M)
    simpa only [Nat.one_mul] using h
  have hcx : c+x=13+M*(E+2) := by
    change (13+M*(E+2)-x)+x=13+M*(E+2)
    have hb : x ≤ M*(E+2) := by omega
    omega
  have hc : max 2 E ≤ c := by
    change max 2 E ≤ 13+M*(E+2)-x
    rw [hprodplus]
    omega
  have hh : (H0 c + c) % M = 13 % M := H0_plus_input_mod E c hc
  have hcxmod : (c + x) % M = 13 % M := by
    rw [hcx, Nat.add_mod]
    have hdvd : M ∣ M*(E+2) := ⟨E+2, rfl⟩
    rw [Nat.mod_eq_zero_of_dvd hdvd]
    simp
  have hmod : ((H0 c % M) + (c % M)) % M = (x + (c%M))%M := by
    calc
      _ = (H0 c + c) % M := (Nat.add_mod _ _ _).symm
      _ = 13 % M := hh
      _ = (x+c)%M := by rw [Nat.add_comm]; exact hcxmod.symm
      _ = (x + (c%M))%M := by rw [Nat.add_mod_mod]
  have hroot : H0 c % M = x :=
    mod_cancel_bounded M (H0 c % M) x (c % M)
      (Nat.mod_lt _ hM) hx (Nat.mod_lt _ hM) hmod
  exact ⟨c,hc,hroot⟩

/-- An exactly affine, eventually periodic sequence mod 2^E.
    The period bound is unconditional on the multiplier k. -/
theorem H0_twoadic_period (E c k : Nat) (hc : max 2 E ≤ c) :
    H0 (c + 2^E*k) % 2^E = H0 c % 2^E := by
  let M := 2^E
  have hM : 0<M := Nat.pow_pos (by decide)
  have hc' : max 2 E ≤ c+M*k := by omega
  have h1 := H0_plus_input_mod E c hc
  have h2 := H0_plus_input_mod E (c+M*k) hc'
  have hzero : (M*k)%M=0 := Nat.mod_eq_zero_of_dvd ⟨k,rfl⟩
  have hshift : (c+M*k)%M=c%M := by
    rw [Nat.add_mod,hzero]
    simp
  have hmod :
      ((H0 (c+M*k) %M)+(c%M))%M = ((H0 c%M)+(c%M))%M := by
    calc
      _ = ((H0 (c+M*k)%M) + ((c+M*k)%M))%M := by rw [hshift]
      _ = (H0 (c+M*k)+(c+M*k))%M := (Nat.add_mod _ _ _).symm
      _ = 13 % M := h2
      _ = (H0 c+c)%M := h1.symm
      _ = ((H0 c%M)+(c%M))%M := Nat.add_mod _ _ _
  exact mod_cancel_bounded M _ _ (c%M)
    (Nat.mod_lt _ hM) (Nat.mod_lt _ hM) (Nat.mod_lt _ hM) hmod

#print axioms H0_twoadic_period
#print axioms H0_all_two_power_residues
#print axioms H0_plus_input_mod
end H0TwoAdic
