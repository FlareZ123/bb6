import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 100000

namespace BB6.Agent3U5Q0RootAffineResidue

private theorem residual_rhs_div8192 (w : Nat) :
    8192 ∣ 20 * 2 ^ (201 + 3360 * w) := by
  have hdiv : 8192 ∣ 2 ^ (201 + 3360 * w) := by
    change 2 ^ 13 ∣ 2 ^ (201 + 3360 * w)
    exact Nat.pow_dvd_pow 2 (by omega)
  rcases hdiv with ⟨q, hq⟩
  refine ⟨20 * q, ?_⟩
  rw [hq]
  omega

private theorem residual_linear_div8192 (w t : Nat)
    (hres : 211 * t + 1360 + 22155 * w =
      20 * 2 ^ (201 + 3360 * w)) :
    8192 ∣ 211 * t + 1360 + 22155 * w := by
  rw [hres]
  exact residual_rhs_div8192 w

private theorem mul291_preserves_div8192 (n : Nat)
    (hdiv : 8192 ∣ n) : 8192 ∣ 291 * n := by
  rcases hdiv with ⟨m, hm⟩
  refine ⟨291 * m, ?_⟩
  rw [hm]
  omega

private theorem affine_expand (w h : Nat) :
    291 * (211 * (39 + 64 * h) + 1360 + 22155 * w) =
      (w + 5696 * h + 5119) + 8192 * (787 * w + 479 * h + 340) := by omega

private theorem affine_c_div8192 (h : Nat) :
    8192 ∣ 2496 * h + 3073 + 5696 * h + 5119 := by
  refine ⟨h + 1, ?_⟩
  omega

private theorem affine_mod_cancel (w h : Nat)
    (hA : 8192 ∣ w + 5696 * h + 5119)
    (hC : 8192 ∣ 2496 * h + 3073 + 5696 * h + 5119) :
    w % 8192 = (2496 * h + 3073) % 8192 := by omega

private theorem affine_w_mod64 (w h : Nat)
    (hmap : w % 8192 = (2496 * h + 3073) % 8192) : w % 64 = 1 := by omega

/-- For every U5 q=0 residual pair with t=39+64*h, the authentic
residual identity fixes w modulo 8192 as an affine function of h. -/
theorem residual_w_affine_mod8192 (w h : Nat)
    (hres : 211 * (39 + 64 * h) + 1360 + 22155 * w =
      20 * 2 ^ (201 + 3360 * w)) :
    w % 8192 = (2496 * h + 3073) % 8192 := by
  have hlin := residual_linear_div8192 w (39 + 64 * h) hres
  have hmul := mul291_preserves_div8192 _ hlin
  have hexpand := affine_expand w h
  have hsumdiv : 8192 ∣ (w + 5696 * h + 5119) + 8192 * (787 * w + 479 * h + 340) := by
    rw [hexpand] at hmul
    exact hmul
  have hB : 8192 ∣ 8192 * (787 * w + 479 * h + 340) :=
    ⟨787 * w + 479 * h + 340, rfl⟩
  have hdivA : 8192 ∣ w + 5696 * h + 5119 :=
    (Nat.dvd_add_iff_left hB).mpr hsumdiv
  exact affine_mod_cancel w h hdivA (affine_c_div8192 h)

private theorem affine_inverse_mod (h w : Nat)
    (hmap : w % 8192 = (2496 * h + 3073) % 8192) :
    h % 128 = (23 * (w % 8192 / 64 + 80)) % 128 := by omega

/-- The root residue determines the q=0 parameter modulo 128. -/
theorem residual_h_mod128_of_w (w h : Nat)
    (hres : 211 * (39 + 64 * h) + 1360 + 22155 * w =
      20 * 2 ^ (201 + 3360 * w)) :
    h % 128 = (23 * (w % 8192 / 64 + 80)) % 128 := by
  exact affine_inverse_mod h w (residual_w_affine_mod8192 w h hres)

/-- The affine map is injective on h-residues modulo 128. -/
theorem affine_residue_injective (h1 h2 : Nat)
    (heq : (2496 * h1 + 3073) % 8192 = (2496 * h2 + 3073) % 8192) :
    h1 % 128 = h2 % 128 := by omega

/-- Every residue modulo 8192 that is 1 modulo 64 is attained by an
h-residue modulo 128 under the affine map. Together with injectivity this
is a bijection onto the 128 residues that are 1 modulo 64. -/
theorem affine_residue_surjective (r : Nat)
    (hr : r < 8192) (hr64 : r % 64 = 1) :
    ∃ h, h % 128 = (23 * (r / 64 + 80)) % 128 ∧
      (2496 * h + 3073) % 8192 = r := by
  let h := (23 * (r / 64 + 80)) % 128
  refine ⟨h, ?_, ?_⟩
  · simp [h]
  · omega

/-- All U5 q=0 residual parameters in the t=39+64*h slice satisfy w=1 mod 64. -/
theorem residual_w_mod64 (w h : Nat)
    (hres : 211 * (39 + 64 * h) + 1360 + 22155 * w =
      20 * 2 ^ (201 + 3360 * w)) : w % 64 = 1 := by
  exact affine_w_mod64 w h (residual_w_affine_mod8192 w h hres)

#print axioms residual_w_affine_mod8192
#print axioms residual_h_mod128_of_w
#print axioms affine_residue_injective
#print axioms affine_residue_surjective
#print axioms residual_w_mod64

end BB6.Agent3U5Q0RootAffineResidue
