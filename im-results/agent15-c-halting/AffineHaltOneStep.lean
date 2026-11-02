import AffineNormalize
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15

/-- When a+2k is one modulo four, forced affine inversion stops in at most one step. -/
theorem affineNormalize_one_of_center_one (a k : Nat)
    (hc : (a+2*k)%4=1) :
    affineNormalize a k =
      if h : 4≤k ∧ k%2=0 ∧ (a+k)%4=1 then
        (a+k-2,(k-2)/2) else (a,k) := by
  by_cases h : 4≤k ∧ k%2=0 ∧ (a+k)%4=1
  · have hnext : ¬(4≤(k-2)/2 ∧ ((k-2)/2)%2=0 ∧
      ((a+k-2)+(k-2)/2)%4=1) := by omega
    rw [affineNormalize, dif_pos h, affineNormalize, dif_neg hnext,
      dif_pos h]
  · rw [affineNormalize,dif_neg h,dif_neg h]

#print axioms affineNormalize_one_of_center_one

theorem center_one_cond (a k : Nat) (hc : (a+2*k)%4=1) :
  (4≤k ∧ k%2=0 ∧ (a+k)%4=1) ↔ (4≤k ∧ k%4=0) := by omega

theorem center_three_cond (a k : Nat) (hc : (a+2*k)%4=3) :
  (4≤k ∧ k%2=0 ∧ (a+k)%4=1) ↔ (4≤k ∧ k%4=2) := by omega

theorem normalize_center_one_closed (a k : Nat)
    (hc : (a+2*k)%4=1) :
    affineNormalize a k =
      if 4≤k ∧ k%4=0 then (a+k-2,(k-2)/2) else (a,k) := by
  rw [affineNormalize_one_of_center_one a k hc]
  exact dite_congr (propext (center_one_cond a k hc)) (fun _ => rfl) (fun _ => rfl)

theorem normalize_center_three_recur (a k : Nat)
    (hc : (a+2*k)%4=3) :
    affineNormalize a k =
      if 4≤k ∧ k%4=2 then affineNormalize (a+k-2) ((k-2)/2) else (a,k) := by
  rw [affineNormalize]
  exact dite_congr (propext (center_three_cond a k hc)) (fun _ => rfl) (fun _ => rfl)

private theorem second_halt_power_mod4 (j m : Nat) :
  (2^(2*m+2)*(j+3))%4=0 := by
  have hp : 2^(2*m+2) = 4*2^(2*m) := by
    rw [show 2*m+2=2+2*m by omega, Nat.pow_add]
  rw [hp]
  have hd : 4 ∣ 4 * 2^(2*m) * (j+3) := ⟨2^(2*m)*(j+3), by simp [Nat.mul_assoc]⟩
  exact Nat.mod_eq_zero_of_dvd hd

theorem second_halt_center_mod4 (j m k : Nat)
    (hk : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    (2*j+3+2*k)%4 = (2*m+1)%4 := by
  have hmod : (k+j+3*m+5)%4=0 := by
    rw [hk]
    exact second_halt_power_mod4 j m
  omega

theorem second_halt_even_m_one_step (j m k : Nat)
    (hk : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hm : m%2=0) :
    affineNormalize (2*j+3) k =
      if 4≤k ∧ k%4=0 then (2*j+3+k-2,(k-2)/2)
      else (2*j+3,k) := by
  have hc := second_halt_center_mod4 j m k hk
  have hone : (2*j+3+2*k)%4=1 := by omega
  exact normalize_center_one_closed (2*j+3) k hone

#print axioms second_halt_even_m_one_step

theorem normalize_a_one_mod4 (a k : Nat) (ha : a%4=1) :
    affineNormalize a k =
      if h : 4≤k ∧ k%4=0 then (a+k-2,(k-2)/2) else (a,k) := by
  by_cases hs : 4≤k ∧ k%4=0
  · have hc : (a+2*k)%4=1 := by omega
    rw [normalize_center_one_closed a k hc]
    simp [hs]
  · have hnoc : ¬(4≤k ∧ k%2=0 ∧ (a+k)%4=1) := by omega
    rw [affineNormalize,dif_neg hnoc,dif_neg hs]

#print axioms normalize_a_one_mod4

theorem second_halt_a_k_mod4 (j m k : Nat)
    (hk : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    (2*j+3+k)%4 = (j+m+2)%4 := by
  have hmod : (k+j+3*m+5)%4=0 := by
    rw [hk]
    exact second_halt_power_mod4 j m
  omega

/-- At most one forced inverse for the second Machine C halting family
outside the two narrow residue sectors with j even and m odd. -/
theorem second_halt_one_step_outside_deep (j m k : Nat)
    (hk : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hcase : j%2=1 ∨ m%2=0 ∨ (j+m)%4=1) :
    affineNormalize (2*j+3) k =
      if h : 4≤k ∧ k%2=0 ∧ (2*j+3+k)%4=1
      then (2*j+3+k-2,(k-2)/2) else (2*j+3,k) := by
  rcases hcase with hj | hm | hmod
  · have ha : (2*j+3)%4=1 := by omega
    have hnorm := normalize_a_one_mod4 (2*j+3) k ha
    have heq : (4≤k ∧ k%2=0 ∧ (2*j+3+k)%4=1) ↔
          (4≤k ∧ k%4=0) := by omega
    by_cases hb : 4≤k ∧ k%4=0
    · have hx : 4≤k ∧ k%2=0 ∧ (2*j+3+k)%4=1 := heq.mpr hb
      simpa [hb,hx] using hnorm
    · have hx : ¬ (4≤k ∧ k%2=0 ∧ (2*j+3+k)%4=1) := fun h => hb (heq.mp h)
      simpa [hb,hx] using hnorm
  · have hnorm := second_halt_even_m_one_step j m k hk hm
    have heq : (4≤k ∧ k%2=0 ∧ (2*j+3+k)%4=1) ↔
          (4≤k ∧ k%4=0) := by
      have hc := second_halt_center_mod4 j m k hk
      omega
    by_cases hb : 4≤k ∧ k%4=0
    · have hx : 4≤k ∧ k%2=0 ∧ (2*j+3+k)%4=1 := heq.mpr hb
      simpa [hb,hx] using hnorm
    · have hx : ¬ (4≤k ∧ k%2=0 ∧ (2*j+3+k)%4=1) := fun h => hb (heq.mp h)
      simpa [hb,hx] using hnorm
  · have hh := second_halt_a_k_mod4 j m k hk
    have hn : ¬ (4≤k ∧ k%2=0 ∧ (2*j+3+k)%4=1) := by omega
    rw [affineNormalize,dif_neg hn,dif_neg hn]

#print axioms second_halt_one_step_outside_deep
end BB6.Agent15
