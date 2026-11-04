import Std
import Lean.Elab.Tactic.Omega

namespace BB6.Agent1Unified

/-- A single dyadic equation simultaneously describes both nonzero
    classes of the full Machine C section stopping locus. -/
theorem two_families_iff_unified (a k : Nat) :
    ((a = 1 ∧ ∃ m : Nat, k + 3*m + 4 = 2^(2*m+3)) ∨
     (∃ j m : Nat, a = 2*j+3 ∧
       k+j+3*m+5 = 2^(2*m+2)*(j+3))) ↔
    (0 < a ∧ a%2=1 ∧ ∃ m : Nat,
       a+2*k+6*m+7 = 2^(2*m+2)*(a+3)) := by
  constructor
  · rintro (⟨ha,m,hm⟩ | ⟨j,m,ha,hm⟩)
    · subst a
      refine ⟨by omega, by omega, m, ?_⟩
      have hpow : 2^(2*m+3) = 2*(2^(2*m+2)) := by
        rw [show 2*m+3=(2*m+2)+1 by omega, Nat.pow_succ]
        omega
      omega
    · subst a
      refine ⟨by omega, by omega, m, ?_⟩
      have hscale : 2^(2*m+2)*(2*j+3+3) =
          2*(2^(2*m+2)*(j+3)) := by
        have h : 2*j+3+3 = 2*(j+3) := by omega
        rw [h]
        ac_rfl
      omega
  · rintro ⟨ha,hodd,m,hm⟩
    by_cases h1 : a=1
    · left
      refine ⟨h1,m,?_⟩
      subst a
      have hpow : 2^(2*m+3) = 2*(2^(2*m+2)) := by
        rw [show 2*m+3=(2*m+2)+1 by omega, Nat.pow_succ]
        omega
      omega
    · right
      let j := (a-3)/2
      have haa : a=2*j+3 := by dsimp [j]; omega
      refine ⟨j,m,haa,?_⟩
      rw [haa] at hm
      have hscale : 2^(2*m+2)*(2*j+3+3) =
          2*(2^(2*m+2)*(j+3)) := by
        have h : 2*j+3+3 = 2*(j+3) := by omega
        rw [h]
        ac_rfl
      omega

/-- The same halting equation in base four. -/
theorem dyadic_power_eq_four (m : Nat) :
    2^(2*m+2) = 4^(m+1) := by
  calc
    2^(2*m+2) = (2^2)^(m+1) := by
      rw [show 2*m+2 = 2*(m+1) by omega, Nat.pow_mul]
    _ = 4^(m+1) := by simp

theorem two_families_iff_one_four_power (a k : Nat) :
    ((a = 1 ∧ ∃ m : Nat, k + 3*m + 4 = 2^(2*m+3)) ∨
     (∃ j m : Nat, a = 2*j+3 ∧
       k+j+3*m+5 = 2^(2*m+2)*(j+3))) ↔
    (0 < a ∧ a%2=1 ∧ ∃ m : Nat,
       a+2*k+6*m+7 = 4^(m+1)*(a+3)) := by
  rw [two_families_iff_unified]
  constructor
  · rintro ⟨ha,hodd,m,hm⟩
    exact ⟨ha,hodd,m,by rwa [dyadic_power_eq_four] at hm⟩
  · rintro ⟨ha,hodd,m,hm⟩
    exact ⟨ha,hodd,m,by rwa [dyadic_power_eq_four]⟩

/-- Halting levels with (u+m)%4=1 land in the odd-right,
    sum-two image class of the original section map. -/
theorem bad_level_residues (u k m : Nat)
    (hm : (u+m)%4=1)
    (heq : (2*u+1)+2*k+6*m+7 = 4^(m+1)*((2*u+1)+3)) :
    k%2=1 ∧ ((2*u+1)+k)%4=2 := by
  have hpow : 4^(m+1) = 4*4^m := by
    rw [Nat.pow_succ]
    omega
  have hscale : 4^(m+1)*((2*u+1)+3)=8*(4^m*(u+2)) := by
    rw [hpow,show 2*u+1+3=2*(u+2) by omega]
    have h8 : (8:Nat)=4*2 := by decide
    rw [h8]
    ac_rfl
  rw [hscale] at heq
  omega

/-- Uniform halting locus as a single affine family in parameters
    u (odd-state index) and m (dyadic bounce depth). -/
theorem one_four_power_iff_affine_rays (a k : Nat) :
    (0 < a ∧ a%2=1 ∧ ∃ m : Nat,
       a+2*k+6*m+7 = 4^(m+1)*(a+3)) ↔
    (∃ u m : Nat, a=2*u+1 ∧
       k+u+3*m+4 = 4^(m+1)*(u+2)) := by
  constructor
  · rintro ⟨ha,ho,m,heq⟩
    let u := (a-1)/2
    have hh : a=2*u+1 := by dsimp [u]; omega
    refine ⟨u,m,hh,?_⟩
    rw [hh] at heq
    have hs : 4^(m+1)*(2*u+1+3)=2*(4^(m+1)*(u+2)) := by
      rw [show 2*u+1+3=2*(u+2) by omega]
      ac_rfl
    rw [hs] at heq
    omega
  · rintro ⟨u,m,ha,hm⟩
    subst a
    refine ⟨by omega,by omega,m,?_⟩
    have hs : 4^(m+1)*(2*u+1+3)=2*(4^(m+1)*(u+2)) := by
      rw [show 2*u+1+3=2*(u+2) by omega]
      ac_rfl
    rw [hs]
    omega

/-- Every nonzero Machine C halting input has right counter 1 mod 3. -/
theorem affine_ray_right_mod3 (u k m : Nat)
    (heq : k+u+3*m+4=4^(m+1)*(u+2)) : k%3=1 := by
  have h4 : (4:Nat)%3=1 := by decide
  have hp : 4^(m+1)%3=1 := by simp [Nat.pow_mod, h4]
  have hr : (4^(m+1)*(u+2))%3=(u+2)%3 := by
    rw [Nat.mul_mod,hp]
    omega
  omega

#print axioms one_four_power_iff_affine_rays
#print axioms affine_ray_right_mod3

#print axioms bad_level_residues
#print axioms two_families_iff_unified
#print axioms two_families_iff_one_four_power
end BB6.Agent1Unified
