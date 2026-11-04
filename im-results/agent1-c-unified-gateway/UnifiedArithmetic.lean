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

#print axioms two_families_iff_unified
#print axioms two_families_iff_one_four_power
end BB6.Agent1Unified
