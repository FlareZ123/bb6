import Lean
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0

namespace BB6.Agent48.NeedleTwoStepOdd

def den (v : Nat) : Nat := 2^(v+1)+3
def bias (v : Nat) : Nat := 3*2^v+v+3
def destinationPlusTwo (q v : Nat) : Nat := den v*q+bias v

def modulus (v : Nat) : Nat := 5*den v
def offset (v : Nat) : Nat := 15*2^v+5*v+12

/-- Arithmetic normal form for an odd second transition into a terminal
power after one arbitrary odd-tower (q,v) source transition. -/
theorem two_step_odd_normal_form (q v K : Nat) :
    (∃ a, destinationPlusTwo q v = 2*a+1 ∧ 5*a+1=2^K) ↔
      2^(K+1)+3=5*destinationPlusTwo q v := by
  constructor
  · rintro ⟨a, hy, hk⟩
    rw [hy]
    rw [Nat.pow_succ']
    omega
  · intro h
    let y := destinationPlusTwo q v
    have hy : y%2=1 := by
      dsimp [y] at *
      have hp : 2^(K+1)%2=0 := by
        rw [Nat.pow_succ']
        omega
      omega
    refine ⟨y/2, ?_, ?_⟩
    · dsimp [y]
      omega
    · rw [Nat.pow_succ'] at h
      dsimp [y] at *
      omega

/-- Expanded Diophantine identity, one affine equation for the entire
odd-ending two-step preimage of terminal power 2^K. -/
theorem two_step_odd_expanded (q v K : Nat) :
  (∃ a, destinationPlusTwo q v=2*a+1 ∧ 5*a+1=2^K) ↔
    2^(K+1)=modulus v*q+offset v := by
  rw [two_step_odd_normal_form]
  simp only [destinationPlusTwo, modulus, den, bias, offset]
  rw [Nat.mul_add, Nat.mul_assoc]
  have hb : 5 * (3 * 2^v + v + 3) = 15 * 2^v + 5*v + 15 := by
    simp only [Nat.mul_add]
    omega
  rw [hb]
  omega

/-- Every fixed v supports at most one q for a terminal odd two-step
feeder, because the affine denominator is strictly positive. -/
theorem second_parent_unique (q₁ q₂ v K : Nat)
    (h₁ : 2^(K+1)=modulus v*q₁+offset v)
    (h₂ : 2^(K+1)=modulus v*q₂+offset v) : q₁=q₂ := by
  have hp : 0<modulus v := by simp [modulus,den]
  have he : modulus v*q₁=modulus v*q₂ := by omega
  exact Nat.eq_of_mul_eq_mul_left hp he

/-- The terminal odd two-step source valuation is always strictly below K.
The inequality holds for arbitrary q and does not use blank reachability. -/
theorem second_parent_valuation_lt (q v K : Nat)
    (h : 2^(K+1)=modulus v*q+offset v) : v<K := by
  by_cases hv : v<K
  · exact hv
  have hkv : K≤v := by omega
  have hpowle : (2:Nat)^K ≤ 2^v :=
    Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hkv
  have hbase : 0 < (2:Nat)^v := Nat.pow_pos (by decide)
  have h15 : 15*2^v ≤ modulus v*q+offset v := by
    unfold offset
    omega
  rw [Nat.pow_succ'] at h
  omega

#print axioms two_step_odd_normal_form
#print axioms two_step_odd_expanded
#print axioms second_parent_unique
#print axioms second_parent_valuation_lt
end BB6.Agent48.NeedleTwoStepOdd
