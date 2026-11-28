import EvenV2
import Lean.Elab.Tactic.Omega

namespace BB6.Agent2F321OddV2Witness
open BB6.Agent2F321EvenV2

/-- A number with an explicit odd 2-adic valuation cannot have EvenV2Form. -/
theorem oddV2Witness_not_evenV2 (t u : Nat) (hu : u % 2 = 1) :
    ¬ EvenV2Form (2 * 4^t * u) := by
  intro h
  rcases h with ⟨s,v,heq,hv⟩
  by_cases hst : s ≤ t
  · obtain ⟨r,hr⟩ := Nat.exists_eq_add_of_le hst
    subst t
    rw [Nat.pow_add] at heq
    have heq' : 4^s * (2 * 4^r * u) = 4^s * v := by
      calc
        4^s * (2 * 4^r * u) = 2 * (4^s * 4^r) * u := by ac_rfl
        _ = 4^s * v := heq
    have hc : 2 * 4^r * u = v :=
      Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) heq'
    have hv0 : v % 2 = 0 := by
      rw [← hc, show 2 * 4^r * u = 2 * (4^r * u) by ac_rfl]
      simp
    omega
  · have hts : t < s := Nat.lt_of_not_ge hst
    obtain ⟨r,hr⟩ := Nat.exists_eq_add_of_lt hts
    have hpow : 4^s = 4^t * (4^r * 4) := by
      rw [hr]
      rw [show t + r + 1 = (t+r)+1 by omega, Nat.pow_succ, Nat.pow_add]
      ac_rfl
    rw [hpow] at heq
    have heq' : 4^t * (2*u) = 4^t * ((4^r * 4) * v) := by
      calc
        4^t * (2*u) = 2 * 4^t * u := by ac_rfl
        _ = (4^t * (4^r * 4)) * v := heq
        _ = 4^t * ((4^r * 4) * v) := by ac_rfl
    have hc : 2*u = (4^r * 4) * v :=
      Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) heq'
    have hl : (2*u) % 4 = 2 := by omega
    have hr0 : ((4^r * 4) * v) % 4 = 0 := by
      rw [show (4^r * 4) * v = 4 * (4^r * v) by ac_rfl]
      simp
    rw [hc, hr0] at hl
    contradiction

#print axioms oddV2Witness_not_evenV2
end BB6.Agent2F321OddV2Witness
