import Agent15RayReach
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15Rays

/-- A complete infinite first-stopping-index family is blank-unreachable. -/
theorem blank_no_first_175_mod256 (m k : Nat)
    (hm : m%256=175) (hgate : k+3*m+4=2^(2*m+3)) :
    ¬BB6.Agent3.CReach 1 k := by
  have hdiv : 256 ∣ (2:Nat)^(2*m+3) := by
    change (2:Nat)^8 ∣ (2:Nat)^(2*m+3)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨w,hw⟩ := hdiv
  have hkmod : k%256=239 := by
    rw [hw] at hgate
    omega
  have hk : k=256*(k/256)+239 := by omega
  intro hr
  rw [hk] at hr
  exact blank_no_one_239_mod256 (k/256) hr

/-- A disjoint complete infinite first-stopping-index family is blank-unreachable. -/
theorem blank_no_first_223_mod256 (m k : Nat)
    (hm : m%256=223) (hgate : k+3*m+4=2^(2*m+3)) :
    ¬BB6.Agent3.CReach 1 k := by
  have hdiv : 256 ∣ (2:Nat)^(2*m+3) := by
    change (2:Nat)^8 ∣ (2:Nat)^(2*m+3)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨w,hw⟩ := hdiv
  have hkmod : k%256=95 := by
    rw [hw] at hgate
    omega
  have hk : k=256*(k/256)+95 := by omega
  intro hr
  rw [hk] at hr
  exact blank_no_one_95_mod256 (k/256) hr

#print axioms blank_no_first_175_mod256
#print axioms blank_no_first_223_mod256
end BB6.Agent15Rays
