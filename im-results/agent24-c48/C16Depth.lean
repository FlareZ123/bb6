import C16Reach
import FeederOrbitGeneric
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- Genuine blank-section states of the form (1,4096q+260) are
    unreachable. The entire quantified q family is covered. -/
theorem blank_no_c16_one_gate (q : Nat) :
    ¬BB6.Agent3.CReach 1 (4096*q+260) := by
  intro h
  have ht : 1≤256*q+16 := by omega
  have hk : 4096*q+260=16*(256*q+16)+4 := by omega
  rw [hk] at h
  obtain ⟨time,hr⟩ :=
    (BB6.Agent3.generic_one_gate_reach_iff (256*q+16) ht).mp h
  have hx : 12*(256*q+16)=3072*q+192 := by omega
  have hy : 10*(256*q+16)-1=2560*q+159 := by omega
  rw [hx,hy] at hr
  exact blank_no_c16_target q time hr

/-- Every possible low Machine C halting section whose exponential
    parameter is 4008 modulo 4096 is absent from the real blank orbit. -/
theorem blank_no_low_halt_depth4008 (m k : Nat)
    (hm : m%4096=4008)
    (heq : k+3*m+4=2^(2*m+3)) :
    ¬BB6.Agent3.CReach 1 k := by
  have hlarge : 5≤m := by omega
  have hpow : 4096 ∣ 2^(2*m+3) := by
    change 2^12 ∣ 2^(2*m+3)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨w,hw⟩ := hpow
  have hmod : k%4096=260 := by omega
  have hk : k=4096*(k/4096)+260 := by omega
  intro h
  rw [hk] at h
  exact blank_no_c16_one_gate (k/4096) h

#print axioms blank_no_c16_one_gate
#print axioms blank_no_low_halt_depth4008
end BB6.Agent46
