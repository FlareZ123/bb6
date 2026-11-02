import DeepFamily
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11

/-- A third disjoint infinite congruence class of forbidden Machine C
    first-family stopping indices. This is the r=2 arithmetic
    specialization of the all-depth source-connected Diophantine barrier. -/
theorem first_halt_m3784_mod4096_unreachable (m k : Nat)
    (hm : m%4096=3784)
    (hk : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hmpos : 5≤m := by omega
  have hpow : 4096 ∣ 2^(2*m+3) := by
    have hh : 2^12 ∣ 2^(2*m+3) := Nat.pow_dvd_pow 2 (by omega)
    simpa using hh
  have hmod : (k+3*m+4)%4096=0 := by
    rw [hk]
    exact Nat.mod_eq_zero_of_dvd hpow
  have hkmod : k%4096=932 := by omega
  let u : Nat := (k-4)/32
  have hku : k=32*u+4 := by dsimp [u]; omega
  have hu : u%128=29 := by dsimp [u]; omega
  have hfact : 21*u-1 = 2^(2*2+1)*(4*((21*u-97)/128)+3) := by
    change 21*u-1 = 32*(4*((21*u-97)/128)+3)
    omega
  intro hr
  rw [hku] at hr
  exact deep_low_gate_diophantine 2 ((21*u-97)/128) u hfact hr

#print axioms first_halt_m3784_mod4096_unreachable
end BB6.Agent11
