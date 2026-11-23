import One307Source
import Lean.Elab.Tactic.Omega

namespace BB6.Agent13LowM67

/-- A new original-source exclusion of an entire low Machine C stopping
    progression. The halting-index witness m=512*z+67, z=13 mod64
    would force k=256*u+51, u=49 mod128. Four original-source unique
    inverse steps and the independently checked two-parent closure
    forbid the resulting blank-section return. -/
theorem low_stop_m67_z13_unreachable
    (z m k : Nat)
    (hm : m=512*z+67)
    (hz : z%64=13)
    (hstop : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hpdiv : 32768 ∣ 2^(2*m+3) := by
    have h : (2:Nat)^15 ∣ 2^(2*m+3) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa only [show (2:Nat)^15=32768 by decide] using h
  have hpmod : (2^(2*m+3))%32768=0 :=
    Nat.mod_eq_zero_of_dvd hpdiv
  have hkmod : k%32768=12595 := by
    have hs : (k+3*m+4)%32768=0 := by
      rw [hstop]
      exact hpmod
    rw [hm] at hs
    omega
  let u := 128*(k/32768)+49
  have hu : u%128=49 := by
    dsimp [u]
    omega
  have hk : k=256*u+51 := by
    have hdecomp := Nat.mod_add_div k 32768
    rw [hkmod] at hdecomp
    dsimp [u]
    omega
  rw [hk]
  exact BB6.Agent13One307.no_one_256u51_u49_mod128 u hu

#print axioms low_stop_m67_z13_unreachable
end BB6.Agent13LowM67
