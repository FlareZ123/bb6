import Lean.Elab.Tactic.Omega

namespace BB6.Agent3U5B2Root4ParameterBridge

private theorem pow_two_mod105_12q (q : Nat) :
    (2:Nat)^(12*q)%105=1 := by
  rw [Nat.pow_mul, Nat.pow_mod]
  have h12 : (2:Nat)^12%105=1 := by decide
  rw [h12]
  simp

private theorem pow_two_mod105_of_mod12 (n : Nat)
    (hn : n%12=8) : (2:Nat)^n%105=46 := by
  have hdecomp : n=12*(n/12)+8 := by omega
  rw [hdecomp, Nat.pow_add, Nat.mul_mod]
  rw [pow_two_mod105_12q]

private theorem exponent_facts (r E : Nat)
    (hE : E=201+3360*(6657+8192*r)) :
    6≤E-13 ∧ (E-13)%12=8 := by
  have hE19 : 19≤E := by rw [hE]; omega
  constructor
  · omega
  · have hEm : E-13=188+3360*(6657+8192*r) := by rw [hE]; omega
    rw [hEm]
    omega

private theorem u_mod105 (r u : Nat)
    (hmod : (18018+211*u+22155*r)%105=80) : u%105=17 := by omega

private theorem u_mod8 (r u : Nat)
    (hr8 : r%8=4)
    (hmod : (18018+211*u+22155*r)%8=0) : u%8=6 := by omega

private theorem u_parameter_from_mods (u : Nat)
    (hu8 : u%8=6) (hu105 : u%105=17) :
    ∃ w : Nat, u=542+840*w := by
  have hu840 : u%840=542 := by omega
  refine ⟨u/840,?_⟩
  have h := Nat.mod_add_div u 840
  omega

private theorem w_even_of_mod64 (r w : Nat)
    (hr16 : r%16=12)
    (hmod64 : (18018+211*(542+840*w)+22155*r)%64=0) : w%2=0 := by omega

/-- On the root-index cylinder r=12 (mod 16), the exact residual root
equation forces u=542+840*w with w even. -/
theorem root4_u_parameter_of_exact (r E u : Nat)
    (hr8 : r%8=4) (hr16 : r%16=12)
    (hE : E=201+3360*(6657+8192*r))
    (hRoot : 18018+211*u+22155*r=20*2^(E-13)) :
    ∃ w : Nat, u=542+840*w ∧ w%2=0 := by
  obtain ⟨h6,hmod12⟩ := exponent_facts r E hE
  have hdiv8 : 8∣2^(E-13) := by
    have h := Nat.pow_dvd_pow 2 (Nat.le_trans (by decide : 3≤6) h6)
    simpa only [show (2:Nat)^3=8 by decide] using h
  have hpow8 : (2^(E-13))%8=0 := Nat.mod_eq_zero_of_dvd hdiv8
  have hmod8 : (18018+211*u+22155*r)%8=0 := by
    rw [hRoot, Nat.mul_mod, hpow8]
  have hpow105 : (2:Nat)^(E-13)%105=46 :=
    pow_two_mod105_of_mod12 (E-13) hmod12
  have hmod105 : (18018+211*u+22155*r)%105=80 := by
    rw [hRoot, Nat.mul_mod, hpow105]
  have hu105 : u%105=17 := u_mod105 r u hmod105
  have hu8 : u%8=6 := u_mod8 r u hr8 hmod8
  obtain ⟨w,hw⟩ := u_parameter_from_mods u hu8 hu105
  have hdiv64 : 64∣2^(E-13) := by
    have h := Nat.pow_dvd_pow 2 h6
    simpa only [show (2:Nat)^6=64 by decide] using h
  have hpow64 : (2^(E-13))%64=0 := Nat.mod_eq_zero_of_dvd hdiv64
  have hmod64 : (18018+211*u+22155*r)%64=0 := by
    rw [hRoot, Nat.mul_mod, hpow64]
  have hwEven : w%2=0 := by
    rw [hw] at hmod64
    exact w_even_of_mod64 r w hr16 hmod64
  exact ⟨w,hw,hwEven⟩

#print axioms root4_u_parameter_of_exact

end BB6.Agent3U5B2Root4ParameterBridge
