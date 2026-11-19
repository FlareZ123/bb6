import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 200000
set_option maxRecDepth 12000

namespace BB6.Agent3U5B2Root32ParameterBridge

/-- Powers of two with exponent divisible by twelve are one modulo 105. -/
private theorem pow_two_mod105_12q (q : Nat) :
    (2:Nat)^(12*q)%105=1 := by
  rw [Nat.pow_mul, Nat.pow_mod]
  have h12 : (2:Nat)^12%105=1 := by decide
  rw [h12]
  simp

/-- The root exponent has the fixed residue needed modulo 105. -/
private theorem pow_two_mod105_of_mod12 (n : Nat)
    (hn : n%12=8) : (2:Nat)^n%105=46 := by
  have hdecomp : n=12*(n/12)+8 := by omega
  rw [hdecomp, Nat.pow_add, Nat.mul_mod]
  rw [pow_two_mod105_12q]

private theorem root32_exponent_facts (r E : Nat)
    (hE : E=201+3360*(6657+8192*r)) :
    6≤E-13 ∧ (E-13)%12=8 := by
  have hE19 : 19≤E := by rw [hE]; omega
  constructor
  · omega
  · have hEm : E-13=188+3360*(6657+8192*r) := by rw [hE]; omega
    rw [hEm]
    omega

private theorem root32_u_mod64 (r u : Nat)
    (hr : r%64=32)
    (hmod : (18018+211*u+22155*r)%64=0) : u%64=10 := by
  have h1 : 18018%64=34 := by decide
  have h2 : 211%64=19 := by decide
  have h3 : 22155%64=11 := by decide
  have hu_lt64 : u%64<64 := Nat.mod_lt u (by decide)
  have hu_mod_mod : (u%64)%64 = u%64 := Nat.mod_eq_of_lt hu_lt64
  have hred : (34+19*(u%64)+11*32)%64=0 := by
    simpa [Nat.add_mod, Nat.mul_mod, h1, h2, h3, hr, hu_mod_mod] using hmod
  omega

private theorem root32_u_mod105 (r u : Nat)
    (hmod : (18018+211*u+22155*r)%105=80) : u%105=17 := by
  have h1 : 18018%105=63 := by decide
  have h2 : 211%105=1 := by decide
  have h3 : 22155%105=0 := by decide
  have hu_lt105 : u%105<105 := Nat.mod_lt u (by decide)
  have hu_mod_mod : (u%105)%105=u%105 := Nat.mod_eq_of_lt hu_lt105
  have hred : (63+u%105)%105=80 := by
    simpa [Nat.add_mod, Nat.mul_mod, h1, h2, h3, hu_mod_mod] using hmod
  omega

private theorem root32_u_parameter_from_mods (u : Nat)
    (hu64 : u%64=10) (hu105 : u%105=17) :
    ∃ t : Nat, u=1802+6720*t := by
  have hu8 : u%8=2 := by omega
  obtain ⟨a,ha⟩ : ∃ a, u=105*a+17 := by
    refine ⟨u/105,?_⟩
    have h := Nat.mod_add_div u 105
    omega
  have ha8 : a%8=1 := by
    rw [ha] at hu8
    omega
  obtain ⟨w,hw⟩ : ∃ w, a=8*w+1 := by
    refine ⟨a/8,?_⟩
    have h := Nat.mod_add_div a 8
    omega
  have hu : u=122+840*w := by
    rw [ha,hw]
    omega
  have hw8 : w%8=2 := by
    rw [hu] at hu64
    omega
  refine ⟨w/8,?_⟩
  have h := Nat.mod_add_div w 8
  rw [hu]
  omega

/-- The exact residual root equation on the root-index class r=32 (mod 64)
forces the B2 parameter into u=1802+6720*t. -/
theorem root32_u_parameter_of_exact (r E u : Nat)
    (hr : r%64=32)
    (hE : E=201+3360*(6657+8192*r))
    (hRoot : 18018+211*u+22155*r=20*2^(E-13)) :
    ∃ t : Nat, u=1802+6720*t := by
  obtain ⟨h6,hmod12⟩ := root32_exponent_facts r E hE
  have hdiv64 : 64∣2^(E-13) := by
    have h := Nat.pow_dvd_pow 2 h6
    simpa only [show (2:Nat)^6=64 by decide] using h
  have hpow64 : (2^(E-13))%64=0 := Nat.mod_eq_zero_of_dvd hdiv64
  have hmod64 : (18018+211*u+22155*r)%64=0 := by
    rw [hRoot, Nat.mul_mod, hpow64]
  have hpow105 : (2:Nat)^(E-13)%105=46 :=
    pow_two_mod105_of_mod12 (E-13) hmod12
  have hmod105 : (18018+211*u+22155*r)%105=80 := by
    rw [hRoot, Nat.mul_mod, hpow105]
  exact root32_u_parameter_from_mods u
    (root32_u_mod64 r u hr hmod64)
    (root32_u_mod105 r u hmod105)

#print axioms root32_u_parameter_of_exact

end BB6.Agent3U5B2Root32ParameterBridge
