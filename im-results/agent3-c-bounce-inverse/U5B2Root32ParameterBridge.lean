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

private theorem root_equation_mod16 (u r : Nat)
    (hmod : (18018+211*u+22155*r)%16=0) :
    (u+105*r)%16=10 := by
  omega

private theorem root_equation_mod105 (u r : Nat)
    (hmod : (18018+211*u+22155*r)%105=80) :
    (u+105*r)%105=17 := by
  omega

private theorem root_equation_crt1680 (x : Nat)
    (h16 : x%16=10) (h105 : x%105=17) : x%1680=122 := by
  omega

/-- The residual equation and exponent class determine one parameter
congruence modulo 1680 for every root index, not only the special
mod-16/mod-64 cylinders. -/
theorem root_equation_mod1680 (r E u : Nat)
    (hE : E=201+3360*(6657+8192*r))
    (hRoot : 18018+211*u+22155*r=20*2^(E-13)) :
    (u+105*r)%1680=122 := by
  obtain ⟨h6,hmod12⟩ := root32_exponent_facts r E hE
  have h4 : 4≤E-13 := by omega
  have hdiv16 : 16∣2^(E-13) := by
    have h := Nat.pow_dvd_pow 2 h4
    simpa only [show (2:Nat)^4=16 by decide] using h
  have hpow16 : (2^(E-13))%16=0 := Nat.mod_eq_zero_of_dvd hdiv16
  have hmod16 : (18018+211*u+22155*r)%16=0 := by
    rw [hRoot, Nat.mul_mod, hpow16]
  have hpow105 : (2:Nat)^(E-13)%105=46 :=
    pow_two_mod105_of_mod12 (E-13) hmod12
  have hmod105 : (18018+211*u+22155*r)%105=80 := by
    rw [hRoot, Nat.mul_mod, hpow105]
  exact root_equation_crt1680 (u+105*r)
    (root_equation_mod16 u r hmod16)
    (root_equation_mod105 u r hmod105)

private theorem affine_of_mod1680 (x : Nat) (hx : x%1680=122) :
    ∃ t : Nat, x=122+1680*t := by
  refine ⟨x/1680,?_⟩
  have h := Nat.mod_add_div x 1680
  omega

/-- The root equation therefore has the affine parameter form
u+105*r = 122+1680*t for some natural t. -/
theorem root_equation_affine_parameter (r E u : Nat)
    (hE : E=201+3360*(6657+8192*r))
    (hRoot : 18018+211*u+22155*r=20*2^(E-13)) :
    ∃ t : Nat, u+105*r=122+1680*t := by
  exact affine_of_mod1680 (u+105*r) (root_equation_mod1680 r E u hE hRoot)

/-- The exact residual root equation forces the B2 and P4 root
parameters to have the same parity. -/
theorem root_equation_parity (r E u : Nat)
    (hRoot : 18018+211*u+22155*r=20*2^(E-13)) :
    u%2 = r%2 := by
  have hdiv : 2 ∣ 18018+211*u+22155*r := by
    refine ⟨10*2^(E-13), ?_⟩
    rw [hRoot]
    omega
  rcases hdiv with ⟨n, hn⟩
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

private theorem mod_complement (x q : Nat)
    (hx : x<8192) (hq : x+1535=8192*q) : x=6657 := by omega

private theorem cancel_8192 (x y : Nat)
    (h : 8192*x=8192*y) : x=y := by omega

private theorem div_6657_add_mul (r : Nat) :
    (6657+8192*r)/8192=r := by omega

/-- On the B2 parameterization t=551+8192*u, the exact residual
identity forces the affine root parameter w=6657 (mod 8192). -/
theorem b2_root_residue_of_exact_residual (u w : Nat)
    (hres : 211*(551+8192*u)+1360+22155*w =
      20*2^(201+3360*w)) :
    w%8192=6657 := by
  have hdiv : 8192∣2^(201+3360*w) := by
    refine ⟨2^(188+3360*w),?_⟩
    have hexp : 201+3360*w=13+(188+3360*w) := by omega
    rw [hexp,Nat.pow_add,show (2:Nat)^13=8192 by decide]
  have hpowdiv : 8192∣20*2^(201+3360*w) := by
    rcases hdiv with ⟨q,hq⟩
    refine ⟨20*q,?_⟩
    rw [hq]
    omega
  have hmod :
      (211*(551+8192*u)+1360+22155*w)%8192=0 := by
    rw [hres]
    exact Nat.mod_eq_zero_of_dvd hpowdiv
  have hmulmod :
      (291*(211*(551+8192*u)+1360+22155*w))%8192=0 := by
    rw [Nat.mul_mod,hmod]
  have hexpand :
      291*(211*(551+8192*u)+1360+22155*w) =
        (w+5696*(8+128*u)+5119) +
          8192*(787*w+479*(8+128*u)+340) := by omega
  have hAm : (w+5696*(8+128*u)+5119)%8192=0 := by
    rw [hexpand] at hmulmod
    simpa [Nat.add_mod,Nat.mul_mod] using hmulmod
  have hsplit :
      w+5696*(8+128*u)+5119 = (w+1535)+8192*(89*u+6) := by omega
  have hWm : (w+1535)%8192=0 := by
    rw [hsplit] at hAm
    simpa [Nat.add_mod,Nat.mul_mod] using hAm
  have hmodW : (w%8192+1535)%8192=0 := by
    simpa [Nat.add_mod] using hWm
  have hdivW : 8192∣w%8192+1535 := Nat.dvd_of_mod_eq_zero hmodW
  rcases hdivW with ⟨q,hq⟩
  have hz : w%8192<8192 := Nat.mod_lt w (by decide : 0<8192)
  exact mod_complement (w%8192) q hz hq

/-- Reparameterizing the exact residual equation by w=6657+8192*r
produces the exact root-index equation used by the source-orbit closure. -/
theorem b2_exact_root_equation_of_residual (u r w E : Nat)
    (hw : w=6657+8192*r)
    (hE : E=201+3360*w)
    (hres : 211*(551+8192*u)+1360+22155*w =
      20*2^(201+3360*w)) :
    18018+211*u+22155*r=20*2^(E-13) := by
  have hleft :
      211*(551+8192*u)+1360+22155*(6657+8192*r) =
        8192*(18018+211*u+22155*r) := by omega
  have hEminus : E-13=188+3360*(6657+8192*r) := by rw [hE,hw]; omega
  have hpow : 2^E=8192*2^(E-13) := by
    have hexp : E=13+(E-13) := by omega
    rw [hexp,Nat.pow_add,show (2:Nat)^13=8192 by decide]
    simp
  have hE' : E=201+3360*(6657+8192*r) := by rw [hw] at hE; exact hE
  have hEq :
      8192*(18018+211*u+22155*r)=20*2^E := by
    rw [hw,hleft] at hres
    rw [← hE'] at hres
    exact hres
  rw [hpow] at hEq
  have hmul : 20*(8192*2^(E-13))=8192*(20*2^(E-13)) := by
    calc
      20*(8192*2^(E-13)) = (20*8192)*2^(E-13) := by rw [← Nat.mul_assoc]
      _ = (8192*20)*2^(E-13) := by rw [Nat.mul_comm 20 8192]
      _ = 8192*(20*2^(E-13)) := by rw [Nat.mul_assoc]
  rw [hmul] at hEq
  exact cancel_8192 _ _ hEq

/-- Every exact B2 residual solution has a canonical quotient r in the
root affine parameterization, and satisfies the root-index equation. -/
theorem b2_root_parameter_of_exact_residual (u w E : Nat)
    (hE : E=201+3360*w)
    (hres : 211*(551+8192*u)+1360+22155*w =
      20*2^(201+3360*w)) :
    ∃ r, w=6657+8192*r ∧
      18018+211*u+22155*r=20*2^(E-13) := by
  have hmod := b2_root_residue_of_exact_residual u w hres
  let r := w/8192
  have hw : w=6657+8192*r := by
    dsimp [r]
    have h := Nat.mod_add_div w 8192
    omega
  exact ⟨r,hw,b2_exact_root_equation_of_residual u r w E hw hE hres⟩

/-- If the quotient root index is 32 modulo 64, the exact B2 residual
identity alone forces the B2 parameter into u=1802+6720*t. -/
theorem b2_root32_parameter_of_exact_residual (u w E : Nat)
    (hE : E=201+3360*w)
    (hres : 211*(551+8192*u)+1360+22155*w =
      20*2^(201+3360*w))
    (hr : (w/8192)%64=32) :
    ∃ t : Nat, u=1802+6720*t := by
  obtain ⟨r,hw,hRoot⟩ := b2_root_parameter_of_exact_residual u w E hE hres
  have hquot : w/8192=r := by rw [hw]; exact div_6657_add_mul r
  have hr' : r%64=32 := by rw [← hquot]; exact hr
  have hE' : E=201+3360*(6657+8192*r) := by rw [hw] at hE; exact hE
  exact root32_u_parameter_of_exact r E u hr' hE' hRoot

/-- Compose the U5 source residual equations with the q=0 parent form
and the B2 affine parameter h=8+128*u. On the r=32 (mod 64) root
cylinder this already forces the same B2 parameter progression. -/
theorem b2_root32_parameter_of_u5_q0_residual (u w E s m h : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hq0 : m+1=8*(39+64*h)+1)
    (hB2 : h=8+128*u)
    (hE : E=201+3360*w)
    (hr : (w/8192)%64=32) :
    ∃ t : Nat, u=1802+6720*t := by
  have ht : 39+64*h=551+8192*u := by rw [hB2]; omega
  have hp : m+1=8*(551+8192*u)+1 := by rw [ht] at hq0; exact hq0
  have hid : 211*(m+1)+10669+22155*(8*w)=160*2^(201+3360*w) := by omega
  have hidForT :
      211*(8*(551+8192*u)+1)+10669+22155*(8*w)=
        160*2^(201+3360*w) := by simpa [hp] using hid
  have hlin :
      211*(8*(551+8192*u)+1)+10669+22155*(8*w)=
        8*(211*(551+8192*u)+1360+22155*w) := by omega
  rw [hlin] at hidForT
  have hres :
      211*(551+8192*u)+1360+22155*w=20*2^(201+3360*w) := by omega
  exact b2_root32_parameter_of_exact_residual u w E hE hres hr

private theorem cancel_64 (x y : Nat) (h : 64*x=64*y) : x=y := by omega

private theorem mul_8192 (q : Nat) : 8192*q=64*(128*q) := by omega

private theorem quotient_rearrange (h r q : Nat)
    (hq : 184+128*r+89*h=128*q) : 89*h+184=128*(q-r) := by omega

private theorem mod89_h (h : Nat)
    (hmod : (89*h+184)%128=0) : h%128=8 := by omega

private theorem h_mod128_of_root_residue (h w r : Nat)
    (hw : w=6657+8192*r)
    (hres : 211*(39+64*h)+1360+22155*w=20*2^(201+3360*w)) :
    h%128=8 := by
  have hdiv : 8192∣2^(201+3360*w) := by
    refine ⟨2^(188+3360*w),?_⟩
    have hexp : 201+3360*w=13+(188+3360*w) := by omega
    rw [hexp,Nat.pow_add,show (2:Nat)^13=8192 by decide]
  have hpowdiv : 8192∣20*2^(201+3360*w) := by
    rcases hdiv with ⟨q,hq⟩
    refine ⟨20*q,?_⟩
    rw [hq]
    omega
  have hmod :
      (211*(39+64*h)+1360+22155*w)%8192=0 := by
    rw [hres]
    exact Nat.mod_eq_zero_of_dvd hpowdiv
  have hmulmod :
      (291*(211*(39+64*h)+1360+22155*w))%8192=0 := by
    rw [Nat.mul_mod,hmod]
  have hexpand :
      291*(211*(39+64*h)+1360+22155*w) =
        (w+5696*h+5119)+8192*(787*w+479*h+340) := by omega
  have hAm : (w+5696*h+5119)%8192=0 := by
    rw [hexpand] at hmulmod
    simpa [Nat.add_mod,Nat.mul_mod] using hmulmod
  rw [hw] at hAm
  have hsplit :
      6657+8192*r+5696*h+5119 = 64*(184+128*r+89*h) := by omega
  have hdivA : 8192∣64*(184+128*r+89*h) := by
    apply Nat.dvd_of_mod_eq_zero
    simpa [hsplit] using hAm
  rcases hdivA with ⟨q,hq⟩
  have hdiv128 : 128∣184+128*r+89*h := by
    refine ⟨q,?_⟩
    have hq' : 64*(184+128*r+89*h)=64*(128*q) := by
      calc
        64*(184+128*r+89*h) = 8192*q := hq
        _ = 64*(128*q) := mul_8192 q
    exact cancel_64 _ _ hq'
  rcases hdiv128 with ⟨q',hq'⟩
  have heq : 89*h+184=128*(q'-r) :=
    quotient_rearrange h r q' hq'
  have hmod128 : (89*h+184)%128=0 := by rw [heq]; simp
  exact mod89_h h hmod128

/-- The q=0 U5 residual equations and the root32 affine-index class
force h=8 (mod 128), so the B2-style quotient is derived rather than
assumed. -/
theorem u5_q0_root32_forces_h8_parameter (w E s m h r : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hq0 : m+1=8*(39+64*h)+1)
    (hw : w=6657+8192*r)
    (hE : E=201+3360*w)
    (hr : r%64=32) :
    ∃ u t : Nat, h=8+128*u ∧ u=1802+6720*t ∧
      18018+211*u+22155*r=20*2^(E-13) := by
  have hid : 211*(m+1)+10669+22155*(8*w)=160*2^(201+3360*w) := by omega
  have hlin :
      211*(m+1)+10669+22155*(8*w)=
        8*(211*(39+64*h)+1360+22155*w) := by rw [hq0]; omega
  rw [hlin] at hid
  have hres :
      211*(39+64*h)+1360+22155*w=20*2^(201+3360*w) := by omega
  have hhmod := h_mod128_of_root_residue h w r hw hres
  let u := h/128
  have hparam : h=8+128*u := by
    dsimp [u]
    have h := Nat.mod_add_div h 128
    rw [hhmod] at h
    omega
  have ht : 39+64*h=551+8192*u := by rw [hparam]; omega
  have hresB2 :
      211*(551+8192*u)+1360+22155*w=20*2^(201+3360*w) := by
    rw [← ht]
    exact hres
  have hq : w/8192=r := by rw [hw]; exact div_6657_add_mul r
  have hr' : (w/8192)%64=32 := by rw [hq]; exact hr
  obtain ⟨t,hu⟩ := b2_root32_parameter_of_exact_residual u w E hE hresB2 hr'
  have hRoot := b2_exact_root_equation_of_residual u r w E hw hE hresB2
  exact ⟨u,t,hparam,hu,hRoot⟩

#print axioms root_equation_affine_parameter
#print axioms root_equation_mod1680
#print axioms root_equation_parity
#print axioms root32_u_parameter_of_exact
#print axioms b2_root_residue_of_exact_residual
#print axioms b2_exact_root_equation_of_residual
#print axioms b2_root_parameter_of_exact_residual
#print axioms b2_root32_parameter_of_exact_residual
#print axioms b2_root32_parameter_of_u5_q0_residual
#print axioms u5_q0_root32_forces_h8_parameter

end BB6.Agent3U5B2Root32ParameterBridge
