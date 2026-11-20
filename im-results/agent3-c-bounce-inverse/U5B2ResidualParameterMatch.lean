import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 200000
set_option maxRecDepth 12000

namespace BB6.Agent15ResidualParameter

private theorem mod89_h (h : Nat) (hmod : (89*h+184)%128=0) :
    h%128=8 := by
  have hmulmod : (105*(89*h+184))%128=0 := by
    rw [Nat.mul_mod,hmod]
  have hmul : 105*(89*h+184)=h+120+128*(73*h+150) := by omega
  rw [hmul] at hmulmod
  simp [Nat.add_mod] at hmulmod
  omega

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
        _ = 64*(128*q) := by omega
    exact Nat.mul_left_cancel (by omega) hq'
  have hdivA' : 128∣184+89*h+128*r := by
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hdiv128
  have hdivB : 128∣184+89*h := by
    exact (Nat.dvd_add_iff_left (show 128∣128*r from ⟨r,rfl⟩)).mpr hdivA'
  have hdivB' : 128∣89*h+184 := by simpa [Nat.add_comm] using hdivB
  have hmod128 : (89*h+184)%128=0 := Nat.mod_eq_zero_of_dvd hdivB'
  exact mod89_h h hmod128

/-- The authentic U5 residual equations and q=0 parent form identify
its high-stop parameter with the same B2 parameter. -/
theorem residual_forces_same_b2_parameter
    (w E s m h r : Nat)
    (hs : 211*s+129=5*2^E)
    (hm : 32*s=32+840*w+m)
    (hq0 : m+1=8*(39+64*h)+1)
    (hw : w=6657+8192*r)
    (hE : E=201+3360*w) :
    ∃ u : Nat, h=8+128*u ∧ m=4408+65536*u ∧
      211*(551+8192*u)+1360+22155*w=20*2^E := by
  have hm0 : m=8*(39+64*h) := by omega
  have hfour : 4*s=4+105*w+(39+64*h) := by omega
  have hres :
      211*(39+64*h)+1360+22155*w=20*2^(201+3360*w) := by
    calc
      211*(39+64*h)+1360+22155*w = 211*(4+105*w+(39+64*h))+516 := by omega
      _ = 211*(4*s)+516 := by rw [← hfour]
      _ = 4*(211*s+129) := by omega
      _ = 20*2^E := by rw [hs]; omega
      _ = 20*2^(201+3360*w) := by rw [hE]
  have hhmod := h_mod128_of_root_residue h w r hw hres
  let u := h/128
  have hh : h=8+128*u := by
    dsimp [u]
    have hdecomp := Nat.mod_add_div h 128
    rw [hhmod] at hdecomp
    omega
  have hq' : 39+64*h=551+8192*u := by rw [hh]; omega
  have hresB : 211*(551+8192*u)+1360+22155*w=20*2^E := by
    rw [← hq',hE]
    exact hres
  have hmfinal : m=4408+65536*u := by
    rw [hm0,hh]
    omega
  exact ⟨u,hh,hmfinal,hresB⟩

#print axioms residual_forces_same_b2_parameter

end BB6.Agent15ResidualParameter
