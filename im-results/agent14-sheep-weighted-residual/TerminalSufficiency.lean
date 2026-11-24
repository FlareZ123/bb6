import ThreeAdicLift
namespace SheepWeightedResidual

theorem add_mod_cancel (m c x y : Nat) (he : (c+x)%m=(c+y)%m) : x%m=y%m := by
  obtain ⟨k,l,h⟩ := Nat.mod_eq_mod_iff.mp he
  exact Nat.mod_eq_mod_iff.mpr ⟨k,l,by omega⟩

theorem mul_mod_congr (m d x y : Nat) (he : x%m=y%m) : (d*x)%m=(d*y)%m := by
  rw [Nat.mul_mod d x, Nat.mul_mod d y, he]

theorem mul_mod_cancel (m d i x y : Nat) (hi : (i*d)%m=1)
    (he : (d*x)%m=(d*y)%m) : x%m=y%m := by
  have hh := mul_mod_congr m i (d*x) (d*y) he
  rw [←Nat.mul_assoc,←Nat.mul_assoc i d y,Nat.mul_mod (i*d) x,Nat.mul_mod (i*d) y,hi] at hh
  simpa using hh

theorem type3_lift_mod (H B v m r i : Nat) (hm : 1<m)
    (hr : (2*r)%m=3%m) (hi : (i*3)%m=1)
    (hv : 2^B=1+3^H*v) (hb : 2^B%m=(1+19*r^H)%m) :
    (2^H*v)%m=19%m := by
  rw [hv] at hb
  have he := add_mod_cancel m 1 (3^H*v) (19*r^H) hb
  have hh := mul_mod_congr m (2^H) (3^H*v) (19*r^H) he
  have hL : 2^H*(3^H*v)=3^H*(2^H*v) := by ac_rfl
  have hR : 2^H*(19*r^H)=19*(2*r)^H := by rw [Nat.mul_pow]; ac_rfl
  rw [hL,hR] at hh
  have hR2 : (19*(2*r)^H)%m=(3^H*19)%m := by
    rw [Nat.mul_comm (3^H) 19, Nat.mul_mod 19 ((2*r)^H),Nat.pow_mod (2*r),hr,←Nat.pow_mod 3,←Nat.mul_mod 19]
  rw [hR2] at hh
  have hI : (i^H*3^H)%m=1 := by rw [←Nat.mul_pow,Nat.pow_mod,hi,Nat.one_pow,Nat.mod_eq_of_lt hm]
  exact mul_mod_cancel m (3^H) (i^H) (2^H*v) 19 hI hh

def allowedType3 (H : Nat) : Prop :=
  H%80=5 ∨ H%80=17 ∨ H%80=24 ∨ H%80=37 ∨ H%80=40 ∨ H%80=65

instance (H : Nat) : Decidable (allowedType3 H) := by unfold allowedType3; infer_instance

def type3Q (H : Nat) : Nat := match H%240 with
  | 5 => 71 | 85 => 11 | 165 => 131
  | 17 => 17 | 97 => 137 | 177 => 77
  | 24 => 22 | 104 => 82 | 184 => 142
  | 37 => 47 | 117 => 167 | 197 => 107
  | 40 => 34 | 120 => 94 | 200 => 154
  | 65 => 161 | 145 => 101 | 225 => 41
  | _ => 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
private theorem type3_q_table : ∀ h : Fin 240, allowedType3 h.val →
    0<type3Q h.val ∧
    (7*2^(h.val%6)*type3Q h.val)%9=1 ∧
    2^((2*3^((h.val-1)%4)*type3Q h.val)%10)%11=(1+19*7^(h.val%10))%11 ∧
    2^((2*3^((h.val-1)%2)*type3Q h.val)%8)%17=(1+19*10^(h.val%16))%17 := by decide

theorem type3_q_conditions (H : Nat) (ha : allowedType3 H) :
    0<type3Q H ∧ (7*2^H*type3Q H)%9=1 ∧
    2^(2*3^(H-1)*type3Q H)%11=(1+19*7^H)%11 ∧
    2^(2*3^(H-1)*type3Q H)%17=(1+19*10^H)%17 := by
  let h := H%240
  have hh : h<240 := Nat.mod_lt _ (by decide)
  have ha' : allowedType3 h := by
    unfold allowedType3 at *
    dsimp [h]
    rw [Nat.mod_mod_of_dvd _ (by decide : 80∣240)]
    exact ha
  have ht := type3_q_table ⟨h,hh⟩ ha'
  have hq : type3Q h=type3Q H := by simp [type3Q,h]
  have h6 : h%6=H%6 := Nat.mod_mod_of_dvd _ (by decide)
  have h10 : h%10=H%10 := Nat.mod_mod_of_dvd _ (by decide)
  have h16 : h%16=H%16 := Nat.mod_mod_of_dvd _ (by decide)
  have h4 : (h-1)%4=(H-1)%4 := by
    unfold allowedType3 at ha
    dsimp [h]
    omega
  have h2 : (h-1)%2=(H-1)%2 := by omega
  simp only at ht
  rw [hq,h6,h10,h16,h4,h2] at ht
  obtain ⟨hqpos,h9,h11,h17⟩ := ht
  refine ⟨hqpos,?_,?_,?_⟩
  · rw [Nat.mul_mod (7*2^H),Nat.mul_mod 7,base_period_reduce 2 9 6 H (by decide)]
    rw [Nat.mul_mod (7*2^(H%6)),Nat.mul_mod 7] at h9
    exact h9
  · rw [base_period_reduce 2 11 10 _ (by decide),ratio_period_reduce 7 11 10 H (by decide)]
    have he : (2*3^(H-1)*type3Q H)%10=(2*3^((H-1)%4)*type3Q H)%10 := by
      rw [Nat.mul_mod (2*3^(H-1)),Nat.mul_mod 2,base_period_reduce 3 10 4 (H-1) (by decide),←Nat.mul_mod 2,←Nat.mul_mod]
    rw [he]
    exact h11
  · rw [base_period_reduce 2 17 8 _ (by decide),ratio_period_reduce 10 17 16 H (by decide)]
    have he : (2*3^(H-1)*type3Q H)%8=(2*3^((H-1)%2)*type3Q H)%8 := by
      rw [Nat.mul_mod (2*3^(H-1)),Nat.mul_mod 2,base_period_reduce 3 8 2 (H-1) (by decide),←Nat.mul_mod 2,←Nat.mul_mod]
    rw [he]
    exact h17

private theorem crt1683 (y : Nat) (h9 : y%9=1) (h11 : y%11=8) (h17 : y%17=2) : y%1683=19 := by omega

set_option maxHeartbeats 2000000 in
theorem type3_terminal_exists (H : Nat) (ha : allowedType3 H) :
    ∃ k B : Nat, 1≤k ∧ 1≤B ∧ 3^H*(19+1683*k)=2^H*(2^B-1) := by
  have hH : 5≤H := by unfold allowedType3 at ha; omega
  let q := type3Q H
  obtain ⟨hq,h9,h11,h17⟩ := type3_q_conditions H ha
  obtain ⟨z,hz⟩ := type3_exponent_lift H q (by omega)
  let B := 2*3^(H-1)*q
  let v := 7*q+9*z
  let y := 2^H*v
  have hy9 : y%9=1 := by
    dsimp [y,v]
    have h : 2^H*(7*q+9*z)=7*2^H*q+9*(2^H*z) := by grind
    rw [h,Nat.add_mod,Nat.mul_mod 9]; simpa [q] using h9
  have hy11 : y%11=8 := by
    exact type3_lift_mod H B v 11 7 4 (by decide) (by decide) (by decide) hz h11
  have hy17 : y%17=2 := by
    exact type3_lift_mod H B v 17 10 6 (by decide) (by decide) (by decide) hz h17
  have hy : y%1683=19 := crt1683 y hy9 hy11 hy17
  have hylo : 19<y := by
    have hpow : 32≤2^H := Nat.pow_le_pow_right (by decide : 0<2) hH
    have hv : 1≤v := by
      change 1≤7*q+9*z
      have hq' : 0<q := hq
      omega
    have hp := Nat.mul_le_mul_left (2^H) hv
    simp at hp
    exact Nat.lt_of_lt_of_le (by decide : 19<32) (Nat.le_trans hpow hp)
  let k := y/1683
  have hyform : y=19+1683*k := by
    have hh:=Nat.mod_add_div y 1683
    rw [hy] at hh
    exact hh.symm
  have hk : 1≤k := by
    rw [hyform] at hylo
    omega
  have hB : 1≤B := by
    have hp : 0<3^(H-1) := Nat.pow_pos (by decide)
    have hq' : 0<q := hq
    exact Nat.mul_pos (Nat.mul_pos (by decide : 0<2) hp) hq'
  refine ⟨k,B,hk,hB,?_⟩
  rw [←hyform,hz]
  change 3^H*(2^H*v)=2^H*((1+3^H*v)-1)
  rw [Nat.add_comm 1,Nat.add_sub_cancel]
  ac_rfl

theorem type3_hidden_iff (H : Nat) :
    (∃ k B : Nat, 1≤k ∧ 1≤B ∧ 3^H*(19+1683*k)=2^H*(2^B-1)) ↔ allowedType3 H := by
  constructor
  · rintro ⟨k,B,hk,hB,he⟩
    by_cases hz : H=0
    · subst H
      exact False.elim (type3_H0 k B he)
    · exact type3_terminal_hidden_classes k H B (by omega) he
  · exact type3_terminal_exists H

#print axioms type3_hidden_iff
end SheepWeightedResidual
