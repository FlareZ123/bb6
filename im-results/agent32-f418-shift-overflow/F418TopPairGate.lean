import F418NormalPath

namespace BB6.Agent32F418.ReturnBounds.Prefix
open EventSystem

/-- The final relative valuation of an odd-only word is encoded by its
    two highest set bits, unless the word is a singleton. -/
theorem oddChain_top_shape {N last : Nat} (hc : OddChain N last) :
    N=2^last ∨ ∃ h R, R<2^h ∧ N=2^(h+last+1)+2^h+R := by
  induction hc with
  | last j hj => exact Or.inl rfl
  | more j Q last hj hQ hc ih =>
    rcases ih with hsingle | ⟨h,R,hR,he⟩
    · right
      refine ⟨j,0,Nat.two_pow_pos _,?_⟩
      rw [hsingle,Nat.mul_add,Nat.mul_one,show 2*2^last=2^(last+1) by rw [Nat.pow_succ,Nat.mul_comm],←Nat.pow_add]
      simp [Nat.add_assoc]
    · right
      refine ⟨j+1+h,2^(j+1)*R+2^j,?_,?_⟩
      · have hp := Nat.two_pow_pos j
        have hm := Nat.mul_le_mul_left (2^(j+1)) (show R+1≤2^h by omega)
        rw [Nat.mul_add,Nat.mul_one,←Nat.pow_add] at hm
        have hpow : 2^(j+1)=2^j*2 := Nat.pow_succ _ _
        omega
      · rw [he,Nat.mul_add,Nat.mul_one,Nat.mul_comm 2,←Nat.mul_assoc,←Nat.pow_succ]
        rw [Nat.mul_add,Nat.mul_add,←Nat.pow_add,←Nat.pow_add]
        ac_rfl

theorem pow_interval_unique {N a b : Nat}
    (ha : 2^a≤N ∧ N<2^(a+1)) (hb : 2^b≤N ∧ N<2^(b+1)) : a=b := by
  by_cases h : a<b
  · have hm := pow_mono (show a+1≤b by omega)
    omega
  · by_cases h' : b<a
    · have hm := pow_mono (show b+1≤a by omega)
      omega
    · omega

theorem pair_interval {h k R : Nat} (hh : h<k) (hr : R<2^h) :
    2^k≤2^k+2^h+R ∧ 2^k+2^h+R<2^(k+1) := by
  have hm := pow_mono (show h+1≤k by omega)
  rw [Nat.pow_succ] at hm ⊢
  omega

/-- The largest two positions determine the odd-chain terminal gap exactly. -/
theorem oddChain_top_gap {N last h k R : Nat} (hc : OddChain N last)
    (hh : h<k) (hr : R<2^h) (he : N=2^k+2^h+R) :
    last+1=k-h := by
  have hk := pair_interval (R:=R) hh hr
  rw [←he] at hk
  rcases oddChain_top_shape hc with hs | ⟨a,U,hu,ha⟩
  · have hl : 2^last≤N ∧ N<2^(last+1) := by
      rw [hs,Nat.pow_succ]
      have hp := Nat.two_pow_pos last
      omega
    have hkl := pow_interval_unique hk hl
    rw [←hkl] at hs
    have hp := Nat.two_pow_pos h
    omega
  · have hk' := pair_interval (R:=U) (show a<a+last+1 by omega) hu
    rw [←ha] at hk'
    have hkl := pow_interval_unique hk hk'
    rw [←hkl] at ha
    have hEq : 2^h+R=2^a+U := by omega
    have hh' : 2^h≤2^h+R ∧ 2^h+R<2^(h+1) := by
      rw [Nat.pow_succ]; omega
    have ha' : 2^a≤2^h+R ∧ 2^h+R<2^(a+1) := by
      rw [hEq,Nat.pow_succ]; omega
    have hha := pow_interval_unique hh' ha'
    omega

/-- For a return with a present old top bit and modest consumed length,
    an odd-only output cannot borrow through that bit. Its top pair
    is precisely the new injection and the shifted old top bit. -/
theorem modest_gate_top_pair {b : Prefix} {Q W last : Nat}
    (hw : b.value Q<2^W) (htop : 2^(W-1)≤b.value Q)
    (hW : 9*b.p+6≤W) (hc : OddChain (b.next Q W) last) :
    last=7*b.p+3 ∧ b.p%2=0 := by
  let h := W-b.L-1
  have hh : 2≤h := by simp [h,L]; omega
  have hpow : 2^(W-1)=2^b.L*2^h := by
    rw [←Nat.pow_add]; congr 1; simp [h,L]; omega
  have hQtop : 2^h≤Q := by
    by_cases hle : 2^h≤Q
    · exact hle
    · have hm := Nat.mul_le_mul_left (2^b.L) (show Q+1≤2^h by omega)
      have hv := (value_bounds b Q).2
      rw [hpow] at htop
      omega
  have hC : b.C<2^(h-2) :=
    Nat.lt_of_lt_of_le (correction_upper b) (pow_mono (by simp [h,L,E]; omega))
  have hb : b.C≤Q := by
    have hm := pow_mono (show h-2≤h by omega)
    omega
  have hn := oddChain_noEven hc
  have ht := noBorrow_tail_noEven hw hb hn
  have hp4 : 2^h=4*2^(h-2) := by
    calc
      2^h=2^(2+(h-2)) := congrArg (fun n : Nat => 2^n) (by omega)
      _=4*2^(h-2) := by rw [Nat.pow_add]; rfl
  have hRtop : 2^h≤Q-b.C := by
    by_cases hle : 2^h≤Q-b.C
    · exact hle
    · exfalso
      apply top_pair_not_noEven (h:=h-2) (N:=Q-b.C) _ _ ht
      · omega
      · omega
  have hQt := (width_tail hw).2
  have hhW : W-b.L=h+1 := by simp [h,L]; omega
  rw [hhW,Nat.pow_succ] at hQt
  let R := Q-b.C-2^h
  have hR : R<2^h := by dsimp [R]; omega
  have he : b.next Q W=2^(W+b.E)+2^h+R := by
    unfold next
    dsimp [R]
    omega
  have hg := oddChain_top_gap hc (show h<W+b.E by simp [h,L,E]; omega) hR he
  have hlast : last=7*b.p+3 := by simp [h,L,E] at hg; omega
  have ho := oddChain_odd hc
  exact ⟨hlast,by omega⟩

theorem modest_gate_fatal_iff {b : Prefix} {Q W last : Nat}
    (hw : b.value Q<2^W) (htop : 2^(W-1)≤b.value Q)
    (hW : 9*b.p+6≤W) (hc : OddChain (b.next Q W) last) :
    last%4=3 ↔ b.p%4=0 := by
  have h := (modest_gate_top_pair hw htop hW hc).1
  omega

#print axioms oddChain_top_shape
#print axioms oddChain_top_gap
#print axioms modest_gate_top_pair
#print axioms modest_gate_fatal_iff
end BB6.Agent32F418.ReturnBounds.Prefix
