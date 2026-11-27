import AffineResidue
namespace BB6.Agent9AffineResidue
open BB6.P1CarryExtinction
open BB6.P1CarryExact (weightedTail)

theorem absSum_append (n j : Nat) (xs ys : List Bool) :
    absSum n j (xs++ys)=absSum n j xs+absSum n (j+xs.length) ys := by
  induction xs generalizing j with
  | nil => simp [absSum]
  | cons b bs ih =>
    simp only [List.cons_append,absSum,List.length_cons,ih]
    rw [show j+1+bs.length=j+(bs.length+1) by omega]
    omega

theorem expr_append (n : Nat) (xs ys : List Bool) :
    expr n (xs++ys)=expr n xs+absSum n (1+xs.length) ys := by
  simp only [expr,absSum_append]
  omega

theorem bitMass_factor (k j : Nat) (xs : List Bool) :
    bitMass (k+j) xs=2^k*bitMass j xs := by
  induction xs generalizing j with
  | nil => simp [bitMass]
  | cons b bs ih =>
    simp only [bitMass]
    rw [show k+j+1=k+(j+1) by omega,ih,Nat.pow_add]
    cases b <;> simp [Nat.mul_add]

/-- Splitting a word at its affine prefix eliminates all suffix
parameter dependence modulo 2^d whenever d <= k. -/
theorem expr_suffix (k : Nat) (xs ys : List Bool) (p : Node)
    (T : Nat) (h : Rep k xs p) :
    expr (p.r+2^k*T) (xs++ys) =
      1+2^k*(p.a+T*p.B+weightedTail p.r k ys+2^k*T*bitMass 0 ys) := by
  rcases h with ⟨hlen,hr,hex,hB⟩
  rw [expr_append,expr_shift,hex,←hB,show 1+xs.length=k by omega,
    absSum_shift,absSum_eq]
  have hb : bitMass k ys=2^k*bitMass 0 ys := by
    simpa using bitMass_factor k 0 ys
  rw [hb]
  simp only [Nat.mul_add]
  ac_rfl

theorem scaled_residue (k d A : Nat) (hk : 0<k) :
    (1+2^k*A)%2^(k+d)=1 ↔ A%2^d=0 := by
  have h1 : 1<2^k := Nat.one_lt_two_pow hk
  rw [Nat.pow_add,Nat.mod_mul,Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos k),
    Nat.mod_eq_of_lt h1,Nat.div_eq_of_lt h1,Nat.zero_add]
  constructor
  · intro h
    have hz : 2^k*(A%2^d)=0 := by omega
    rcases Nat.mul_eq_zero.mp hz with hzero|hzero
    · have hp := Nat.two_pow_pos k
      omega
    · exact hzero
  · intro h
    simp [h]

theorem suffix_iff (k d : Nat) (xs ys : List Bool) (p : Node)
    (T : Nat) (hk : 0<k) (hd : d≤k) (h : Rep k xs p) :
    expr (p.r+2^k*T) (xs++ys)%2^(k+d)=1 ↔
      (p.a+T*p.B+weightedTail p.r k ys)%2^d=0 := by
  rw [expr_suffix k xs ys p T h,scaled_residue k d _ hk]
  obtain ⟨v,hv⟩ := Nat.pow_dvd_pow 2 hd
  have he : 2^k*T*bitMass 0 ys=2^d*(v*T*bitMass 0 ys) := by
    rw [hv]
    ac_rfl
  rw [he,Nat.add_mul_mod_self_left]

/-- Exact prefix/suffix membership, with no canonical-half assumption. -/
theorem width_pos_iff_suffix (k d n : Nat) (hk : 0<k) (hd : d≤k) :
    0<width (k+d) n ↔
      ∃ p∈nodes (k-1), p.r=n%2^k ∧
        ∃ ys : List Bool, ys.length=d ∧
          (p.a+(n/2^k)*p.B+weightedTail p.r k ys)%2^d=0 := by
  rw [width_pos_iff _ _ (by omega)]
  constructor
  · rintro ⟨zs,hz,he⟩
    let xs := zs.take (k-1)
    let ys := zs.drop (k-1)
    have hx : xs.length=k-1 := by
      simp [xs,List.length_take]
      omega
    have hy : ys.length=d := by simp [ys,List.length_drop]; omega
    have hxy : xs++ys=zs := List.take_append_drop _ _
    obtain ⟨p,hp,hr⟩ := nodes_complete (k-1) xs hx
    have hr' : Rep k xs p := by
      rw [show k=k-1+1 by omega]
      exact hr
    have hpre : expr n xs%2^k=1 := by
      have hdiv : 2^k ∣ 2^(k+d) := Nat.pow_dvd_pow 2 (by omega)
      have hm := congrArg (fun x : Nat => x%2^k) he
      rw [Nat.mod_mod_of_dvd _ hdiv,Nat.mod_eq_of_lt (Nat.one_lt_two_pow hk)] at hm
      rw [←hxy,expr_append,show 1+xs.length=k by omega,absSum_eq,
        Nat.add_mul_mod_self_left] at hm
      exact hm
    have hpr := rep_unique k n xs p hr' hpre
    have hn : n=p.r+2^k*(n/2^k) := by
      rw [←hpr]
      exact (Nat.mod_add_div n _).symm
    refine ⟨p,hp,hpr.symm,ys,hy,?_⟩
    apply (suffix_iff k d xs ys p (n/2^k) hk hd hr').mp
    rw [←hn,hxy]
    exact he
  · rintro ⟨p,hp,hr,ys,hy,he⟩
    obtain ⟨xs,hx⟩ := nodes_sound (k-1) p hp
    have hx' : Rep k xs p := by
      rw [show k=k-1+1 by omega]
      exact hx
    refine ⟨xs++ys,?_,?_⟩
    · have hlen := hx'.1
      simp [List.length_append,hy]
      omega
    · have hn : n=p.r+2^k*(n/2^k) := by
        rw [hr]
        exact (Nat.mod_add_div n _).symm
      conv_lhs => rw [hn]
      exact (suffix_iff k d xs ys p (n/2^k) hk hd hx').mpr he

#print axioms expr_suffix
#print axioms suffix_iff
#print axioms width_pos_iff_suffix
end BB6.Agent9AffineResidue
