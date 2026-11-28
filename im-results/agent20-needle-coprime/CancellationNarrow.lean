import AsymmetricRotation

namespace NeedleRotation.Asymmetric

/-- The old cutoff confines the candidate to a region with a large ternary gap. -/
theorem floor_large (r a m : Nat) (hr : 8≤r) (ha : 1728*r^4≤a)
    (hm : 0<m) (hold : m*m<16*r*a) : 8*r≤a/m := by
  have hp : r^3≤r^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have hA : 1024*r^3≤a := Nat.le_trans (Nat.mul_le_mul (by decide) hp) ha
  have hmul := Nat.mul_lt_mul_of_pos_left hold (show 0<64*r*r from Nat.mul_pos (Nat.mul_pos (by decide) (by omega)) (by omega))
  have hl : 64*r*r*(m*m)=(8*r*m)*(8*r*m) := by grind
  have hh : 64*r*r*(16*r*a)=1024*r^3*a := by simp only [Nat.pow_succ,Nat.pow_zero,Nat.one_mul]; grind
  rw [hl,hh] at hmul
  have hA2 := Nat.mul_le_mul_right a hA
  apply (Nat.le_div_iff_mul_le hm).mpr
  by_cases h : 8*r*m≤a
  · exact h
  · have hlt := Nat.mul_self_lt_mul_self (show a<8*r*m by omega)
    omega

/-- A candidate outside the new cutoff is much larger than the overhead in the
    individual coefficient widths. -/
theorem large_m (r a m : Nat) (hr : 8≤r) (ha : 1728*r^4≤a)
    (hbig : 13*(r+1)*a≤4*(m*m)) : 1000*r≤m := by
  have hsq : 64≤r*r := Nat.mul_le_mul hr hr
  have hh := Nat.mul_le_mul_right (r*r) (Nat.mul_le_mul_left 1728 hsq)
  have he : 1728*(r*r)*(r*r)=1728*r^4 := by simp only [Nat.pow_succ,Nat.pow_zero,Nat.one_mul]; grind
  rw [he] at hh
  have hA : 100000*(r*r)≤a := by omega
  have hB := Nat.mul_le_mul_left 117 hA
  have hC := Nat.mul_le_mul_right a (show 117≤13*(r+1) by omega)
  have hS : 4*((1000*r)*(1000*r))≤13*(r+1)*a := by
    have he1 : 4*((1000*r)*(1000*r))=4000000*(r*r) := by grind
    rw [he1]
    rw [←Nat.mul_assoc] at hB
    omega
  by_cases h : 1000*r≤m
  · exact h
  · have hlt := Nat.mul_self_lt_mul_self (show m<1000*r by omega)
    omega

/-- An exact integer estimate for one nonconstant term's width. -/
theorem width_scaled (m e H : Nat) :
    5*(width m e H*m)≤5*(H+10)*m+8*e := by
  let q := (e+m-1)/m
  let p := (q+4)/5
  have hq : q*m≤e+m-1 := Nat.div_mul_le_self _ _
  have hp : 5*p≤q+4 := by dsimp [p]; omega
  have hpm := Nat.mul_le_mul_right m hp
  have hpm' : 5*(p*m) ≤ q*m+4*m := by
    simpa only [Nat.mul_assoc,Nat.add_mul] using hpm
  have h8 := Nat.mul_le_mul_left 8 hpm'
  have h8' : 40*(p*m)≤8*e+40*m := by omega
  change 5*((H+8*p+2)*m)≤5*(H+10)*m+8*e
  rw [show (H+8*p+2)*m=H*m+8*(p*m)+2*m by grind,
      show 5*(H+10)*m=5*(H*m+10*m) by grind]
  omega

/-- With separately sized coefficients, the new 13/4 cutoff guarantees a
    good rotation. The old symmetric mass calculation paid a factor of 3. -/
theorem width_sum_lt (r a m : Nat) (hr : 8≤r) (ha : 1728*r^4≤a)
    (hm : 0<m) (hbig : 13*(r+1)*a≤4*(m*m)) :
    width m ((2*r+1)*a) 6+width m a (4*r+7)+width m 0 (4*r+8)<m := by
  let E := (2*r+1)*a
  let W := width m E 6+width m a (4*r+7)+width m 0 (4*r+8)
  have h1 := width_scaled m E 6
  have h2 := width_scaled m a (4*r+7)
  have h3 : width m 0 (4*r+8)=4*r+10 := by rw [width_const m _ hm]
  have hW : 5*(W*m)≤5*(8*r+43)*m+16*(r+1)*a := by
    have heW : 5*(W*m)=5*(width m E 6*m)+5*(width m a (4*r+7)*m)+5*(width m 0 (4*r+8)*m) := by dsimp [W]; grind
    rw [heW,h3]
    calc
       _ ≤ (5*(6+10)*m+8*E)+(5*((4*r+7)+10)*m+8*a)+5*((4*r+10)*m) := Nat.add_le_add_right (Nat.add_le_add h1 h2) _
       _ = 5*(8*r+43)*m+16*(r+1)*a := by dsimp [E]; grind
  have hM := large_m r a m hr ha hbig
  have hO : 65*(8*r+43)<m := by omega
  have hOm := Nat.mul_lt_mul_of_pos_right hO hm
  have hbig16 := Nat.mul_le_mul_left 16 hbig
  have hW13 := Nat.mul_le_mul_left 13 hW
  have htotal : 65*(W*m)<65*(m*m) := by
    rw [Nat.mul_add] at hW13
    have he1 : 13*(5*(W*m))=65*(W*m) := by omega
    have he2 : 13*(5*(8*r+43)*m)=65*(8*r+43)*m := by grind
    have he3 : 13*(16*(r+1)*a)=16*(13*(r+1)*a) := by grind
    rw [he1,he2,he3] at hW13
    omega
  change W<m
  by_cases h : W<m
  · exact h
  · have hle := Nat.mul_le_mul_left 65 (Nat.mul_le_mul_right m (show m≤W by omega))
    omega

/-- The sharpened bound in the exact three-term equation, assuming only the
    old cutoff and the existing elementary bounds on N and a. This covers both
    the initial cancellation feeder and the known second-level family. -/
theorem narrow_cutoff (r N a m : Nat) (c C : Int)
    (hr : 8≤r) (ha : 1728*r^4≤a) (haN : 2*a=N+5)
    (hN : 81≤N) (hNpow : N<2^(4*r)) (hm : 0<m)
    (hold : m*m<16*r*a) (hc : c.natAbs<64)
    (hC : C.natAbs≤110*m+325) (hCne : C≠0)
    (hd : denominator m∣value [(c,(2*r+1)*a),(C-c*(N:Int),a),(3*C,0)]) :
    4*(m*m)<13*(r+1)*a := by
  by_cases hsmall : 4*(m*m)<13*(r+1)*a
  · exact hsmall
  exfalso
  have hf := floor_large r a m hr ha hm hold
  have hma : m≤a := by
    have hfm := (Nat.le_div_iff_mul_le hm).mp hf
    have h := Nat.mul_le_mul_right m (show 1≤8*r by omega)
    omega
  have hC64 : C.natAbs<64*N := by omega
  have hsub := Int.natAbs_sub_le C (c*(N:Int))
  rw [Int.natAbs_mul,Int.natAbs_natCast] at hsub
  have hcn := Nat.mul_le_mul_right N (show c.natAbs≤63 by omega)
  have hD128 : (C-c*(N:Int)).natAbs<128*N := by omega
  have hC256 : (3*C).natAbs<256*N := by
    simp only [Int.natAbs_mul]
    change 3*C.natAbs<256*N
    omega
  have hDpow : (C-c*(N:Int)).natAbs<2^(4*r+7) := by
    rw [Nat.pow_add]
    have h := Nat.mul_lt_mul_of_pos_left hNpow (show 0<128 by decide)
    simpa [Nat.mul_comm] using Nat.lt_trans hD128 h
  have hCpow : (3*C).natAbs<2^(4*r+8) := by
    rw [Nat.pow_add]
    have h := Nat.mul_lt_mul_of_pos_left hNpow (show 0<256 by decide)
    simpa [Nat.mul_comm] using Nat.lt_trans hC256 h
  have hwidth := width_sum_lt r a m hr ha hm (by omega)
  have hE : a≤(2*r+1)*a := by simpa using Nat.mul_le_mul_right a (show 1≤2*r+1 by omega)
  have hdiv := constant_dvd_of_width_sum m a ((2*r+1)*a) a 6 (4*r+7) (4*r+8)
    c (C-c*(N:Int)) (3*C) hE (by omega) (by exact hc) hDpow hCpow hwidth hd
  have hpow : 2^(4*r+8)≤3^(a/m) := Nat.le_trans
    (Nat.pow_le_pow_left (by decide : 2≤3) _) (Nat.pow_le_pow_right (by decide) (by omega))
  have hnat := Int.natAbs_dvd_natAbs.mpr hdiv
  simp only [Int.natAbs_pow] at hnat
  change 3^(a/m)∣(3*C).natAbs at hnat
  have hpos : 0<(3*C).natAbs := Int.natAbs_pos.mpr (by omega)
  have hle := Nat.le_of_dvd hpos hnat
  omega

#print axioms floor_large
#print axioms large_m
#print axioms width_scaled
#print axioms width_sum_lt
#print axioms narrow_cutoff
end NeedleRotation.Asymmetric
