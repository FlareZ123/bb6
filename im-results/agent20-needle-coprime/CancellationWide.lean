import CancellationRotationBound

namespace NeedleRotation.CancellationWide
open Cancellation

theorem three_mass_bound (r m : Nat) (c C : Int)
    (hr : 8≤r) (hm : m≤2*r*a r) (hc : c.natAbs≤32) (hC : C.natAbs≤110*m+325) :
    mass [(c,(2*r+1)*a r),(C-c*(N r:Int),a r),(3*C,0)]<2^(8*r) := by
  have hN := N_ge_81 r (by omega)
  have hRN : 8*N r≤r*N r := Nat.mul_le_mul_right _ hr
  have hmN := Nat.le_trans hm (Nat.mul_le_mul_left (2*r) (a_le_N r (by omega)))
  rw [Nat.mul_assoc] at hmN
  have hcN := Nat.mul_le_mul_right (N r) hc
  have hsub := Int.natAbs_sub_le C (c*(N r:Int))
  rw [Int.natAbs_mul,Int.natAbs_natCast] at hsub
  have hscale := scale_mass_lt r hr
  simp only [mass,Int.natAbs_mul,Nat.add_zero]
  change c.natAbs+((C-c*(N r:Int)).natAbs+3*C.natAbs)<2^(8*r)
  rw [Nat.mul_assoc] at hscale
  omega

theorem near_mass_bound (r m : Nat) (c C : Int)
    (hr : 8≤r) (hm : m≤2*r*a r) (hc : c.natAbs≤32) (hC : C.natAbs≤110*m+325) :
    c.natAbs*3^(2*r)+C.natAbs<2^(8*r) := by
  have hN := N_ge_81 r (by omega)
  have hRN : 8*N r≤r*N r := Nat.mul_le_mul_right _ hr
  have hmN := Nat.le_trans hm (Nat.mul_le_mul_left (2*r) (a_le_N r (by omega)))
  rw [Nat.mul_assoc] at hmN
  have hcN := Nat.mul_le_mul_right (N r) hc
  have hscale := scale_mass_lt r hr
  rw [Nat.mul_assoc] at hscale
  rw [Nat.pow_mul,show (3:Nat)^2=9 by decide]
  change c.natAbs*N r+C.natAbs<2^(8*r)
  omega

theorem low_mass_bound (r m k : Nat) (c C : Int)
    (hr : 8≤r) (hm : m≤a r) (hk : 1≤k) (hc : c.natAbs≤32) (hC : C.natAbs≤110*m+325) :
    C.natAbs+2*r*c.natAbs*3^(2*r*k)<2^(9*r*k) := by
  have hN := N_ge_81 r (by omega)
  have ha := a_spec r
  have hCsmall : C.natAbs<64*N r := by omega
  have hNpow := N_lt_pow r (by omega)
  have hCpow : C.natAbs<2^(6+4*r) := by
    rw [Nat.pow_add]
    exact Nat.lt_trans hCsmall (Nat.mul_lt_mul_of_pos_left hNpow (by decide))
  have hrk : r≤r*k := by simpa using Nat.mul_le_mul_left r hk
  have hCpow2 : C.natAbs<2^(6+4*r*k) := Nat.lt_of_lt_of_le hCpow (Nat.pow_le_pow_right (by decide) (by rw [Nat.mul_assoc]; omega))
  have h3pow : 3^(2*r*k)<2^(4*r*k) := by
    rw [show 4*r*k=2*(2*r*k) by grind,Nat.pow_mul 2 2 (2*r*k)]
    exact Nat.pow_lt_pow_left (by decide : 3<2^2) (Nat.ne_of_gt (Nat.mul_pos (show 0<2*r by omega) (show 0<k by omega)))
  have hcoef : c.natAbs*3^(2*r*k) < 2^(6+4*r*k) := by
    have hle := Nat.mul_le_mul hc (Nat.le_of_lt h3pow)
    rw [Nat.pow_add]
    have hpos := Nat.two_pow_pos (4*r*k)
    omega
  have hpoly := Nat.mul_le_mul_left (2*r) (Nat.le_of_lt hcoef)
  have hsum : C.natAbs+2*r*c.natAbs*3^(2*r*k)<(2*r+1)*2^(6+4*r*k) := by
    rw [Nat.mul_assoc,Nat.add_mul,Nat.one_mul]
    omega
  have hpow := two_r_plus_one_le_pow r (by omega)
  have hsum2 := Nat.mul_le_mul_right (2^(6+4*r*k)) hpow
  rw [←Nat.pow_add] at hsum2
  have h9 : 2*r+(6+4*r*k)≤9*r*k := by
    rw [Nat.mul_assoc 4, Nat.mul_assoc 9]
    omega
  exact Nat.lt_of_lt_of_le hsum (Nat.le_trans hsum2 (Nat.pow_le_pow_right (by decide) h9))

/-- Uniform high-side exclusion for all the two target types. -/
theorem high_no_dvd (r m v : Nat) (C : Int)
    (hr : 8≤r) (hm : a r<m) (hmphys : m≤2*r*a r)
    (hv : v≤5) (hC : C.natAbs≤110*m+325)
    (hCne : C≠0) (hMne : C-(2:Int)^v*(N r:Int)≠0) :
    ¬denominator m∣value ((C,0)::sparse (a r) ((2:Int)^v) (2*r)) := by
  let B := 12*r+2
  let c := (2:Int)^v
  have hc : c.natAbs≤32 := by
    simp only [c,Int.natAbs_pow]
    exact Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hv
  have hAgap := a_ge_high_gap r hr
  have hA : (4*r+1)*B≤a r := hAgap
  have h2B : 2*B≤a r := by
    have h := Nat.mul_le_mul_right B (show 2≤4*r+1 by omega)
    omega
  intro hd
  by_cases hfar : a r+2*B≤m
  · have hmass0 := three_mass_bound r m c C hr hmphys hc hC
    have hmass : ∀ h<m, mass (rotate m h [(3*C,0),(C-c*(N r:Int),a r),(c,(2*r+1)*a r)])<2^B := by
      intro h hh
      have hmass1 : mass [(3*C,0),(C-c*(N r:Int),a r),(c,(2*r+1)*a r)]<2^(8*r) := by
        simp only [mass] at *
        omega
      have hbound := mass_rotate_lt m h ((2*r+1)*a r) (8*r) _ (by omega) hh (by
        intro t ht
        simp at ht
        rcases ht with rfl|rfl|rfl
        · simp
        · have h := Nat.mul_le_mul_right (a r) (show 1≤2*r+1 by omega); simpa using h
        · simp) hmass1
      have hceil : ((2*r+1)*a r+m-1)/m≤2*r+1 := by
        apply (Nat.div_le_iff_le_mul (show 0<m by omega)).mpr
        have hh := Nat.mul_le_mul_left (2*r+1) (Nat.le_of_lt hm)
        omega
      have he : 8*r+2*(((2*r+1)*a r+m-1)/m)≤B := by dsimp [B]; omega
      exact Nat.lt_of_lt_of_le hbound (Nat.pow_le_pow_right (by decide) he)
    have hD := sparse_to_three r m c C hd
    have he : value [(3*C,0),(C-c*(N r:Int),a r),(c,(2*r+1)*a r)]=value [(c,(2*r+1)*a r),(C-c*(N r:Int),a r),(3*C,0)] := by simp [value]; omega
    exact three_far_no_dvd m B (a r) ((2*r+1)*a r) (3*C) (C-c*(N r:Int)) c
      (by dsimp [B]; omega) h2B hfar (by omega) hMne hmass (by rwa [he])
  · let s := m-a r
    have hs : 0<s := by dsimp [s]; omega
    have hms : m=a r+s := by dsimp [s]; omega
    have hsB : s<2*B := by dsimp [s]; omega
    have hsize : B+2*r*s≤a r+s := by
      have hh := Nat.mul_le_mul_left (2*r) (Nat.le_of_lt hsB)
      have he : (4*r+1)*B=B+2*r*(2*B) := by grind
      rw [he] at hA
      omega
    have hv2 : v<2*r*s := by
      have hh := Nat.mul_le_mul_left (2*r) (show 1≤s by omega)
      omega
    have hmass := near_mass_bound r m c C hr hmphys hc hC
    have hmass2 : (1*(2:Int)^v).natAbs*3^(2*r)+C.natAbs<2^B := by
      simp only [Int.one_mul]
      exact Nat.lt_of_lt_of_le hmass (Nat.pow_le_pow_right (by decide) (by dsimp [B]; omega))
    have hnon := near_no_dvd (a r) s (2*r) B v 1 C hs (by omega) hv2 (by decide) hmass2 hsize
    simp only [Int.one_mul,←hms] at hnon
    exact hnon hd

/-- The low side above the new square-root threshold has an explicit
3-adic obstruction. This includes the unique large exceptional congruence. -/
theorem low_large_dvd (r m : Nat) (c C : Int)
    (hr : 8≤r) (hm : 0<m) (hma : m≤a r) (hbig : 16*r*a r≤m*m)
    (hc : c.natAbs≤32) (hC : C.natAbs≤110*m+325) (hCne : C≠0)
    (hd : denominator m∣value ((C,0)::sparse (a r) c (2*r))) :
    (3:Int)^(2*r+a r/m-1)∣C := by
  have hmphys : m≤2*r*a r := by
    have h := Nat.mul_le_mul_right (a r) (show 1≤2*r by omega)
    omega
  by_cases hfloor : 8*r≤a r/m
  · exfalso
    have hD := sparse_to_three r m c C hd
    have hmass := three_mass_bound r m c C hr hmphys hc hC
    have h := three_constant_dvd_or_small m ((2*r+1)*a r) (8*r) (a r) ((2*r+1)*a r) (a r)
      c (C-c*(N r:Int)) (3*C)
      (by have hh:=Nat.mul_le_mul_right (a r) (show 1≤2*r+1 by omega); omega) (by omega) (by omega)
      (by have hh:=Nat.mul_le_mul_right (a r) (show 1≤2*r+1 by omega); omega) hmass hD
    have hdiv := h.resolve_left (by have := threshold_mass r m hr hm hbig; omega)
    have hC3 : (3*C).natAbs<2^(8*r) := by simp only [mass] at hmass; omega
    have hpow : 2^(8*r)≤3^(a r/m) := Nat.le_trans (Nat.pow_le_pow_left (by decide : 2≤3) _) (Nat.pow_le_pow_right (by decide) hfloor)
    exact not_dvd_small ((3:Int)^(a r/m)) (3*C) (by omega)
      (by simp only [Int.natAbs_pow]; exact Nat.lt_of_lt_of_le hC3 hpow) hdiv
  · let k := (a r+m-1)/m
    let j := a r/m
    have hk := ceil_pos_of_le (a r) m hm hma
    have hj : 1≤j := by apply (Nat.le_div_iff_mul_le hm).mpr; omega
    have hja : j*m≤a r := Nat.div_mul_le_self _ _
    have hB : 0<9*r*k := Nat.mul_pos (by omega) (by omega)
    have hsize := low_many_gap r m hr hm hma (by omega)
    have hmass := low_mass_bound r m k c C hr hma hk hc hC
    exact sparse_constant_dvd (a r) m (2*r) (9*r*k) j c C hm hB hj hja hsize hmass hd



#print axioms high_no_dvd
#print axioms low_large_dvd
end NeedleRotation.CancellationWide
