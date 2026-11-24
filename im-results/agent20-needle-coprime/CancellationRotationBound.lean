import RotationNear

namespace NeedleRotation.Cancellation

def N (r : Nat) : Nat := 9^r
def a (r : Nat) : Nat := (N r+5)/2

theorem N_odd (r : Nat) : N r % 2=1 := by
  induction r with
  | zero => decide
  | succ r ih => simp only [N,Nat.pow_succ] at *; rw [Nat.mul_mod,ih]

theorem a_spec (r : Nat) : 2*a r=N r+5 := by
  have h := N_odd r
  unfold a
  omega

theorem N_pos (r : Nat) : 0<N r := Nat.pow_pos (by decide)

theorem N_lt_pow (r : Nat) (hr : 0<r) : N r < 2^(4*r) := by
  unfold N
  rw [Nat.pow_mul]
  exact Nat.pow_lt_pow_left (by decide : 9<2^4) (by omega)

theorem a_le_N (r : Nat) (hr : 1≤r) : a r≤N r := by
  have hp : 9≤N r := Nat.pow_le_pow_right (by decide : 0<(9:Nat)) hr
  have hs := a_spec r
  omega

theorem a_succ (r : Nat) : a (r+1)+20=9*a r := by
  have h1 := a_spec r
  have h2 := a_spec (r+1)
  have hN : N (r+1)=9*N r := by simp [N,Nat.pow_succ,Nat.mul_comm]
  omega

theorem pow4_succ_le (r : Nat) (hr : 3≤r) : (r+1)^4≤4*r^4 := by
  have hmul : 3*r≤r*r := Nat.mul_le_mul_right r hr
  have hsq : (r+1)^2≤2*r^2 := by
    simp only [Nat.pow_two,Nat.add_mul,Nat.mul_add,Nat.mul_one,Nat.one_mul]
    omega
  have h := Nat.pow_le_pow_left hsq 2
  rw [←Nat.pow_mul,Nat.mul_pow,←Nat.pow_mul] at h
  exact h

theorem a_growth_aux (t : Nat) : 1728*(8+t)^4≤a (8+t) := by
  induction t with
  | zero => decide
  | succ t ih =>
    have hpoly := pow4_succ_le (8+t) (by omega)
    have hlarge : 20≤a (8+t) := by
      have hp : 1≤(8+t)^4 := Nat.pow_pos (by omega)
      omega
    have ha := a_succ (8+t)
    have hmul := Nat.mul_le_mul_left 1728 hpoly
    have hmul2 := Nat.mul_le_mul_left 4 ih
    rw [←Nat.mul_assoc,show 1728*4=4*1728 by decide,Nat.mul_assoc] at hmul
    change 1728*(8+t+1)^4≤a (8+t+1)
    omega

theorem a_growth (r : Nat) (hr : 8≤r) : 1728*r^4≤a r := by
  have h := a_growth_aux (r-8)
  rwa [Nat.add_sub_of_le hr] at h

theorem a_ge_1024r (r : Nat) (hr : 8≤r) : 1024*r≤a r := by
  have hp : r≤r^4 := by
    have h := Nat.pow_le_pow_right (by omega : 0<r) (show 1≤4 by decide)
    simpa using h
  have h := a_growth r hr
  omega

theorem a_ge_low_gap (r : Nat) (hr : 8≤r) : 576*r^3*(2*r+1)≤a r := by
  have hsmall : 2*r+1≤3*r := by omega
  have h := Nat.mul_le_mul_left (576*r^3) hsmall
  have he : 576*r^3*(3*r)=1728*r^4 := by
    rw [show r^4=r^3*r by rw [Nat.pow_succ]]
    grind
  rw [he] at h
  exact Nat.le_trans h (a_growth r hr)

theorem r_le_two_pow (r : Nat) : r≤2^r := by
  induction r with
  | zero => decide
  | succ r ih =>
    rw [Nat.pow_succ]
    have hp := Nat.two_pow_pos r
    omega

theorem two_r_plus_one_le_pow (r : Nat) (hr : 1≤r) : 2*r+1≤2^(2*r) := by
  have h := r_le_two_pow r
  have hp := Nat.two_pow_pos r
  have h2 : 2≤2^r := by exact Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hr
  have hh := Nat.mul_le_mul_right (2^r) h2
  rw [show 2*r=r+r by omega,Nat.pow_add]
  by_cases h3 : r=1
  · subst r; decide
  have h3' : 3≤2^r := by
    have hx : 4≤2^r := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (show 2≤r by omega)
    omega
  have hmul := Nat.mul_le_mul_right (2^r) h3'
  omega

/-- The signed geometric numerator is the source-equation numerator. -/
theorem source_sparse (r : Nat) (P c : Int)
    (hP : ((2:Int)^(a r)+3)*P+(N r:Int)=((2:Int)^(a r))^(2*r)) :
    value (sparse (a r) c (2*r))=c*2^(a r)*P := by
  have h := sparse_identity (a r) (2*r) c
  have hN : (-3:Int)^(2*r)=(N r:Int) := by rw [Int.pow_mul]; simp [N,Int.natCast_pow]
  rw [hN,show (2*r+1)*a r=2*r*a r+a r by rw [Nat.add_mul,Nat.one_mul],Int.pow_add,Nat.mul_comm (2*r),Int.pow_mul] at h
  have he : ((2:Int)^(a r)+3)*(value (sparse (a r) c (2*r))-c*2^(a r)*P)=0 := by grind
  have hnon : (2:Int)^(a r)+3≠0 := by have hp := Int.pow_pos (by decide : (0:Int)<2) (m:=a r); omega
  have hh := (Int.mul_eq_zero.mp he).resolve_left hnon
  omega


/-- Multiplying by 2^a+3 collapses the signed polynomial to three terms. -/
theorem sparse_to_three (r m : Nat) (c C : Int)
    (hd : denominator m∣value ((C,0)::sparse (a r) c (2*r))) :
    denominator m∣value [(c,(2*r+1)*a r),(C-c*(N r:Int),a r),(3*C,0)] := by
  have hs := sparse_identity (a r) (2*r) c
  have hN : (-3:Int)^(2*r)=(N r:Int) := by rw [Int.pow_mul]; simp [N,Int.natCast_pow]
  rw [hN] at hs
  have hh : denominator m∣((2:Int)^(a r)+3)*value ((C,0)::sparse (a r) c (2*r)) := Int.dvd_mul_of_dvd_right hd
  have he : ((2:Int)^(a r)+3)*value ((C,0)::sparse (a r) c (2*r)) = value [(c,(2*r+1)*a r),(C-c*(N r:Int),a r),(3*C,0)] := by
    simp only [value,Int.pow_zero,Int.mul_one,Int.add_zero,Int.mul_add]
    grind
  rwa [he] at hh

theorem N_ge_81 (r : Nat) (hr : 2≤r) : 81≤N r := Nat.pow_le_pow_right (by decide : 0<(9:Nat)) hr

theorem scale_mass_lt (r : Nat) (hr : 8≤r) : 2048*r*N r<2^(8*r) := by
  have hN := N_lt_pow r (by omega)
  have h := Nat.mul_lt_mul_of_pos_left hN (show 0<2048*r by omega)
  have hrpow := r_le_two_pow r
  have h2 := Nat.mul_le_mul_right (2^(4*r)) (Nat.mul_le_mul_left 2048 hrpow)
  have he : 2048*2^r*2^(4*r)=2^(11+5*r) := by
    rw [show 2048=2^11 by decide,←Nat.pow_add,←Nat.pow_add,show 11+r+4*r=11+5*r by omega]
  rw [he] at h2
  exact Nat.lt_of_lt_of_le h (Nat.le_trans h2 (Nat.pow_le_pow_right (by decide) (by omega)))

theorem three_mass_bound (r m : Nat) (c C : Int)
    (hr : 8≤r) (hm : m≤2*r*a r) (hc : c.natAbs≤16) (hC : C.natAbs≤110*m+325) :
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
    (hr : 8≤r) (hm : m≤2*r*a r) (hc : c.natAbs≤16) (hC : C.natAbs≤110*m+325) :
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
    (hr : 8≤r) (hm : m≤a r) (hk : 1≤k) (hc : c.natAbs≤16) (hC : C.natAbs≤110*m+325) :
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

theorem a_ge_high_gap (r : Nat) (hr : 8≤r) : (4*r+1)*(12*r+2)≤a r := by
  have h1 : 4*r+1≤5*r := by omega
  have h2 : 12*r+2≤14*r := by omega
  have hmul := Nat.mul_le_mul h1 h2
  have he : 5*r*(14*r)=70*r^2 := by simp only [Nat.pow_two]; grind
  rw [he] at hmul
  have hp := Nat.pow_le_pow_right (by omega : 0<r) (show 2≤4 by decide)
  have h := a_growth r hr
  omega


/-- The new threshold is proportional to sqrt(r*a), not r*sqrt(a). -/
theorem threshold_mass (r m : Nat) (hr : 8≤r) (hm : 0<m)
    (hbig : 16*r*a r≤m*m) :
    3*(8*r+2*(((2*r+1)*a r+m-1)/m))≤m := by
  let E := (2*r+1)*a r
  let Q := (E+m-1)/m
  have hA := a_ge_1024r r hr
  have hs := Nat.mul_le_mul_left (16*r) hA
  have h128 : 128*r≤m := by
    by_cases h : 128*r≤m
    · exact h
    have hlt := Nat.mul_self_lt_mul_self (show m<128*r by omega)
    have he : (128*r)*(128*r)=16*r*(1024*r) := by grind
    rw [he] at hlt
    omega
  have hQ : Q*m≤E+m-1 := Nat.div_mul_le_self _ _
  have hE : 4*(6*E)≤51*(r*a r) := by
    have hh := Nat.mul_le_mul_right (a r) (show 24*(2*r+1)≤51*r by omega)
    dsimp [E]
    rw [show 4*(6*((2*r+1)*a r))=24*(2*r+1)*a r by grind,show 51*(r*a r)=51*r*a r by grind]
    exact hh
  have hleft := Nat.mul_le_mul_right m (show 128*r≤m from h128)
  have hleft2 : 128*(25*r*m)≤25*(m*m) := by
    have hh := Nat.mul_le_mul_left 25 hleft
    rw [show 128*(25*r*m)=25*((128*r)*m) by grind]
    exact hh
  have hright : 128*(6*E)≤102*(m*m) := by
    have hh := Nat.mul_le_mul_left 32 hE
    have hh2 := Nat.mul_le_mul_left 102 hbig
    rw [show 32*(4*(6*E))=128*(6*E) by grind,show 32*(51*(r*a r))=102*(16*r*a r) by grind] at hh
    exact Nat.le_trans hh hh2
  have hmid : (24*r+6*Q)*m≤25*r*m+6*E := by
    have h6 := Nat.mul_le_mul_right m (show 6≤r by omega)
    rw [Nat.add_mul,Nat.mul_assoc 24,Nat.mul_assoc 6,Nat.mul_assoc 25] at *
    omega
  have hlarge := Nat.mul_le_mul_left 128 hmid
  rw [Nat.mul_add] at hlarge
  have htotal : 128*((24*r+6*Q)*m)≤127*(m*m) := by omega
  change 3*(8*r+2*Q)≤m
  by_cases h : 24*r+6*Q≤m
  · omega
  have hlt := Nat.mul_lt_mul_of_pos_right (show m<24*r+6*Q by omega) hm
  have hlt2 := Nat.mul_lt_mul_of_pos_left hlt (show 0<128 by decide)
  omega

theorem ceil_le_of_floor_lt (a m K : Nat) (hm : 0<m) (h : a/m<K) : (a+m-1)/m≤K := by
  apply (Nat.div_le_iff_le_mul hm).mpr
  have hh := (Nat.div_lt_iff_lt_mul hm).mp h
  omega

theorem low_many_gap (r m : Nat) (hr : 8≤r) (hm : 0<m)
    (hma : m≤a r) (hfloor : a r/m<8*r) :
    (2*r+1)*(9*r*((a r+m-1)/m))≤m := by
  let k := (a r+m-1)/m
  have hk := ceil_le_of_floor_lt (a r) m (8*r) hm hfloor
  have hmul := (Nat.div_lt_iff_lt_mul hm).mp hfloor
  have hA := a_ge_low_gap r hr
  have he : 8*r*((2*r+1)*(9*r*(8*r)))=576*r^3*(2*r+1) := by simp only [Nat.pow_succ,Nat.pow_zero,Nat.one_mul]; grind
  have hsmall : (2*r+1)*(9*r*(8*r))≤m := by
    by_cases h : (2*r+1)*(9*r*(8*r))≤m
    · exact h
    have hh := Nat.mul_lt_mul_of_pos_left (show m<(2*r+1)*(9*r*(8*r)) by omega) (show 0<8*r by omega)
    rw [he] at hh
    omega
  exact Nat.le_trans (Nat.mul_le_mul_left (2*r+1) (Nat.mul_le_mul_left (9*r) hk)) hsmall

theorem ceil_pos_of_le (a m : Nat) (hm : 0<m) (hma : m≤a) : 1≤(a+m-1)/m := by
  apply (Nat.le_div_iff_mul_le hm).mpr
  omega

theorem denominator_positive (m : Nat) : 0<denominator m := by
  have h := Int.pow_pos (by decide : (0:Int)<2) (m:=m)
  unfold denominator
  omega

theorem not_dvd_small (D C : Int) (hC : C≠0) (h : C.natAbs<D.natAbs) : ¬D∣C := by
  intro hd
  exact hC (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd h)

/-- Uniform high-side exclusion for all the two target types. -/
theorem high_no_dvd (r m v : Nat) (C : Int)
    (hr : 8≤r) (hm : a r<m) (hmphys : m≤2*r*a r)
    (hv : v≤4) (hC : C.natAbs≤110*m+325)
    (hCne : C≠0) (hMne : C-(2:Int)^v*(N r:Int)≠0) :
    ¬denominator m∣value ((C,0)::sparse (a r) ((2:Int)^v) (2*r)) := by
  let B := 12*r+2
  let c := (2:Int)^v
  have hc : c.natAbs≤16 := by
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
    (hc : c.natAbs≤16) (hC : C.natAbs≤110*m+325) (hCne : C≠0)
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


theorem three_pow_even (r : Nat) : (3:Int)^(2*r)=(N r:Int) := by rw [Int.pow_mul]; simp [N,Int.natCast_pow]

theorem N_dvd_of_large (r m : Nat) (C : Int) (hm : 0<m) (hma : m≤a r)
    (hd : (3:Int)^(2*r+a r/m-1)∣C) : (N r:Int)∣C := by
  have hj : 1≤a r/m := (Nat.le_div_iff_mul_le hm).mpr (by simpa using hma)
  rw [←three_pow_even]
  have h : (3:Int)^(2*r)∣(3:Int)^(2*r+a r/m-1) := by
    apply Int.natAbs_dvd_natAbs.mp
    simp only [Int.natAbs_pow]
    exact Nat.pow_dvd_pow 3 (by omega)
  exact Int.dvd_trans h hd

theorem geom_zero (n : Nat) : geom 0 n=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [geom,ih,Nat.add_comm]

theorem at_a_no_dvd (r : Nat) (hr : 8≤r) :
    ¬ denominator (a r)∣value ((-(N r:Int),0)::sparse (a r) 1 (2*r)) := by
  intro hd
  have h := near_congruence (a r) 0 (2*r) 1
  simp only [Nat.add_zero,Nat.mul_zero,Int.pow_zero,Int.one_mul,geom_zero,three_pow_even] at h
  have hn : (-3:Int)^(2*r)=(N r:Int) := by rw [Int.pow_mul]; simp [N,Int.natCast_pow]
  rw [hn] at h
  have hD : denominator (a r)∣(N r:Int)*((2*r:Nat):Int)-(N r:Int) := by
    have hsub := Int.dvd_sub hd h
    simp only [value,Int.pow_zero,Int.mul_one] at hsub
    have he : -(N r:Int)+value (sparse (a r) 1 (2*r))-(value (sparse (a r) 1 (2*r))-(N r:Int)*((2*r:Nat):Int)) = (N r:Int)*((2*r:Nat):Int)-(N r:Int) := by omega
    rwa [he] at hsub
  have hN := N_pos r
  have hpos : 0<N r*(2*r-1) := Nat.mul_pos hN (by omega)
  have hprod : (N r:Int)*((2*r:Nat):Int)-(N r:Int)=(N r*(2*r-1):Nat) := by
    simp only [Int.natCast_mul,Int.natCast_sub (show 1≤2*r by omega)]
    grind
  rw [hprod] at hD
  have hsize : N r*(2*r-1)<2^(a r)+3 := by
    have hNpow := N_lt_pow r (by omega)
    have hrpow := two_r_plus_one_le_pow r (by omega)
    have hmul := Nat.mul_lt_mul_of_pos_right hNpow (show 0<2*r by omega)
    have hmul2 := Nat.mul_le_mul_left (2^(4*r)) (show 2*r≤2^(2*r) by omega)
    rw [←Nat.pow_add] at hmul2
    have hpow := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (show 4*r+2*r≤a r by have := a_ge_1024r r hr; omega)
    have hsm := Nat.mul_le_mul_left (N r) (show 2*r-1≤2*r by omega)
    omega
  have hden : (denominator (a r)).natAbs=2^(a r)+3 := by simp [denominator,Int.natAbs_pow,Int.natAbs_add_of_nonneg,Int.pow_nonneg]
  exact not_dvd_small (denominator (a r)) (N r*(2*r-1):Nat) (by exact_mod_cast (show N r*(2*r-1)≠0 by omega))
    (by rw [Int.natAbs_natCast,hden]; exact hsize) hD

/-- First cancellation feeder, all r>=8: the sharpened universal bound. -/
theorem first_cutoff (r m : Nat) (hr : 8≤r) (hm : 0<m) (hmphys : m≤2*r*a r)
    (hd : denominator m∣value ((5-2*(m:Int),0)::sparse (a r) 1 (2*r))) :
    m*m<16*r*a r := by
  let C : Int := 5-2*(m:Int)
  have hC : C.natAbs≤110*m+325 := by dsimp [C]; omega
  have hCne : C≠0 := by dsimp [C]; omega
  have hMne : C-(2:Int)^0*(N r:Int)≠0 := by have := N_ge_81 r (by omega); dsimp [C]; omega
  have hd' : denominator m∣value ((C,0)::sparse (a r) ((2:Int)^0) (2*r)) := hd
  by_cases hma : m≤a r
  · by_cases hsmall : m*m<16*r*a r
    · exact hsmall
    exfalso
    have hD := low_large_dvd r m 1 C hr hm hma (by omega) (by decide) hC hCne hd
    have hN := N_dvd_of_large r m C hm hma hD
    have ha := a_spec r
    have hNlarge := N_ge_81 r (by omega)
    by_cases hlt : m<a r
    · exact not_dvd_small (N r:Int) C hCne (by rw [Int.natAbs_natCast]; dsimp [C]; omega) hN
    · have he : m=a r := by omega
      have hCeq : C=-(N r:Int) := by dsimp [C]; omega
      have hd'' : denominator (a r)∣value ((-(N r:Int),0)::sparse (a r) 1 (2*r)) := by simpa only [←hCeq,←he] using hd
      exact at_a_no_dvd r hr hd''
  · exact False.elim (high_no_dvd r m 0 C hr (by omega) hmphys (by decide) hC hCne hMne hd')

theorem N_mod22 (j : Nat) : N (110*j+50)%22=1 := by
  unfold N
  rw [show 110*j+50=5*(22*j+10) by omega,Nat.pow_mul]
  have h (k : Nat) : ((9:Nat)^5)^k%22=1 := by
    induction k with
    | zero => decide
    | succ k ih => rw [Nat.pow_succ,Nat.mul_mod,ih]
  exact h _

/-- Second-level valuation-two/odd ancestor, all r=110j+50. -/
theorem second_cutoff (j m : Nat) (hm : 0<m) (hmphys : m≤2*(110*j+50)*a (110*j+50))
    (hd : denominator m∣value ((325-110*(m:Int),0)::sparse (a (110*j+50)) 16 (2*(110*j+50)))) :
    m*m<16*(110*j+50)*a (110*j+50) := by
  let r := 110*j+50
  let C : Int := 325-110*(m:Int)
  have hr : 8≤r := by dsimp [r]; omega
  have hC : C.natAbs≤110*m+325 := by dsimp [C]; omega
  have hCne : C≠0 := by dsimp [C]; omega
  have hMne : C-(2:Int)^4*(N r:Int)≠0 := by dsimp [C]; omega
  have hd' : denominator m∣value ((C,0)::sparse (a r) ((2:Int)^4) (2*r)) := hd
  change m*m<16*r*a r
  by_cases hma : m≤a r
  · by_cases hsmall : m*m<16*r*a r
    · exact hsmall
    exfalso
    have hD := low_large_dvd r m 16 C hr hm hma (by omega) (by decide) hC hCne hd
    have hN := N_dvd_of_large r m C hm hma hD
    have hfive : (N r:Int)∣5*(65-22*(m:Int)) := by
      rw [show 5*(65-22*(m:Int))=C by dsimp [C]; omega]
      exact hN
    have hNat := Int.natAbs_dvd_natAbs.mpr hfive
    simp only [Int.natAbs_natCast,Int.natAbs_mul] at hNat
    have hcop : (N r).Coprime 5 := (by decide : (9:Nat).Coprime 5).pow_left r
    have hdiv : (N r:Int)∣22*(m:Int)-65 := by
      apply Int.natAbs_dvd_natAbs.mp
      have h := hcop.dvd_of_dvd_mul_left hNat
      have he : 22*(m:Int)-65=-(65-22*(m:Int)) := by omega
      simpa only [he,Int.natAbs_neg,Int.natAbs_natCast] using h
    obtain ⟨t,ht⟩ := hdiv
    have hNpos : 0<(N r:Int) := by exact_mod_cast N_pos r
    have hNlarge := N_ge_81 r (by omega)
    have ha := a_spec r
    have hlow : -(N r:Int)<22*(m:Int)-65 := by omega
    have hhigh : 22*(m:Int)-65<11*(N r:Int) := by omega
    have ht0 : 0≤t := by
      by_cases h : 0≤t
      · exact h
      have hmul := Int.mul_le_mul_of_nonneg_left (show t≤-1 by omega) (Int.le_of_lt hNpos)
      simp only [Int.mul_neg,Int.mul_one] at hmul
      omega
    have ht10 : t≤10 := by
      by_cases h : t≤10
      · exact h
      have hmul := Int.mul_le_mul_of_nonneg_left (show 11≤t by omega) (Int.le_of_lt hNpos)
      rw [Int.mul_comm (N r:Int) 11] at hmul
      omega
    have hNmod : (N r:Int)%22=1 := by exact_mod_cast N_mod22 j
    have hmod := congrArg (fun x : Int => x%22) ht
    change (22*(m:Int)-65)%22=((N r:Int)*t)%22 at hmod
    rw [Int.mul_emod,hNmod,Int.one_mul,Int.emod_emod] at hmod
    have ht1 : t=1 := by omega
    rw [ht1,Int.mul_one] at ht
    have hCeq : C= -5*(N r:Int) := by dsimp [C]; omega
    have h2m : 2*m≤a r := by omega
    have hj : 2≤a r/m := (Nat.le_div_iff_mul_le hm).mpr h2m
    have hpow : (3:Int)^(2*r+1)∣(3:Int)^(2*r+a r/m-1) := by
      apply Int.natAbs_dvd_natAbs.mp
      simp only [Int.natAbs_pow]
      exact Nat.pow_dvd_pow 3 (by omega)
    have h3N := Int.dvd_trans hpow hD
    rw [Int.pow_succ,three_pow_even,hCeq] at h3N
    have hNat2 := Int.natAbs_dvd_natAbs.mpr h3N
    simp only [Int.natAbs_mul,Int.natAbs_natCast] at hNat2
    have hNat3 : N r*3∣N r*5 := by simpa [Nat.mul_comm] using hNat2
    exact (by decide : ¬(3:Nat)∣5) (Nat.dvd_of_mul_dvd_mul_left (N_pos r) hNat3)
  · exact False.elim (high_no_dvd r m 4 C hr (by omega) hmphys (by decide) hC hCne hMne hd')

/-- Physical inverse equation in shifted coordinates. -/
def parentEq (b q w : Nat) : Prop :=
  b=(2^(w+1)+3)*q+3*2^w+w+3

theorem parent_int_dvd (b q w : Nat) (h : parentEq b q w) :
    denominator (w+1) ∣ 2*(b:Int)+5-2*((w+1:Nat):Int) := by
  refine ⟨(2*(q:Int)+3),?_⟩
  unfold parentEq at h
  have hInt : (b:Int)=((2:Int)^(w+1)+3)*(q:Int)+3*(2:Int)^w+(w:Int)+3 := by exact_mod_cast h
  have hp : (2:Int)^(w+1)=2*(2:Int)^w := by rw [Int.pow_succ,Int.mul_comm]
  unfold denominator
  simp only [Int.natCast_add]
  grind

theorem parent_pow_lt (b q w : Nat) (h : parentEq b q w) : 2^(w+1)<b := by
  unfold parentEq at h
  have hp := Nat.two_pow_pos w
  rw [Nat.pow_succ]
  omega

theorem feeder_AP_lt (r P : Nat)
    (hP : (2^(a r)+3)*P+N r=(2^(a r))^(2*r)) :
    2^(a r)*P<2^(2*r*a r) := by
  rw [←Nat.pow_mul, Nat.mul_comm (a r) (2*r)] at hP
  rw [Nat.add_mul] at hP
  have hn := N_pos r
  omega

theorem physical_m_bound (r b q w : Nat) (hb : b<2^(2*r*a r)) (hp : parentEq b q w) :
    w+1≤2*r*a r := by
  have hpow := parent_pow_lt b q w hp
  by_cases h : w+1≤2*r*a r
  · exact h
  have hmono := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (show 2*r*a r≤w+1 by omega)
  omega

/-- All-r>=8 cutoff, stated directly on the exact original-source parent
    equation for the constructed cancellation feeder. -/
theorem first_source_equation_cutoff (r P b q w : Nat) (hr : 8≤r)
    (hP : (2^(a r)+3)*P+N r=(2^(a r))^(2*r))
    (hb : 2*b=2^(a r)*P) (hp : parentEq b q w) :
    (w+1)*(w+1)<16*r*a r := by
  have hAP := feeder_AP_lt r P hP
  have hphys := physical_m_bound r b q w (by omega) hp
  have hPint : ((2:Int)^(a r)+3)*(P:Int)+(N r:Int)=((2:Int)^(a r))^(2*r) := by exact_mod_cast hP
  have hs := source_sparse r (P:Int) 1 hPint
  have hd := parent_int_dvd b q w hp
  have hbInt : 2*(b:Int)=(2:Int)^(a r)*(P:Int) := by exact_mod_cast hb
  apply first_cutoff r (w+1) hr (by omega) hphys
  simp only [value,Int.pow_zero,Int.mul_one,hs,Int.one_mul]
  have he : 5-2*((w+1:Nat):Int)+((2:Int)^(a r))*(P:Int)=2*(b:Int)+5-2*((w+1:Nat):Int) := by omega
  rwa [he]

/-- All members of the second-level progression, directly on the exact
    source parent equation, including its physical valuation range. -/
theorem second_source_equation_cutoff (j P b q w : Nat)
    (hP : (2^(a (110*j+50))+3)*P+N (110*j+50)=(2^(a (110*j+50)))^(2*(110*j+50)))
    (hb : 55*b=8*2^(a (110*j+50))*P+25) (hp : parentEq b q w) :
    (w+1)*(w+1)<16*(110*j+50)*a (110*j+50) := by
  let r:=110*j+50
  have hAP := feeder_AP_lt r P hP
  have hbig : 1≤2^(2*r*a r) := Nat.two_pow_pos _
  have hb' : b<2^(2*r*a r) := by
    change 55*b=8*2^(a r)*P+25 at hb
    rw [Nat.mul_assoc] at hb
    omega
  have hphys := physical_m_bound r b q w hb' hp
  have hPint : ((2:Int)^(a r)+3)*(P:Int)+(N r:Int)=((2:Int)^(a r))^(2*r) := by exact_mod_cast hP
  have hs := source_sparse r (P:Int) 16 hPint
  have hd := parent_int_dvd b q w hp
  have hD : denominator (w+1)∣55*(2*(b:Int)+5-2*((w+1:Nat):Int)) := Int.dvd_mul_of_dvd_right hd
  have hbInt : 55*(b:Int)=8*(2:Int)^(a r)*(P:Int)+25 := by exact_mod_cast hb
  apply second_cutoff j (w+1) (by omega) hphys
  change denominator (w+1)∣value ((325-110*((w+1:Nat):Int),0)::sparse (a r) 16 (2*r))
  simp only [value,Int.pow_zero,Int.mul_one,hs]
  have he : 325-110*((w+1:Nat):Int)+16*(2:Int)^(a r)*(P:Int)=55*(2*(b:Int)+5-2*((w+1:Nat):Int)) := by
    rw [Int.mul_assoc 16,Int.mul_assoc 8] at *
    omega
  rwa [he]

#print axioms first_source_equation_cutoff
#print axioms second_source_equation_cutoff
#print axioms first_cutoff
#print axioms second_cutoff
end NeedleRotation.Cancellation
