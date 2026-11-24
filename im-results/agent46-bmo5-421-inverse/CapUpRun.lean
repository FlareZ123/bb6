import CapStrip
namespace CapSieve

/-- Upper end of W in a band. -/
def Wmax (j : Nat) : Int := 4*(P j:Int)-2*(j:Int)-15

theorem p_ge_one {j : Nat} (hj : 1≤j) : j+7≤P j := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases h : j=0
    · subst j; decide
    · have hh:=ih (by omega)
      rw [p_succ]; omega

theorem wmax_growth {j : Nat} (hj : 1≤j) : Wmax (j+1)≤3*Wmax j := by
  have hp:=p_ge_one hj
  unfold Wmax
  rw [p_succ]
  omega

theorem wmax_power {j : Nat} (hj : 1≤j) (n : Nat) : Wmax (j+n)≤(3^n:Int)*Wmax j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs:=wmax_growth (j:=j+n) (by omega)
    have h : j+(n+1)=j+n+1 := by omega
    rw [h,Int.pow_succ]
    have he : (3^n:Int)*3*Wmax j=3*((3^n:Int)*Wmax j) := by grind
    rw [he]
    omega

theorem lower_growth (j n : Nat) : 2*(j+n)+7≤3^n*(2*j+7) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.pow_succ,Nat.mul_assoc,show 3*(2*j+7)=(2*j+7)*3 by omega,←Nat.mul_assoc]
    omega

theorem regular_lower_growth {j : Nat} (hj : 1≤j) (n : Nat) :
    2*(j+(n+1))+7<3^(n+1)*(2*j+3) := by
  induction n with
  | zero => simp; omega
  | succ n ih =>
    rw [Nat.pow_succ,Nat.mul_assoc,show 3*(2*j+3)=(2*j+3)*3 by omega,←Nat.mul_assoc]
    omega

theorem band_of_w_bounds {j x : Nat}
    (hl : -(2*(j:Int)+7)≤W j x) (hh : W j x≤Wmax j) : Band j x := by
  have h:=l_add j
  have h':=l_add (j+1)
  rw [p_succ] at h'
  unfold W Wmax at *
  unfold Band
  omega

theorem w_of_band {j x : Nat} (h : Band j x) :
    -(2*(j:Int)+7)≤W j x ∧ W j x≤Wmax j := w_bounds h

/-- Exact all-sign, all-length regular one-band run characterization, above
    band zero. The endpoint inequalities force every intermediate edge. -/
theorem up_run_of_w {j n x y : Nat} (hj : 1≤j) (hx : Band j x) (hy : Band (j+n) y)
    (hw : W (j+n) y=(3^n:Int)*W j x) : UpRun j n x y := by
  induction n generalizing j x with
  | zero =>
    simp at hw hy ⊢
    have he : x=y := by unfold W at hw; omega
    subst y; exact .zero hx
  | succ n ih =>
    have hpow : 0<(3^(n+1):Int) := Int.pow_pos (by decide)
    have hb:=(w_of_band hy).1
    have hg : (2*((j+(n+1):Nat):Int)+7)<(3^(n+1):Int)*(2*(j:Int)+3) := by exact_mod_cast regular_lower_growth hj n
    have hregular : -(2*(j:Int)+3)<W j x := by
      by_cases h : -(2*(j:Int)+3)<W j x
      · exact h
      · have hh:=Int.mul_le_mul_of_nonneg_left (show W j x≤ -(2*(j:Int)+3) by omega) (Int.le_of_lt hpow)
        rw [Int.mul_neg] at hh
        omega
    let r:=x-L j
    have he : x=L j+r := by dsimp [r]; have := hx.1; omega
    have hr : r+4≤P j := by have hl:=l_add j; unfold W at hregular; dsimp [r]; omega
    let z:=3*r+P j+3
    have hreg : RegFrom j x z := ⟨r,hr,he,rfl⟩
    have hzW:=w_regular_down hreg
    have hy' : Band (j+1+n) y := by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hy
    have hw' : W (j+1+n) y=(3^n:Int)*W (j+1) z := by
      rw [hzW,←Int.mul_assoc,←Int.pow_succ]
      rw [show j+1+n=j+(n+1) by omega,hw]
    have hp : 0<(3^n:Int) := Int.pow_pos (by decide)
    have hlo := (w_of_band hy').1
    have hhi := (w_of_band hy').2
    have hGlo : (2*((j+1+n:Nat):Int)+7)≤(3^n:Int)*(2*((j+1:Nat):Int)+7) := by exact_mod_cast lower_growth (j+1) n
    have hGhi := wmax_power (j:=j+1) (by omega) n
    have hzlo : -(2*((j+1:Nat):Int)+7)≤W (j+1) z := by
      by_cases h : -(2*((j+1:Nat):Int)+7)≤W (j+1) z
      · exact h
      · have hh:=Int.mul_lt_mul_of_pos_left (show W (j+1) z< -(2*((j+1:Nat):Int)+7) by omega) hp
        rw [Int.mul_neg] at hh
        omega
    have hzhi : W (j+1) z≤Wmax (j+1) := by
      by_cases h : W (j+1) z≤Wmax (j+1)
      · exact h
      · have hh:=Int.mul_lt_mul_of_pos_left (show Wmax (j+1)<W (j+1) z by omega) hp
        omega
    have hzband:=band_of_w_bounds hzlo hzhi
    exact .head hreg (ih (by omega) hzband hy' hw')

theorem up_run_iff {j n x y : Nat} (hj : 1≤j) : UpRun j n x y ↔
    Band j x ∧ Band (j+n) y ∧ W (j+n) y=(3^n:Int)*W j x := by
  constructor
  · intro h; exact ⟨(up_run_bands h).1,(up_run_bands h).2,up_run_w h⟩
  · rintro ⟨hx,hy,hw⟩; exact up_run_of_w hj hx hy hw

theorem w_mod4 (j x : Nat) : W j x%4=(2*(j:Int)+1)%4 := by unfold W; omega

theorem wmax_mod4 (j : Nat) : Wmax j%4=(2*(j:Int)+1)%4 := by unfold Wmax; omega

theorem pow3_mod4_int (n : Nat) : (3^n:Int)%4=if n%2=0 then 1 else 3 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Int.pow_succ,Int.mul_emod,ih]
    split <;> rename_i h
    · have h' : (n+1)%2≠0 := by omega
      simp [h']
    · have h' : (n+1)%2=0 := by omega
      simp [h']

/-- All possible W values in one band, including the exceptional top two. -/
theorem w_realize {j : Nat} {w : Int} (hlo : -(2*(j:Int)+7)≤w) (hhi : w≤Wmax j)
    (hmod : w%4=(2*(j:Int)+1)%4) : ∃ x, Band j x ∧ W j x=w := by
  let q:=(Wmax j-w)/4
  have hq : 4*q=Wmax j-w := by have hh:=wmax_mod4 j; dsimp [q]; omega
  have hqpos : 0≤q := by omega
  let x:=L j+q.toNat
  have hxq : (q.toNat:Int)=q := Int.toNat_of_nonneg hqpos
  have hW : W j x=w := by
    have hl:=l_add j
    unfold W Wmax at *
    dsimp [x]
    omega
  exact ⟨x,band_of_w_bounds (by rw [hW]; exact hlo) (by rw [hW]; exact hhi),hW⟩

/-- Every 3-power divisor of W gives an authentic inverse descent run, as
    long as its bottom band is positive. No intermediate range tests remain. -/
theorem up_run_exists {j n y : Nat} (hj : 1≤j) (hy : Band (j+n) y) :
    (∃ x, UpRun j n x y) ↔ (3^n:Int) ∣ W (j+n) y := by
  constructor
  · rintro ⟨x,h⟩; exact ⟨W j x,up_run_w h⟩
  · rintro ⟨w,hw⟩
    have hp : 0<(3^n:Int) := Int.pow_pos (by decide)
    have hGhi:=wmax_power hj n
    have hGlo : (2*((j+n:Nat):Int)+7)≤(3^n:Int)*(2*(j:Int)+7) := by exact_mod_cast lower_growth j n
    have hb:=w_of_band hy
    have hhi : w≤Wmax j := by
      by_cases h : w≤Wmax j
      · exact h
      · have hm:=Int.mul_lt_mul_of_pos_left (show Wmax j<w by omega) hp
        omega
    have hlo : -(2*(j:Int)+7)≤w := by
      by_cases h : -(2*(j:Int)+7)≤w
      · exact h
      · have hm:=Int.mul_lt_mul_of_pos_left (show w< -(2*(j:Int)+7) by omega) hp
        rw [Int.mul_neg] at hm
        omega
    have hmod : w%4=(2*(j:Int)+1)%4 := by
      have hh:=w_mod4 (j+n) y
      rw [hw,Int.mul_emod,pow3_mod4_int] at hh
      split at hh <;> omega
    obtain ⟨x,hx,hW⟩:=w_realize hlo hhi hmod
    exact ⟨x,up_run_of_w hj hx hy (by rw [hW]; exact hw)⟩

#print axioms up_run_exists
#print axioms up_run_iff
end CapSieve
