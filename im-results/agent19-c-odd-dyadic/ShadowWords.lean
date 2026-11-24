import ShadowScalar

namespace BB6.Agent19Scalar

set_option maxHeartbeats 300000

def nextM (m d : Nat) := m+3*d+1

def offset (m : Nat) : List Nat → Nat
  | [] => 0
  | d::ds => base m+211*(nextM m d%2)+2^d*offset (nextM m d) ds

def mask : List Nat → Nat
  | [] => 0
  | d::ds => 1+2^d*mask ds

def WordPath (m x : Nat) : List Nat → Nat → Nat → Prop
  | [],m',x' => m'=m ∧ x'=x
  | d::ds,m',x' => ∃ y, Step m x d (nextM m d) y ∧ WordPath (nextM m d) y ds m' x'

def Positive (ds : List Nat) : Prop := ∀ d ∈ ds, 0<d

private theorem all_pos_cons {d : Nat} {ds : List Nat} : Positive (d::ds) ↔ 0<d ∧ Positive ds := by
  simp [Positive]

private theorem pow_even {d : Nat} (hd : 0<d) : (2:Nat)^d%2=0 := by
  have he : d=d-1+1 := by omega
  conv => lhs; rw [he,Nat.pow_succ]
  simp

/-- Fixing a cost word removes all branching: endpoint mass and numerator
    are determined by one exact divisibility equation. -/
theorem word_iff (ds : List Nat) (m x m' x' : Nat) (hpos : Positive ds) :
    WordPath m x ds m' x' ↔ m'=m+3*ds.sum+ds.length ∧ 2^ds.sum*x'=x+offset m ds := by
  induction ds generalizing m x m' x' with
  | nil => simp [WordPath,offset]
  | cons d ds ih =>
    obtain ⟨hd,hds⟩ := all_pos_cons.mp hpos
    simp only [WordPath,List.sum_cons,List.length_cons,offset,Nat.pow_add]
    have hpow := Nat.two_pow_pos d
    constructor
    · rintro ⟨y,hstep,hrest⟩
      obtain ⟨hm,hrest⟩ := (ih (nextM m d) y m' x' hds).mp hrest
      have he := hstep.2.2.2
      have hp := hstep.2.2.1
      unfold Q A at he hp
      rw [←hp] at he
      refine ⟨by unfold nextM at hm; omega,?_⟩
      rw [Nat.mul_assoc,hrest,Nat.mul_add,he]
      omega
    · rintro ⟨hm,he⟩
      let b := x+base m+211*(nextM m d%2)
      have hdiv : 2^d∣b := by
        have hsum : 2^d∣b+2^d*offset (nextM m d) ds := by
          rw [← show 2^d*2^ds.sum*x'=b+2^d*offset (nextM m d) ds by dsimp [b]; omega, Nat.mul_assoc]
          exact Nat.dvd_mul_right _ _
        exact (Nat.dvd_add_iff_left (m:=b) (Nat.dvd_mul_right (2^d) (offset (nextM m d) ds))).mpr hsum
      obtain ⟨y,hy⟩ := hdiv
      have hpar : nextM m d%2=A m x%2 := by
        have hmod := congrArg (·%2) hy
        dsimp [b] at hmod
        rw [Nat.mul_mod,pow_even hd,Nat.zero_mul,Nat.zero_mod] at hmod
        unfold A
        omega
      have hstep : Step m x d (nextM m d) y := by
        refine ⟨hd,rfl,hpar,?_⟩
        unfold Q A at *
        rw [←hpar]
        simpa [b] using hy.symm
      refine ⟨y,hstep,(ih (nextM m d) y m' x' hds).mpr ⟨by unfold nextM; omega,?_⟩⟩
      apply Nat.eq_of_mul_eq_mul_left hpow
      rw [Nat.mul_add,←hy,←Nat.mul_assoc]
      dsimp [b]
      omega

theorem word_exists_iff (ds : List Nat) (m x : Nat) (hpos : Positive ds) :
    (∃ m' x', WordPath m x ds m' x') ↔ 2^ds.sum∣x+offset m ds := by
  constructor
  · rintro ⟨m',x',h⟩
    exact ⟨x',((word_iff ds m x m' x' hpos).mp h).2.symm⟩
  · rintro ⟨x',h⟩
    exact ⟨m+3*ds.sum+ds.length,x',(word_iff ds m x _ _ hpos).mpr ⟨rfl,h.symm⟩⟩

theorem word_good (ds : List Nat) (m x m' x' : Nat) (g : Good m x)
    (h : WordPath m x ds m' x') : Good m' x' := by
  induction ds generalizing m x m' x' with
  | nil => obtain ⟨rfl,rfl⟩ := h; exact g
  | cons d ds ih =>
    obtain ⟨y,he,ht⟩ := h
    exact ih _ _ _ _ (step_good g he) ht

private theorem base_shift (m e : Nat) : base (m+4*e)=base m+422*e := by
  unfold base
  omega

private theorem nextM_shift (m d e : Nat) : nextM (m+4*e) d=nextM m d+4*e := by
  unfold nextM
  omega

theorem offset_shift (ds : List Nat) (m e : Nat) :
    offset (m+4*e) ds=offset m ds+422*e*mask ds := by
  induction ds generalizing m with
  | nil => simp [offset,mask]
  | cons d ds ih =>
    simp only [offset,mask,base_shift,nextM_shift,ih]
    have hp : (nextM m d+4*e)%2=nextM m d%2 := by omega
    rw [hp,Nat.mul_add,Nat.mul_add,←Nat.mul_assoc,Nat.mul_left_comm (422*e) (2^d),Nat.mul_assoc]
    omega

def genericM (e : Nat) := 78+4*e
def genericX (e : Nat) := 3852+211*e

theorem generic_good (e : Nat) : Good (genericM e) (genericX e) := by
  unfold Good genericM genericX s base
  omega

def coeff (ds : List Nat) := 211*(1+2*mask ds)
def const (ds : List Nat) := 3852+offset 78 ds

theorem coeff_odd (ds : List Nat) : coeff ds%2=1 := by unfold coeff; omega

/-- A single odd affine congruence is necessary and sufficient for an
    arbitrary cost word from the full common-root line. -/
theorem root_word_iff (ds : List Nat) (e : Nat) (hpos : Positive ds) :
    (∃ m' x', WordPath (genericM e) (genericX e) ds m' x') ↔
      2^ds.sum ∣ const ds+coeff ds*e := by
  rw [word_exists_iff _ _ _ hpos]
  unfold genericM genericX const coeff
  rw [offset_shift]
  have he : 211*(1+2*mask ds)*e=211*e+422*e*mask ds := by
    rw [Nat.mul_add,Nat.mul_one,Nat.add_mul,←Nat.mul_assoc 211 2 (mask ds),Nat.mul_right_comm 422 (mask ds) e]
  rw [he,show 3852+211*e+(offset 78 ds+422*e*mask ds)=3852+offset 78 ds+(211*e+422*e*mask ds) by omega]

#print axioms word_iff
#print axioms word_good
#print axioms offset_shift
#print axioms root_word_iff

private theorem mod_double (e p : Nat) :
    e%2^(p+1)=2*((e/2)%2^p)+e%2 := by
  have h := Nat.mod_add_div e 2
  have hk := Nat.mod_add_div (e/2) (2^p)
  have he : e=(2*((e/2)%2^p)+e%2)+2^(p+1)*(e/2/2^p) := by
    rw [Nat.pow_succ,Nat.mul_comm (2^p) 2,Nat.mul_assoc]
    omega
  have hlt : 2*((e/2)%2^p)+e%2<2^(p+1) := by
    have := Nat.mod_lt (e/2) (Nat.two_pow_pos p)
    rw [Nat.pow_succ]
    omega
  conv => lhs; rw [he,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hlt]

/-- Constructive one-bit lifting, valid for every positive or zero precision. -/
theorem odd_affine_residue (a b p : Nat) (ha : a%2=1) :
    ∃ r, r<2^p ∧ ∀ e, 2^p∣b+a*e ↔ e%2^p=r := by
  induction p generalizing b with
  | zero => exact ⟨0,by decide,by simp [Nat.mod_one]⟩
  | succ p ih =>
    let t := b%2
    let c := (b+a*t)/2
    have hpar (e : Nat) : (b+a*e)%2=0 ↔ e%2=t := by
      rw [Nat.add_mod,Nat.mul_mod,ha,Nat.one_mul,Nat.mod_mod]
      dsimp [t]
      omega
    have hc : 2*c=b+a*t := by
      have h := (hpar t).mpr (by dsimp [t]; omega)
      dsimp [c]
      omega
    obtain ⟨r,hr,hi⟩ := ih c
    refine ⟨2*r+t,by rw [Nat.pow_succ]; dsimp [t]; omega,?_⟩
    intro e
    rw [mod_double]
    by_cases he : e%2=t
    · have he' : e=2*(e/2)+t := by omega
      have hsum : b+a*e=2*(c+a*(e/2)) := by
        conv => lhs; rw [he',Nat.mul_add,Nat.mul_left_comm a 2]
        omega
      rw [hsum,Nat.pow_succ,Nat.mul_comm (2^p) 2,Nat.mul_dvd_mul_iff_left (by decide : 0<2),hi,he]
      omega
    · have hn : ¬2^(p+1)∣b+a*e := by
        intro hd
        have hd' : 2∣b+a*e := Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega : 1≤p+1)) hd
        exact he ((hpar e).mp (Nat.mod_eq_zero_of_dvd hd'))
      have hneq : 2*(e/2%2^p)+e%2≠2*r+t := by
        dsimp [t] at he ⊢
        omega
      simp [hn,hneq]

/-- Every positive cost word is realized by exactly one exponent residue,
    with no extra positivity or branch-parity constraints. -/
theorem root_word_unique_residue (ds : List Nat) (hpos : Positive ds) :
    ∃ r, r<2^ds.sum ∧ ∀ e,
      (∃ m' x', WordPath (genericM e) (genericX e) ds m' x') ↔ e%2^ds.sum=r := by
  obtain ⟨r,hr,hi⟩ := odd_affine_residue (coeff ds) (const ds) ds.sum (coeff_odd ds)
  exact ⟨r,hr,fun e => (root_word_iff ds e hpos).trans (hi e)⟩

/-- The mask of a nonempty word is positive. -/
theorem mask_pos {ds : List Nat} (h : ds≠[]) : 0<mask ds := by
  cases ds with
  | nil => contradiction
  | cons d ds => unfold mask; omega

private theorem mask_lt_pow (ds : List Nat) (h : Positive ds) : mask ds<2^ds.sum := by
  induction ds with
  | nil => decide
  | cons d ds ih =>
    obtain ⟨hd,hs⟩ := all_pos_cons.mp h
    have h1 := ih hs
    have hp : 2≤(2:Nat)^d := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hd
    have hmul := Nat.mul_le_mul_left (2^d) (show mask ds+1≤2^ds.sum by omega)
    simp only [Nat.mul_add,Nat.mul_one] at hmul
    simp only [mask,List.sum_cons,Nat.pow_add]
    omega

#print axioms odd_affine_residue
#print axioms root_word_unique_residue
#print axioms mask_lt_pow
end BB6.Agent19Scalar
