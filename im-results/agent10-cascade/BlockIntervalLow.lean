import PeriodicReset

namespace CascadePeriodic

/-- An outward rounded normalized interval, using integer scale M. -/
def Encloses (x k M lo hi : Nat) : Prop :=
  lo*2^k ≤ x*M ∧ x*M ≤ hi*2^k

/-- Propagate the normalized interval without computing the large successor. -/
theorem interval_step (x y k a δ M lo hi clo chi lo' hi' : Nat)
    (hx : Encloses x k M lo hi)
    (hc : Encloses (2*k+5) k M clo chi)
    (he : 2^(a+1)*y = 3^a*(x+16*2^k+2*k+5))
    (hl : lo'*2^(a+1+δ) ≤ (lo+16*M+clo)*3^a)
    (hh : (hi+16*M+chi)*3^a ≤ hi'*2^(a+1+δ)) :
    Encloses y (k+δ) M lo' hi' := by
  rcases hx with ⟨hxl,hxh⟩
  rcases hc with ⟨hcl,hch⟩
  have hmid : 16*M*2^k=16*2^k*M := by ac_rfl
  have hsumL : (lo+16*M+clo)*2^k ≤ (x+16*2^k+2*k+5)*M := by
    rw [show x+16*2^k+2*k+5=x+16*2^k+(2*k+5) by omega]
    rw [Nat.add_mul, Nat.add_mul lo, Nat.add_mul, Nat.add_mul x, hmid]
    exact Nat.add_le_add (Nat.add_le_add hxl (Nat.le_refl _)) hcl
  have hsumH : (x+16*2^k+2*k+5)*M ≤ (hi+16*M+chi)*2^k := by
    rw [show x+16*2^k+2*k+5=x+16*2^k+(2*k+5) by omega]
    rw [Nat.add_mul (x+16*2^k) (2*k+5), Nat.add_mul x (16*2^k), Nat.add_mul (hi+16*M) chi, Nat.add_mul hi (16*M), hmid]
    exact Nat.add_le_add (Nat.add_le_add hxh (Nat.le_refl _)) hch
  have hpos : 0 < 2^(a+1) := Nat.pow_pos (by decide)
  constructor
  · apply Nat.le_of_mul_le_mul_right _ hpos
    calc
      (lo'*2^(k+δ))*2^(a+1) = (lo'*2^(a+1+δ))*2^k := by
        rw [Nat.pow_add 2 k δ, Nat.pow_add 2 (a+1) δ]
        ac_rfl
      _ ≤ ((lo+16*M+clo)*3^a)*2^k := Nat.mul_le_mul_right _ hl
      _ = ((lo+16*M+clo)*2^k)*3^a := by ac_rfl
      _ ≤ ((x+16*2^k+2*k+5)*M)*3^a := Nat.mul_le_mul_right _ hsumL
      _ = (3^a*(x+16*2^k+2*k+5))*M := by ac_rfl
      _ = (y*M)*2^(a+1) := by rw [←he]; ac_rfl
  · apply Nat.le_of_mul_le_mul_right _ hpos
    calc
      (y*M)*2^(a+1) = (3^a*(x+16*2^k+2*k+5))*M := by rw [←he]; ac_rfl
      _ = ((x+16*2^k+2*k+5)*M)*3^a := by ac_rfl
      _ ≤ ((hi+16*M+chi)*2^k)*3^a := Nat.mul_le_mul_right _ hsumH
      _ = ((hi+16*M+chi)*3^a)*2^k := by ac_rfl
      _ ≤ (hi'*2^(a+1+δ))*2^k := Nat.mul_le_mul_right _ hh
      _ = (hi'*2^(k+δ))*2^(a+1) := by
        rw [Nat.pow_add 2 k δ, Nat.pow_add 2 (a+1) δ]
        ac_rfl

/-- The interval can establish the exact source sweep band, and a strict
    lower bound rules out the fatal equality. -/
theorem interval_nonfatal_band (h k M lo hi c3 c5 : Nat)
    (hx : Encloses (2*h+5) k M lo hi)
    (h3 : c3*2^k ≤ (2*k+3)*M)
    (h5 : (2*k+5)*M ≤ c5*2^k)
    (hl : 8*M < lo+c3)
    (hh : hi+c5 < 16*M) : Valid h k := by
  have hp : 0<2^k := Nat.pow_pos (by decide)
  rcases hx with ⟨hxl,hxh⟩
  have hL : (8*2^k)*M < (2*h+5+2*k+3)*M := by
    calc
      (8*2^k)*M = (8*M)*2^k := by ac_rfl
      _ < (lo+c3)*2^k := Nat.mul_lt_mul_of_pos_right hl hp
      _ ≤ (2*h+5+2*k+3)*M := by
        rw [Nat.add_mul, show 2*h+5+2*k+3=(2*h+5)+(2*k+3) by omega, Nat.add_mul]
        exact Nat.add_le_add hxl h3
  have hH : (2*h+5+2*k+5)*M < (16*2^k)*M := by
    calc
      (2*h+5+2*k+5)*M ≤ (hi+c5)*2^k := by
        rw [show 2*h+5+2*k+5=(2*h+5)+(2*k+5) by omega, Nat.add_mul (2*h+5) (2*k+5), Nat.add_mul hi c5]
        exact Nat.add_le_add hxh h5
      _ < (16*M)*2^k := Nat.mul_lt_mul_of_pos_right hh hp
      _ = (16*2^k)*M := by ac_rfl
  have hL' := Nat.lt_of_mul_lt_mul_right hL
  have hH' := Nat.lt_of_mul_lt_mul_right hH
  exact ⟨by omega,by omega⟩

/-- Non-strict lower check suffices to establish the next sweep band,
    without assuming the successor is itself nonfatal. -/
theorem interval_band (h k M lo hi c3 c5 : Nat)
    (hx : Encloses (2*h+5) k M lo hi)
    (h3 : c3*2^k ≤ (2*k+3)*M)
    (h5 : (2*k+5)*M ≤ c5*2^k)
    (hl : 8*M ≤ lo+c3)
    (hh : hi+c5 < 16*M) (hm : 0<M) :
    4*2^k ≤ h+k+4 ∧ h+k+5 < 8*2^k := by
  have hp : 0<2^k := Nat.pow_pos (by decide)
  rcases hx with ⟨hxl,hxh⟩
  have hL : (8*2^k)*M ≤ (2*h+5+2*k+3)*M := by
    calc
      (8*2^k)*M = (8*M)*2^k := by ac_rfl
      _ ≤ (lo+c3)*2^k := Nat.mul_le_mul_right _ hl
      _ ≤ (2*h+5+2*k+3)*M := by
        rw [Nat.add_mul, show 2*h+5+2*k+3=(2*h+5)+(2*k+3) by omega, Nat.add_mul]
        exact Nat.add_le_add hxl h3
  have hH : (2*h+5+2*k+5)*M < (16*2^k)*M := by
    calc
      (2*h+5+2*k+5)*M ≤ (hi+c5)*2^k := by
        rw [show 2*h+5+2*k+5=(2*h+5)+(2*k+5) by omega, Nat.add_mul (2*h+5) (2*k+5), Nat.add_mul hi c5]
        exact Nat.add_le_add hxh h5
      _ < (16*M)*2^k := Nat.mul_lt_mul_of_pos_right hh hp
      _ = (16*2^k)*M := by ac_rfl
  have hL' := Nat.le_of_mul_le_mul_right hL hm
  have hH' := Nat.lt_of_mul_lt_mul_right hH
  exact ⟨by omega,by omega⟩

/-- A low residue of sufficient precision certifies the exact valuation. -/
theorem valuation_from_low (z r b v : Nat) (hb : v+1≤b)
    (hr : z%2^b=r) (hv : r%2^(v+1)=2^v) :
    ∃d, z=2^v*d ∧ d%2=1 ∧ d%2^(b-v)=r/2^v := by
  have hdvd : 2^(v+1) ∣ 2^b := Nat.pow_dvd_pow 2 hb
  have hz : z%2^(v+1)=2^v := by
    rw [←Nat.mod_mod_of_dvd z hdvd,hr,hv]
  let d := 1+2*(z/2^(v+1))
  have hdiv := Nat.mod_add_div z (2^(v+1))
  rw [hz,Nat.pow_succ] at hdiv
  have hf : z=2^v*d := by
    dsimp [d]
    grind
  have hodd : d%2=1 := by dsimp [d]; omega
  have hpow : 2^b=2^v*2^(b-v) := by
    rw [←Nat.pow_add]
    congr 1
    omega
  have hres : r=2^v*(d%2^(b-v)) := by
    rw [←hr,hf,hpow,Nat.mul_mod_mul_left]
  refine ⟨d,hf,hodd,?_⟩
  rw [hres,Nat.mul_div_cancel_left _ (Nat.pow_pos (by decide))]

private theorem pow3_odd (a : Nat) : 3^a%2=1 := by
  induction a with
  | zero => decide
  | succ a ih => rw [Nat.pow_succ,Nat.mul_mod,ih]

/-- Given a valid source band and a certified low valuation, the complete
    reset grammar supplies a real successor and its exact low residue. -/
theorem low_reset_sound (h k a b r : Nat) (hb : a+2≤b)
    (hvalid : Valid h k)
    (hr : ((2*h+5)+16*2^k+2*k+5)%2^b=r)
    (hv : r%2^(a+2)=2^(a+1)) :
    ∃u, Unified h u k a ∧
      (2*u+5)%2^(b-(a+1))=(3^a*(r/2^(a+1)))%2^(b-(a+1)) := by
  obtain ⟨d,hd,hodd,hres⟩ := valuation_from_low _ r b (a+1) (by omega) hr (by simpa only [Nat.add_assoc] using hv)
  let y := 3^a*d
  have hyodd : y%2=1 := by
    dsimp [y]
    rw [Nat.mul_mod,pow3_odd,hodd]
  have hp : 1≤2^k := Nat.one_le_pow _ _ (by decide)
  have hdpos : 1≤d := by omega
  have hy : 5≤y := by
    by_cases ha : 2≤a
    · have hp3 : 9≤3^a := Nat.pow_le_pow_right (n:=3) (by decide) ha
      dsimp [y]
      calc
        5≤9*d := by omega
        _≤3^a*d := Nat.mul_le_mul_right _ hp3
    · have hc : a=0 ∨ a=1 := by omega
      rcases hc with rfl|rfl <;> simp [y] at hd ⊢ <;> omega
  let u := (y-5)/2
  have hu : 2*u+5=y := by dsimp [u]; omega
  refine ⟨u,⟨hvalid,?_⟩,?_⟩
  · rw [hu,hd]
    dsimp [y]
    ac_rfl
  · rw [hu]
    dsimp [y]
    rw [Nat.mul_mod (3^a) d, hres, Nat.mul_mod (3^a) (r/2^(a+1))]
    have hlt : r/2^(a+1)<2^(b-(a+1)) := by
      rw [←hres]
      exact Nat.mod_lt _ (Nat.pow_pos (by decide))
    rw [Nat.mod_eq_of_lt hlt]

/-- Powers larger than the current precision do not need to be materialized. -/
def pow2mod (k b : Nat) : Nat := if b≤k then 0 else 2^k

theorem pow2mod_eq (k b : Nat) : pow2mod k b=2^k%2^b := by
  unfold pow2mod
  split
  · rename_i h
    exact (Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 h)).symm
  · rename_i h
    have hlt : 2^k<2^b := Nat.pow_lt_pow_right (by decide) (by omega)
    exact (Nat.mod_eq_of_lt hlt).symm

theorem low_operand (h k b low : Nat) (hlow : (2*h+5)%2^b=low) :
    ((2*h+5)+16*2^k+2*k+5)%2^b = (low+pow2mod (k+4) b+2*k+5)%2^b := by
  have hp : 16*2^k=2^(k+4) := by rw [Nat.pow_add]; omega
  rw [hp,pow2mod_eq,←hlow]
  rw [show (2*h+5)+2^(k+4)+2*k+5=((2*h+5)+2^(k+4))+(2*k+5) by omega]
  rw [show (2*h+5)%2^b+2^(k+4)%2^b+2*k+5=((2*h+5)%2^b+2^(k+4)%2^b)+(2*k+5) by omega]
  rw [←Nat.mod_add_mod ((2*h+5)+2^(k+4)),Nat.add_mod (2*h+5) (2^(k+4))]
  exact Nat.mod_add_mod _ _ _

def scale : Nat := 2^64

def floorCeil (z p : Nat) : Nat × Nat :=
  (z/p, z/p + if z%p=0 then 0 else 1)

theorem floorCeil_sound (z p : Nat) (hp : 0<p) :
    (floorCeil z p).1*p≤z ∧ z≤(floorCeil z p).2*p := by
  have hd := Nat.div_add_mod z p
  have hm := Nat.mod_lt z hp
  have hcomm : p*(z/p)=(z/p)*p := Nat.mul_comm ..
  rw [hcomm] at hd
  unfold floorCeil
  constructor
  · exact Nat.div_mul_le_self ..
  · dsimp
    split
    · rename_i h
      simp only [h,Nat.add_zero] at hd ⊢
      omega
    · rw [Nat.add_mul,Nat.one_mul]
      omega

private theorem large_correction (k : Nat) (hk : 128≤k) : (2*k+5)*scale≤2^k := by
  have hh (n : Nat) : (2*(128+n)+5)*scale≤2^(128+n) := by
    induction n with
    | zero => decide
    | succ n ih =>
      rw [show 128+(n+1)=128+n+1 by omega,Nat.pow_succ]
      have hle : (2*(128+n+1)+5)*scale≤(2*(2*(128+n)+5))*scale := Nat.mul_le_mul_right _ (by omega)
      calc
        (2*(128+n+1)+5)*scale≤(2*(2*(128+n)+5))*scale := hle
        _=((2*(128+n)+5)*scale)*2 := by ac_rfl
        _≤2^(128+n)*2 := Nat.mul_le_mul_right _ ih
  have he : k=128+(k-128) := by omega
  rw [he]
  exact hh _

def correction (k c : Nat) : Nat × Nat :=
  if 128≤k then (0,1) else floorCeil ((2*k+c)*scale) (2^k)

theorem correction_sound (k c : Nat) (hc : c≤5) :
    Encloses (2*k+c) k scale (correction k c).1 (correction k c).2 := by
  unfold correction
  split
  · rename_i hk
    constructor
    · simp
    · simp only [Nat.one_mul]
      exact Nat.le_trans (Nat.mul_le_mul_right _ (by omega : 2*k+c≤2*k+5)) (large_correction k hk)
  · exact floorCeil_sound _ _ (Nat.pow_pos (by decide))

#print axioms interval_step
#print axioms interval_nonfatal_band
#print axioms low_reset_sound
end CascadePeriodic
