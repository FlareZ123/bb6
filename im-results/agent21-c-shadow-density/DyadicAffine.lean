import Lean

namespace BB6.Agent21Dyadic

def P (n : Nat) : Int := 2^n

theorem P_pos (n : Nat) : 0<P n := Int.pow_pos (by decide)
theorem P_ne (n : Nat) : P n≠0 := by have := P_pos n; omega
theorem P_add (m n : Nat) : P (m+n)=P m*P n := Int.pow_add 2 m n

def parity (S : Int) : Int := S%2
def shift (r : Nat) : Int := 3*(r:Int)+1
def offset (S : Int) (r : Nat) : Int := (S+parity S)/2+1-parity (S+shift r)

def cost (w : List Nat) : Nat := w.sum
def drift : List Nat → Int
  | [] => 0
  | r::w => shift r + drift w

def coeff : List Nat → Int
  | [] => 0
  | r::w => 1+P r*coeff w

def acc (S : Int) : List Nat → Int
  | [] => 0
  | r::w => offset S r+P r*acc (S+shift r) w

theorem cost_cons (r : Nat) (w : List Nat) : cost (r::w)=r+cost w := rfl

theorem cost_append (w v : List Nat) : cost (w++v)=cost w+cost v := List.sum_append

theorem drift_append (w v : List Nat) : drift (w++v)=drift w+drift v := by
  induction w with
  | nil => simp [drift]
  | cons r w ih => simp [drift,ih,Int.add_assoc]

theorem acc_append (S : Int) (w v : List Nat) :
    acc S (w++v)=acc S w+P (cost w)*acc (S+drift w) v := by
  induction w generalizing S with
  | nil => simp [acc,cost,drift,P]
  | cons r w ih =>
    simp only [List.cons_append,acc,drift,cost_cons,P_add,ih,Int.mul_add,Int.mul_assoc]
    rw [←Int.add_assoc S (shift r) (drift w)]
    ac_rfl

private theorem parity_shift (S d : Int) (hd : d%2=0) : parity (S+d)=parity S := by
  unfold parity; omega

theorem offset_translate (S d : Int) (r : Nat) (hd : d%2=0) :
    offset (S+d) r=offset S r+d/2 := by
  unfold offset
  rw [parity_shift S d hd]
  rw [show S+d+shift r=S+shift r+d by omega,parity_shift _ _ hd]
  omega

theorem acc_translate (S d : Int) (w : List Nat) (hd : d%2=0) :
    acc (S+d) w=acc S w+(d/2)*coeff w := by
  induction w generalizing S with
  | nil => simp [acc,coeff]
  | cons r w ih =>
    simp only [acc,coeff,offset_translate _ _ _ hd]
    rw [show S+d+shift r=S+shift r+d by omega,ih _]
    rw [Int.mul_add,Int.mul_add,Int.mul_one]
    rw [Int.mul_left_comm (d/2) (P r)]
    omega

structure Affine where
  s : Int
  sigma : Int
  z : Int
  lam : Int
  deriving Repr

def Good (a : Affine) : Prop := a.sigma%4=0 ∧ a.lam%2=1

def mass (a : Affine) (t : Int) := a.s+a.sigma*t

def norm (a : Affine) (t : Int) := a.z+a.lam*t

def numer (a : Affine) (w : List Nat) (t : Int) := norm a t+acc (mass a t) w

def slope (a : Affine) (w : List Nat) := a.lam+(a.sigma/2)*coeff w

private theorem even_mul (a b : Int) (h : a%2=0) : (a*b)%2=0 := by
  rw [Int.mul_emod,h]; simp

private theorem half_mul (a b : Int) (h : a%2=0) : (a*b)/2=(a/2)*b := by
  have he : a=2*(a/2) := by omega
  calc
    a*b/2=(2*(a/2))*b/2 := by rw [←he]
    _=2*((a/2)*b)/2 := by rw [Int.mul_assoc]
    _=(a/2)*b := Int.mul_ediv_cancel_left _ (by decide)

theorem numer_affine_even (a : Affine) (w : List Nat) (t : Int) (he : a.sigma%2=0) :
    numer a w t=a.z+acc a.s w+slope a w*t := by
  unfold numer norm mass slope
  rw [acc_translate _ _ _ (even_mul _ _ he),half_mul _ _ he,Int.add_mul]
  rw [Int.mul_right_comm (a.sigma/2) t (coeff w)]
  ac_rfl

theorem numer_affine (a : Affine) (w : List Nat) (t : Int) (h : Good a) :
    numer a w t=a.z+acc a.s w+slope a w*t :=
  numer_affine_even a w t (by unfold Good at h; omega)

/-- Admissibility of a root for nonempty positive words.  Unlike Good, this
    includes roots with an even Z slope and an odd half-mass slope. -/
def Admissible (a : Affine) : Prop := a.sigma%2=0 ∧ (a.lam+a.sigma/2)%2=1

theorem good_admissible (a : Affine) (h : Good a) : Admissible a := by
  unfold Admissible Good at *; omega

theorem coeff_odd (w : List Nat) (hw : ∃ r v, w=r::v ∧ 0<r) : coeff w%2=1 := by
  obtain ⟨r,v,rfl,hr⟩ := hw
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r≠0)
  unfold coeff
  rw [show k.succ=k+1 by rfl,P_add]
  change (1+P k*2*coeff v)%2=1
  rw [Int.mul_right_comm (P k) 2]
  omega

theorem slope_odd_nonempty (a : Affine) (w : List Nat) (h : Admissible a)
    (hw : ∃ r v, w=r::v ∧ 0<r) : slope a w%2=1 := by
  have hc := coeff_odd w hw
  unfold slope
  rw [Int.add_emod,Int.mul_emod,hc,Int.mul_one]
  have he := h.2
  simpa [Int.add_emod] using he

theorem slope_odd (a : Affine) (w : List Nat) (h : Good a) : slope a w%2=1 := by
  have he : (a.sigma/2)%2=0 := by unfold Good at h; omega
  have hprod := even_mul _ (coeff w) he
  unfold slope Good at *
  omega

/-- Every odd affine congruence has a solution in its binary cylinder. -/
theorem odd_affine_exists (u c : Int) (hu : u%2=1) (r : Nat) :
    ∃ b : Int, 0≤b ∧ b<P r ∧ P r∣c+u*b := by
  induction r generalizing c with
  | zero => exact ⟨0,by decide,by decide,by simp [P]⟩
  | succ r ih =>
    let e := c%2
    have he : 0≤e ∧ e<2 := by dsimp [e]; omega
    have hmod : (c+u*e)%2=0 := by
      rw [Int.add_emod,Int.mul_emod,hu]
      have h0 : e%2=e := by omega
      rw [Int.one_mul,h0]
      dsimp [e]
      omega
    obtain ⟨b,hb0,hb1,hdiv⟩ := ih ((c+u*e)/2)
    refine ⟨e+2*b,by omega,?_,?_⟩
    · rw [P,Int.pow_succ]; change e+2*b<P r*2; omega
    · obtain ⟨k,hk⟩ := hdiv
      refine ⟨k,?_⟩
      have heq : c+u*(e+2*b)=2*((c+u*e)/2+u*b) := by
        rw [Int.mul_add,Int.mul_left_comm u 2 b,Int.mul_add]
        omega
      rw [heq,hk,P_add]
      change 2*(P r*k)=(P r*2)*k
      ac_rfl

def Compatible (a : Affine) (w : List Nat) (b : Int) : Prop := P (cost w)∣numer a w b

theorem word_exists (a : Affine) (w : List Nat) (h : Good a) :
    ∃ b : Int, 0≤b ∧ b<P (cost w) ∧ Compatible a w b := by
  obtain ⟨b,h0,h1,hd⟩ := odd_affine_exists (slope a w) (a.z+acc a.s w) (slope_odd a w h) (cost w)
  exact ⟨b,h0,h1,by unfold Compatible; rw [numer_affine _ _ _ h]; exact hd⟩

def follow (a : Affine) (w : List Nat) (b : Int) : Affine :=
  ⟨mass a b+drift w,a.sigma*P (cost w),numer a w b/P (cost w),slope a w⟩

theorem follow_good (a : Affine) (w : List Nat) (b : Int) (h : Good a) : Good (follow a w b) := by
  refine ⟨?_,slope_odd a w h⟩
  change (a.sigma*P (cost w))%4=0
  rw [Int.mul_emod,h.1]; simp

theorem follow_mass (a : Affine) (w : List Nat) (b t : Int) :
    mass (follow a w b) t=mass a (b+P (cost w)*t)+drift w := by
  change (a.s+a.sigma*b+drift w)+a.sigma*P (cost w)*t = a.s+a.sigma*(b+P (cost w)*t)+drift w
  rw [Int.mul_add,Int.mul_assoc]; ac_rfl

theorem follow_norm_even (a : Affine) (w : List Nat) (b t : Int) (h : a.sigma%2=0)
    (hb : Compatible a w b) :
    P (cost w)*norm (follow a w b) t=numer a w (b+P (cost w)*t) := by
  have hd := Int.ediv_mul_cancel hb
  unfold norm follow; dsimp
  rw [Int.mul_add,Int.mul_comm (P (cost w)) (numer a w b/P (cost w)),hd]
  rw [numer_affine_even _ _ _ h,numer_affine_even _ _ _ h,Int.mul_add]
  rw [Int.mul_left_comm (P (cost w)) (slope a w)]
  omega

theorem follow_norm (a : Affine) (w : List Nat) (b t : Int) (h : Good a)
    (hb : Compatible a w b) :
    P (cost w)*norm (follow a w b) t=numer a w (b+P (cost w)*t) :=
  follow_norm_even a w b t (by unfold Good at h; omega) hb

theorem append_compatible_even (a : Affine) (w v : List Nat) (b t : Int) (h : a.sigma%2=0)
    (hb : Compatible a w b) (ht : Compatible (follow a w b) v t) :
    Compatible a (w++v) (b+P (cost w)*t) := by
  unfold Compatible at *
  rw [cost_append,P_add]
  have he : numer a (w++v) (b+P (cost w)*t)=P (cost w)*numer (follow a w b) v t := by
    unfold numer
    rw [acc_append,←follow_mass,Int.mul_add]
    have hf := follow_norm_even a w b t h hb
    unfold numer at hf
    omega
  rw [he]
  obtain ⟨k,hk⟩ := ht
  exact ⟨k,by rw [hk,Int.mul_assoc]⟩

theorem append_compatible (a : Affine) (w v : List Nat) (b t : Int) (h : Good a)
    (hb : Compatible a w b) (ht : Compatible (follow a w b) v t) :
    Compatible a (w++v) (b+P (cost w)*t) :=
  append_compatible_even a w v b t (by unfold Good at h; omega) hb ht

#print axioms word_exists
#print axioms append_compatible
end BB6.Agent21Dyadic
