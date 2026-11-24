import Lean
import Lean.Elab.Tactic.Omega

namespace BB6.Agent42DirectBlocks

def DirectLaw (reach : Nat → Nat → Prop) : Prop :=
  ∀ x y, 6≤y → y%2=0 → (x+y)%8≠0 → (x+y)%8≠7 →
    (reach x y ↔ reach (x+y-2) ((y-2)/2))

def ForbiddenLaw (reach : Nat → Nat → Prop) : Prop :=
  ∀ x y, 5≤y → y%2=1 → ((x+y)%4=1 ∨ (x+y)%4=2) → ¬reach x y

/-- An arbitrarily long block of forced direct predecessors; exact mass
    loss and the left residue are preserved by the induction. -/
theorem direct_block (reach : Nat → Nat → Prop) (hd : DirectLaw reach)
    (r x y u : Nat) (hu : 4≤u) (hue : u%2=0) (hy : y+2=2^r*u)
    (hx : x%4=0 ∨ x%4=3) :
    ∃ a, (reach x y ↔ reach a (u-2)) ∧
      a+2*(u-2)+4*r=x+2*y ∧ a%4=x%4 := by
  induction r generalizing x y with
  | zero =>
    simp at hy
    refine ⟨x, ?_, ?_, rfl⟩
    · have h : y=u-2 := by omega
      rw [h]
    · omega
  | succ r ih =>
    have hp : 0<2^r := Nat.pow_pos (by decide)
    have hpu : u≤2^r*u := by
      exact Nat.le_mul_of_pos_left u hp
    have heq : y+2=2*(2^r*u) := by
      rw [hy,Nat.pow_succ]
      ac_rfl
    have h8 : 6≤y := by omega
    have hpar : y%2=0 := by omega
    have h4u : (2^r*u)%2=0 := by simp [Nat.mul_mod,hue]
    have hy4 : y%4=2 := by omega
    have h0 : (x+y)%8≠0 := by omega
    have h7 : (x+y)%8≠7 := by omega
    let x' := x+y-2
    let y' := (y-2)/2
    have hy' : y'+2=2^r*u := by dsimp [y']; omega
    have hx' : x'%4=x%4 := by dsimp [x']; omega
    have hxm : x'%4=0 ∨ x'%4=3 := by rwa [hx']
    have hmass : x'+2*y'+4=x+2*y := by dsimp [x',y']; omega
    obtain ⟨a,ha,hm,hr⟩ := ih x' y' hy' hxm
    refine ⟨a,(hd x y h8 hpar h0 h7).trans ha,?_,hr.trans hx'⟩
    omega

theorem long_direct_excluded (reach : Nat → Nat → Prop) (hd : DirectLaw reach)
    (hf : ForbiddenLaw reach) (x y r u : Nat)
    (hy : y+2=2^(r+1)*u) (hu : 7≤u) (hu4 : u%4=3) (hx : x%4=3)
    (hw : (x+2*y)%8=(4*(r+1)+3)%8) : ¬reach x y := by
  have hy' : y+2=2^r*(2*u) := by rw [hy,Nat.pow_succ,Nat.mul_assoc]
  obtain ⟨a,ha,hm,ha4⟩ := direct_block reach hd r x y (2*u) (by omega) (by omega) hy' (Or.inr hx)
  let k := 2*u-2
  have hk : 6≤k := by dsimp [k]; omega
  have hke : k%2=0 := by dsimp [k]; omega
  have hk8 : k%8=4 := by dsimp [k]; omega
  have hsum : (a+k)%8=3 := by dsimp [k] at *; omega
  have hlast := hd a k hk hke (by omega) (by omega)
  have hku : (k-2)/2=u-2 := by dsimp [k]; omega
  have ha1 : (a+k-2)%4=1 := by dsimp [k] at *; omega
  intro hr
  have hr' : reach a k := ha.mp hr
  have hr'' := hlast.mp hr'
  rw [hku] at hr''
  exact hf _ _ (by omega) (by omega) (Or.inr (by omega)) hr''

theorem high_long_direct_excluded (reach : Nat → Nat → Prop) (hd : DirectLaw reach)
    (hf : ForbiddenLaw reach) (J m k r u : Nat)
    (hstop : k+J+3*m+4=2^(2*m+2)*(J+2))
    (hval : k+2=2^(r+1)*u) (hu : 7≤u) (hu4 : u%4=3)
    (hm : m%4=(2*(r+1)+1)%4) : ¬reach (2*J+1) k := by
  have hm1 : 1≤m := by omega
  have hme : m%2=1 := by omega
  have h8 : 8 ∣ 2^(2*m+2)*(J+2) := by
    exact Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega : 3≤2*m+2)) (Nat.dvd_mul_right _ _)
  have he : (2^(2*m+2)*(J+2))%8=0 := Nat.mod_eq_zero_of_dvd h8
  have hv : k%2=0 := by
    rw [Nat.pow_succ] at hval
    have hh : 2^r*2*u=2*(2^r*u) := by ac_rfl
    rw [hh] at hval
    omega
  have hJ : J%2=1 := by omega
  have hx : (2*J+1)%4=3 := by omega
  have hw : ((2*J+1)+2*k)%8=(4*(r+1)+3)%8 := by omega
  exact long_direct_excluded reach hd hf (2*J+1) k r u hval hu hu4 hx hw

theorem pow4_mod15 (s : Nat) : 2^(4*s)%15=1 := by
  induction s with
  | zero => decide
  | succ s ih =>
    rw [show 4*(s+1)=4*s+4 by omega,Nat.pow_add,Nat.mul_mod,ih]

def m1Mass (s t : Nat) := 2^(4*(s+1))*(27+60*t)
def m1J (s t : Nat) := (m1Mass s t-27)/15

theorem m1Mass_eq (s t : Nat) : m1Mass s t=15*m1J s t+27 := by
  have hm : m1Mass s t%15=12 := by
    unfold m1Mass
    rw [Nat.mul_mod,pow4_mod15]
    omega
  have hp : 16≤2^(4*(s+1)) := by
    exact Nat.pow_le_pow_right (by decide : 0<2) (by omega : 4≤4*(s+1))
  have hb : 27≤m1Mass s t := by
    unfold m1Mass
    have hh := Nat.mul_le_mul_right (27+60*t) hp
    omega
  unfold m1J
  omega

theorem m1_family_excluded (reach : Nat → Nat → Prop) (hd : DirectLaw reach)
    (hf : ForbiddenLaw reach) (s t : Nat) :
    ¬reach (2*m1J s t+1) (15*m1J s t+25) := by
  let J := m1J s t
  let k := 15*J+25
  have hstop : k+J+3*1+4=2^(2*1+2)*(J+2) := by dsimp [k]; omega
  have he := m1Mass_eq s t
  have hval : k+2=2^((4*s+3)+1)*(27+60*t) := by
    unfold m1Mass at he
    rw [show (4*s+3)+1=4*(s+1) by omega]
    dsimp [k,J]
    omega
  exact high_long_direct_excluded reach hd hf J 1 k (4*s+3) (27+60*t) hstop hval (by omega) (by omega) (by omega)

def directDepth (y : Nat) : Nat := ((y+2 : Nat) : Int).trailingZeros
def directOdd (y : Nat) : Nat := (y+2)/2^(directDepth y)
def directBlockExcluded (x y : Nat) : Bool :=
  let d := directDepth y
  let u := directOdd y
  decide (1≤d ∧ y+2=2^d*u ∧ 7≤u ∧ u%4=3 ∧ x%4=3 ∧ (x+2*y)%8=(4*d+3)%8)

theorem directBlockExcluded_sound (reach : Nat → Nat → Prop) (hd : DirectLaw reach)
    (hf : ForbiddenLaw reach) (x y : Nat) (hc : directBlockExcluded x y=true) :
    ¬reach x y := by
  have h := of_decide_eq_true hc
  change 1≤directDepth y ∧ y+2=2^(directDepth y)*directOdd y ∧
    7≤directOdd y ∧ directOdd y%4=3 ∧ x%4=3 ∧
    (x+2*y)%8=(4*directDepth y+3)%8 at h
  obtain ⟨hdp,hv,hu,hu4,hx,hw⟩ := h
  have he : directDepth y-1+1=directDepth y := by omega
  exact long_direct_excluded reach hd hf x y (directDepth y-1) (directOdd y)
    (by rwa [he]) hu hu4 hx (by rwa [he])

theorem direct_block_iff (reach : Nat → Nat → Prop) (hd : DirectLaw reach)
    (r x y u : Nat) (hu : 4≤u) (hue : u%2=0) (hy : y+2=2^r*u)
    (hx : x%4=0 ∨ x%4=3) :
    reach x y ↔ reach (x+2*y-2*(u-2)-4*r) (u-2) := by
  obtain ⟨a,ha,hm,_⟩ := direct_block reach hd r x y u hu hue hy hx
  have he : a=x+2*y-2*(u-2)-4*r := by omega
  rwa [he] at ha

#print axioms directBlockExcluded_sound
#print axioms direct_block_iff
#print axioms m1_family_excluded
#print axioms direct_block
#print axioms long_direct_excluded
#print axioms high_long_direct_excluded
end BB6.Agent42DirectBlocks
