import CapInverse
namespace Cap

def sourceNext (a : Nat) : Option Nat :=
  if a=0 then none else if a=1 then some 9 else eval (a-2) 1

theorem odd_transport (x : Nat) (hx : 0<x) :
    sourceNext (oddCounter x) = (f x).map oddCounter := by
  by_cases he : x=1
  · subst x; decide
  have h2 : 2≤x := by omega
  unfold sourceNext f oddCounter
  simp only [show 2*x-1≠0 by omega,show 2*x-1≠1 by omega,
    show x≠0 by omega,he,ite_false]
  have hb : 2*x-1-2=2*(x-2)+1 := by omega
  rw [hb,eval_odd]
  rfl

inductive Reach (s : Nat) : Nat → Prop where
  | refl : Reach s s
  | tail {x y : Nat} : Reach s x → Edge x y → Reach s y

theorem reach_le {s x : Nat} (h : Reach s x) : s≤x := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail h e ih => have := edge_grows e; omega

def rootOf (x : Nat) : Nat :=
  match h : predecessor x with
  | none => x
  | some p => rootOf p
termination_by x
decreasing_by exact edge_grows (predecessor_sound h)

theorem root_edge {x y : Nat} (e : Edge x y) : rootOf y=rootOf x := by
  rw [rootOf,predecessor_complete e]

theorem root_reach {s x : Nat} (h : Reach s x) : rootOf x=rootOf s := by
  induction h with
  | refl => rfl
  | tail h e ih => rw [root_edge e,ih]

theorem root_reaches (x : Nat) : Reach (rootOf x) x := by
  induction x using Nat.strongRecOn with
  | ind x ih =>
    rw [rootOf]
    split
    next h => exact Reach.refl
    next p hp =>
      have e := predecessor_sound hp
      exact Reach.tail (ih p (edge_grows e)) e

theorem root_two : rootOf 2=2 := by
  rw [rootOf]
  rfl

theorem root_iff_reach (x : Nat) : rootOf x=2 ↔ Reach 2 x := by
  constructor
  · intro h
    have hr := root_reaches x
    rw [h] at hr
    exact hr
  · intro h
    rw [root_reach h,root_two]

theorem halt_iff_root : (∃ x, Reach 2 x ∧ f x=none) ↔ ∃ i, rootOf (halt i)=2 := by
  constructor
  · rintro ⟨x,hR,hN⟩
    obtain ⟨i,rfl⟩ := (f_none_iff (reach_le hR)).mp hN
    exact ⟨i,(root_iff_reach _).mpr hR⟩
  · rintro ⟨i,hR⟩
    have hr := (root_iff_reach _).mp hR
    exact ⟨halt i,hr,(f_none_iff (reach_le hr)).mpr ⟨i,rfl⟩⟩

theorem halt_no_root_mod3 (i : Nat) (h : halt i%3=0) : rootOf (halt i)≠2 := by
  have hn : predecessor (halt i)=none := by
    cases hp : predecessor (halt i) with
    | none => rfl
    | some p => exact False.elim (no_parent_if_mod3 i h p (predecessor_iff.mp hp))
  rw [rootOf,hn]
  exact halt_root_ne i

theorem pow_mod3_parity (i : Nat) : 2^i%3 = if i%2=0 then 1 else 2 := by
  induction i with
  | zero => decide
  | succ i ih =>
    rw [Nat.pow_succ,Nat.mul_mod,ih]
    by_cases h : i%2=0
    · have hh : (i+1)%2≠0 := by omega
      simp [h,hh]
    · have hh : (i+1)%2=0 := by omega
      simp [h,hh]

theorem halt_mod3_iff (i : Nat) : halt i%3=0 ↔ i%6=4 ∨ i%6=5 := by
  have h := halt_formula i
  have h1 := pow_mod3_parity i
  have h2 : (10*2^i)%3 = (2^i)%3 := by rw [Nat.mul_mod]; simp
  by_cases he : i%2=0
  · rw [if_pos he] at h1
    omega
  · rw [if_neg he] at h1
    omega

theorem halt_excluded_classes (i : Nat) (h : i%6=4 ∨ i%6=5) : rootOf (halt i)≠2 :=
  halt_no_root_mod3 i ((halt_mod3_iff i).mpr h)

-- A same-band parent is characterized by exact division of an affine offset.
theorem same_band_regular (i r s : Nat) (hr : r≤c i) :
    Edge (lo i+r) (lo i+s) ↔ s=3*r+i+6 := by
  constructor
  · intro h
    have he := edge_iff.mp h
    rw [f_band] at he
    simp [hr] at he
    have := lo_c i
    omega
  · intro h
    have he := lo_c i
    have hy : lo i+s=3*r+c i+7 := by omega
    rw [hy]; exact Edge.regular i r hr

theorem same_band_parent (i s : Nat) (hs : s≤c i+2) :
    (∃ r, r≤c i ∧ predecessor (lo i+s)=some (lo i+r)) ↔
    3∣(2*s+i+6) ∧ 3*(i+6)≤2*s+i+6 := by
  constructor
  · rintro ⟨r,hr,hp⟩
    have he := (same_band_regular i r s hr).mp (predecessor_sound hp)
    constructor
    · exact ⟨2*r+i+6,by omega⟩
    · omega
  · rintro ⟨⟨q,hq⟩,hle⟩
    have hq1 : i+6≤q := by omega
    have hq2 : (q-(i+6))%2=0 := by omega
    let r := (q-(i+6))/2
    have hr : s=3*r+i+6 := by dsimp [r]; omega
    have hrb : r≤c i := by omega
    exact ⟨r,hrb,predecessor_complete ((same_band_regular i r s hrb).mpr hr)⟩

#print axioms odd_transport
#print axioms halt_iff_root
#print axioms halt_excluded_classes
#print axioms same_band_parent
end Cap
