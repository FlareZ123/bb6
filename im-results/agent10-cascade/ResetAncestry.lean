import SweepInvariant

namespace CascadeAncestry
open CascadeSource CascadeSweep

/-- A sweep remembers an actual prior reset on the same blank-rooted orbit. -/
def Tagged (a b : Nat) : Prop :=
  b=0 ∨ b=2 ∨ ∃ h m,
    ReachC (2,0) (h,0) ∧ a+2=4*2^m ∧
    b+8*2^m=2*h+2*m+9 ∧ b%2=1

theorem tagged_step (a b u v : Nat)
    (hr : ReachC (2,0) (a,b)) (ht : Tagged a b)
    (he : Cstep a b=some (u,v)) : Tagged u v := by
  rcases ht with hb | hb | ⟨h, m, hh, ha, hform, hodd⟩
  · subst b
    simp [Cstep] at he
    rcases he with ⟨rfl,rfl⟩
    right; right
    refine ⟨a,0,hr,by decide, ?_, ?_⟩
    · omega
    · omega
  · subst b
    by_cases ha0 : a=0
    · subst a
      simp [Cstep] at he
      rcases he with ⟨rfl,rfl⟩
      exact Or.inl rfl
    · have hd : ¬(2*a≤0) := by omega
      have hrem : (6*a+8)%4=0 ∨ (6*a+8)%4=2 := by omega
      have he' : some ((6*a+8)/4,(6*a+8)%4)=some (u,v) := by
        simpa [Cstep,ha0,hd] using he
      have huv : u=(6*a+8)/4 ∧ v=(6*a+8)%4 := by simpa using he'.symm
      rcases huv with ⟨rfl,rfl⟩
      rcases hrem with hv|hv
      · exact Or.inl hv
      · exact Or.inr (Or.inl hv)
  · have hpow : 1≤2^m := Nat.one_le_pow m 2 (by omega)
    have ha_even : a%2=0 := by
      have hmod : (4*2^m)%2=0 := by simp [Nat.mul_mod]
      omega
    have ha_pos : 2≤a := by
      have hm : 4 ≤ 4*2^m := by simpa using Nat.mul_le_mul_left 4 hpow
      omega
    have hb0 : b≠0 := by omega
    by_cases hb1 : b=1
    · subst b; simp [Cstep] at he
    · have hb3 : 3≤b := by omega
      let d := b-2
      have hdd : d%2=1 := by dsimp [d]; omega
      by_cases hlarge : 2*a≤d
      · have he' : some (2*a+2,d-2*a)=some (u,v) := by
          simpa [Cstep,hb0,hb1,d,hlarge] using he
        have huv : u=2*a+2 ∧ v=d-2*a := by simpa using he'.symm
        rcases huv with ⟨rfl,rfl⟩
        right; right
        refine ⟨h,m+1,hh,?_,?_,?_⟩
        · rw [Nat.pow_succ]; omega
        · rw [Nat.pow_succ]; dsimp [d]; omega
        · dsimp [d]; omega
      · have hpar : d%2≠0 := by omega
        let t:=6*a+d+5
        have ht : t%2=0 := by dsimp [t]; omega
        have hrem : t%4=0 ∨ t%4=2 := by omega
        have he' : some (t/4,t%4)=some (u,v) := by
          simpa [Cstep,hb0,hb1,d,hlarge,hpar,t] using he
        have huv : u=t/4 ∧ v=t%4 := by simpa using he'.symm
        rcases huv with ⟨rfl,rfl⟩
        rcases hrem with hv|hv
        · exact Or.inl hv
        · exact Or.inr (Or.inl hv)

theorem tagged_reachable {x : Nat × Nat}
    (hr : ReachC (2,0) x) : Tagged x.1 x.2 := by
  induction hr with
  | refl => exact Or.inl rfl
  | push hprev he ih =>
    exact tagged_step _ _ _ _ hprev ih he

/-- A direct reset exit from a sweep remembers its exact earlier reset and
    the affine formula for its output. -/
theorem sweep_even_parent (a b u h m : Nat)
    (ha : a+2=4*2^m) (hform : b+8*2^m=2*h+2*m+9)
    (hodd : b%2=1) (he : Cstep a b=some (u,0)) :
    (6*2^m-1≤u ∧ u≤8*2^m-3) ∧
    2*u=8*2^m+h+m := by
  have hpow : 1≤2^m := Nat.one_le_pow m 2 (by omega)
  have ha_even : a%2=0 := by
    have hmod : (4*2^m)%2=0 := by simp [Nat.mul_mod]
    omega
  have ha_pos : 2≤a := by
    have hm : 4 ≤ 4*2^m := by simpa using Nat.mul_le_mul_left 4 hpow
    omega
  have hb0 : b≠0 := by omega
  by_cases hb1 : b=1
  · subst b; simp [Cstep] at he
  · have hb3 : 3≤b := by omega
    let d := b-2
    have hdd : d%2=1 := by dsimp [d]; omega
    by_cases hlarge : 2*a≤d
    · have he' : some (2*a+2,d-2*a)=some (u,0) := by
        simpa [Cstep,hb0,hb1,d,hlarge] using he
      have hzero : d-2*a=0 := by simpa using congrArg Prod.snd (Option.some.inj he')
      omega
    · have hpar : d%2≠0 := by omega
      let t:=6*a+d+5
      have he' : some (t/4,t%4)=some (u,0) := by
        simpa [Cstep,hb0,hb1,d,hlarge,hpar,t] using he
      have huv : u=t/4 ∧ 0=t%4 := by simpa using he'.symm
      rcases huv with ⟨hu,hv⟩
      have hdiv : t=4*u := by omega
      have ha6 : 6*a+12=24*2^m := by omega
      dsimp [t,d] at hdiv hlarge
      omega

#print axioms sweep_even_parent

#print axioms tagged_reachable

/-- Every genuine predecessor of a reset u with u mod 3 != 2 must be a
    completed even cascade with a genuine earlier reset. -/
theorem reachable_even_reset_parent (u : Nat)
    (hr : ReachC (2,0) (u,0)) (hodd : u%3 ≠ 2) :
    ∃ h m, ReachC (2,0) (h,0) ∧
      6*2^m-1 ≤ u ∧ u ≤ 8*2^m-3 ∧
      2*u=8*2^m+h+m := by
  cases hr with
  | refl =>
    exfalso
    exact hodd (by decide)
  | @push y z hprev he =>
    rcases y with ⟨a,b⟩
    change Cstep a b=some (u,0) at he
    have ht := tagged_reachable hprev
    change Tagged a b at ht
    rcases ht with hb|hb|⟨h,m,hhr,ha,hform,hpar⟩
    · subst b
      simp [Cstep] at he
    · subst b
      by_cases ha0 : a=0
      · subst a
        simp [Cstep] at he
        rcases he with rfl
        exact False.elim (hodd (by decide))
      · have hd : ¬ (2*a≤0) := by omega
        have he' : some ((6*a+8)/4,(6*a+8)%4)=some (u,0) := by
          simpa [Cstep,ha0,hd] using he
        have huv : u=(6*a+8)/4 ∧ 0=(6*a+8)%4 := by simpa using he'.symm
        rcases huv with ⟨hu,hv⟩
        have hdiv : 6*a+8=4*u := by omega
        have hmod : u%3=2 := by omega
        exact False.elim (hodd hmod)
    · obtain ⟨hb1,hb2⟩ := sweep_even_parent a b u h m ha hform hpar he
      exact ⟨h,m,hhr,hb1.1,hb1.2,hb2⟩

/-- Even-reset image intervals at distinct dyadic scales are disjoint. -/
theorem even_band_unique (u m k : Nat)
    (hm : 6*2^m-1 ≤ u ∧ u ≤ 8*2^m-3)
    (hk : 6*2^k-1 ≤ u ∧ u ≤ 8*2^k-3) : m=k := by
  by_cases hyes : m=k
  · exact hyes
  have hne : m<k ∨ k<m := by omega
  rcases hne with h | h
  · have hone : 1≤2^m := Nat.one_le_pow m 2 (by omega)
    have hp := Nat.pow_le_pow_right (by omega : 0 < 2) (show m+1≤k by omega)
    rw [Nat.pow_succ] at hp
    have hs : 2*2^m ≤ 2^k := by omega
    have hbound := Nat.mul_le_mul_left 6 hs
    omega
  · have hone : 1≤2^k := Nat.one_le_pow k 2 (by omega)
    have hp := Nat.pow_le_pow_right (by omega : 0 < 2) (show k+1≤m by omega)
    rw [Nat.pow_succ] at hp
    have hs : 2*2^k ≤ 2^m := by omega
    have hbound := Nat.mul_le_mul_left 6 hs
    omega

#print axioms reachable_even_reset_parent
#print axioms even_band_unique
end CascadeAncestry
