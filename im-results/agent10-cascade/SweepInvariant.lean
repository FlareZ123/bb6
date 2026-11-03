import SourceMacro

namespace CascadeSweep
open CascadeSource

def Sweep (a b : Nat) : Prop := ∃ m, a+2=4*2^m ∧ b%2=1

def Well (a b : Nat) : Prop := b=0 ∨ b=2 ∨ Sweep a b

theorem well_step (a b u v : Nat) (hw : Well a b)
    (he : Cstep a b=some (u,v)) : Well u v := by
  rcases hw with hb | hb | ⟨m, ha, hodd⟩
  · subst b
    simp only [Cstep, if_pos rfl, Option.some.injEq, Prod.mk.injEq] at he
    rcases he with ⟨rfl,rfl⟩
    right; right
    refine ⟨0, by decide, ?_⟩
    omega
  · subst b
    by_cases ha0 : a=0
    · subst a
      simp [Cstep] at he
      rcases he with ⟨rfl,rfl⟩
      left; rfl
    · have ha1 : 1≤a := by omega
      have hd : ¬(2*a ≤ 0) := by omega
      have ht : (6*a+8)%2=0 := by omega
      have hrem : (6*a+8)%4=0 ∨ (6*a+8)%4=2 := by omega
      have he' : some ((6*a+8)/4,(6*a+8)%4)=some (u,v) := by
        simpa [Cstep, ha0, hd] using he
      have huv : u=(6*a+8)/4 ∧ v=(6*a+8)%4 := by simpa using he'.symm
      rcases huv with ⟨rfl,rfl⟩
      rcases hrem with hv | hv
      · left; exact hv
      · right; left; exact hv
  · have hpow : 1≤2^m := Nat.one_le_pow m 2 (by omega)
    have ha_even : a%2=0 := by
      have hmod : (4*2^m)%2=0 := by simp [Nat.mul_mod]
      omega
    have ha_pos : 2≤a := by
      have hm : 4 ≤ 4*2^m := by simpa using Nat.mul_le_mul_left 4 hpow
      omega
    have hbne0 : b≠0 := by omega
    by_cases hb1 : b=1
    · subst b
      simp [Cstep] at he
    · have hb3 : 3≤b := by omega
      let d := b-2
      have hdd : d%2=1 := by dsimp [d]; omega
      by_cases hlarge : 2*a≤d
      · have he' : some (2*a+2,d-2*a)=some (u,v) := by
          simpa [Cstep, hbne0, hb1, d, hlarge] using he
        have huv : u=2*a+2 ∧ v=d-2*a := by simpa using he'.symm
        rcases huv with ⟨rfl,rfl⟩
        right; right
        refine ⟨m+1, ?_, ?_⟩
        · rw [Nat.pow_succ]; omega
        · omega
      · have hpar : d%2≠0 := by omega
        let t := 6*a+d+5
        have ht : t%2=0 := by dsimp [t]; omega
        have hrem : t%4=0 ∨ t%4=2 := by omega
        have he' : some (t/4,t%4)=some (u,v) := by
          simpa [Cstep, hbne0, hb1, d, hlarge, hpar, t] using he
        have huv : u=t/4 ∧ v=t%4 := by simpa using he'.symm
        rcases huv with ⟨rfl,rfl⟩
        rcases hrem with hv | hv
        · left; exact hv
        · right; left; exact hv

/-- Every reset predecessor in the invariant phase-language lies in one
    of the two image classes: odd-exit residue two, or an even-exit band. -/
theorem reset_predecessor (a b u : Nat) (hw : Well a b)
    (he : Cstep a b=some (u,0)) :
    u%3=2 ∨ ∃m, 6*2^m-1 ≤ u ∧ u ≤ 8*2^m-3 := by
  rcases hw with hb | hb | ⟨m, ha, hodd⟩
  · subst b
    simp [Cstep] at he
  · subst b
    by_cases ha0 : a=0
    · subst a
      simp [Cstep] at he
      rcases he with rfl
      left; decide
    · have hd : ¬(2*a≤0) := by omega
      have he' : some ((6*a+8)/4,(6*a+8)%4)=some (u,0) := by
        simpa [Cstep, ha0, hd] using he
      have huv : u=(6*a+8)/4 ∧ 0=(6*a+8)%4 := by simpa using he'.symm
      rcases huv with ⟨hu,hv⟩
      have hdiv : 6*a+8=4*u := by omega
      left
      omega
  · have hpow : 1≤2^m := Nat.one_le_pow m 2 (by omega)
    have ha_even : a%2=0 := by
      have hmod : (4*2^m)%2=0 := by simp [Nat.mul_mod]
      omega
    have ha_pos : 2≤a := by
      have hm : 4 ≤ 4*2^m := by simpa using Nat.mul_le_mul_left 4 hpow
      omega
    have hbne0 : b≠0 := by omega
    by_cases hb1 : b=1
    · subst b
      simp [Cstep] at he
    · have hb3 : 3≤b := by omega
      let d := b-2
      have hdd : d%2=1 := by dsimp [d]; omega
      by_cases hlarge : 2*a≤d
      · have he' : some (2*a+2,d-2*a)=some (u,0) := by
          simpa [Cstep, hbne0, hb1, d, hlarge] using he
        have hzero : d-2*a=0 := by simpa using congrArg Prod.snd (Option.some.inj he')
        omega
      · have hpar : d%2≠0 := by omega
        let t := 6*a+d+5
        have he' : some (t/4,t%4)=some (u,0) := by
          simpa [Cstep, hbne0, hb1, d, hlarge, hpar, t] using he
        have huv : u=t/4 ∧ 0=t%4 := by simpa using he'.symm
        rcases huv with ⟨hu,hv⟩
        have hdiv : t=4*u := by omega
        have ha6 : 6*a+12=24*2^m := by omega
        right
        refine ⟨m, ?_, ?_⟩
        · dsimp [t] at hdiv
          omega
        · dsimp [t] at hdiv
          omega

inductive ReachC : (Nat × Nat) → (Nat × Nat) → Prop where
  | refl (x : Nat × Nat) : ReachC x x
  | push {x y z : Nat × Nat} : ReachC x y →
      Cstep y.1 y.2 = some z → ReachC x z

theorem well_reachable {x y : Nat × Nat} (h : ReachC x y)
    (hx : Well x.1 x.2) : Well y.1 y.2 := by
  induction h with
  | refl => exact hx
  | push hstep he ih =>
    exact well_step _ _ _ _ ih he

/-- An all-time source-C-episode exclusion from the genuine post-initial root C(2,0):
    any t outside the two permitted return-image families cannot be visited. -/
theorem root_excludes_nonimage (t : Nat)
    (hodd : t%3 ≠ 2)
    (heven : ∀m, ¬(6*2^m-1 ≤ t ∧ t ≤ 8*2^m-3)) :
    ¬ ReachC (2,0) (t,0) := by
  intro hr
  cases hr with
  | refl =>
    exact hodd (by decide)
  | push hprev he =>
    have hw : Well _ _ := well_reachable hprev (Or.inl rfl)
    rcases reset_predecessor _ _ t hw he with hres | ⟨m, hband⟩
    · exact hodd hres
    · exact heven m hband

#print axioms root_excludes_nonimage
#print axioms reset_predecessor
#print axioms well_step
end CascadeSweep
