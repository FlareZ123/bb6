import SecondEven

set_option maxHeartbeats 0

namespace CascadeAgent10Four
open CascadeResetInverse CascadeUniformFatal CascadeManyShield CascadeSweep

def thirdPred (n : Nat) : Nat := 4*2^n-15*n-25
def fourthPred (n : Nat) : Nat := 4*2^n-31*n-49

private theorem pow_period_six (n : Nat) : 2^(n+6)%9 = 2^n%9 := by
  rw [Nat.pow_add]
  simp [Nat.mul_mod]

private theorem pow_mod_six (n : Nat) : 2^n%9 = 2^(n%6)%9 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n < 6
    · simp [Nat.mod_eq_of_lt hn]
    · have hm : n-6<n := by omega
      have he : n=(n-6)+6 := by omega
      rw [he,pow_period_six]
      rw [ih (n-6) hm]
      have hemod : ((n-6)+6)%6=(n-6)%6 := by omega
      rw [hemod]

private theorem ray_bound (n : Nat) (hn: 10 ≤ n) : 31*n+49 ≤ 2^n := by
  have h : ∀ k:Nat, 31*(k+10)+49 ≤ 2^(k+10) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
       rw [show k+1+10=k+10+1 by omega,Nat.pow_succ]
       omega
  have he : n=(n-10)+10 := by omega
  rw [he]
  exact h (n-10)

private theorem ray2_nondiv9 (n:Nat) (hn:10≤n)
    (hres:n%18=10 ∨ n%18=17) : (2*secondPred n+5)%9 ≠ 0 := by
  have hb := ray_bound n hn
  have hr:secondPred n+7*n+13 = 4*2^n := by dsimp [secondPred]; omega
  have hp := pow_mod_six n
  rcases hres with h|h
  · have hm:n%6=4 := by omega
    have hm9:2^n%9=7:=by rw [hp,hm]
    omega
  · have hm:n%6=5 := by omega
    have hm9:2^n%9=5:=by rw [hp,hm]
    omega

private theorem ray3_nondiv9 (n:Nat) (hn:10≤n)
    (hres:n%18=10 ∨ n%18=17) : (2*thirdPred n+5)%9 ≠ 0 := by
  have hb := ray_bound n hn
  have hr:thirdPred n+15*n+25 = 4*2^n := by dsimp [thirdPred]; omega
  have hp := pow_mod_six n
  rcases hres with h|h
  · have hm:n%6=4 := by omega
    have hm9:2^n%9=7:=by rw [hp,hm]
    omega
  · have hm:n%6=5 := by omega
    have hm9:2^n%9=5:=by rw [hp,hm]
    omega

private theorem power_min (n : Nat) (hn : 4 ≤ n) : 6 ≤ 2^n := by
  have h := Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) hn
  have hb : 6 ≤ 2^4 := by decide
  omega

/-- A near-top dyadic reset target cannot have any odd first-parent branch
    with zero two-adic drain; the would-be input falls in a dyadic gap. -/
theorem near_top_no_odd_tzero (u n : Nat) (hn : 4 ≤ n)
    (hl : 3*2^n ≤ u) (hu : u ≤ 4*2^n) :
    ¬ ∃ k d, (6*2^k+1 ≤ d ∧ d ≤ 8*2^k-1) ∧ 2*u+5=3*d := by
  rintro ⟨k,d,⟨hlo,hhi⟩,heq⟩
  have hp : 6 ≤ 2^n := power_min n hn
  have hdlow : 2*2^n < d := by omega
  have hdhigh : d < 3*2^n := by omega
  by_cases hk : k+2 ≤ n
  · have hpow : 2^(k+2) ≤ 2^n := Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) hk
    have hh : 2^(k+2) = 4*2^k := by rw [Nat.pow_add]; omega
    rw [hh] at hpow
    omega
  · have hnk : n ≤ k+1 := by omega
    have hpow : 2^n ≤ 2^(k+1) := Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) hnk
    have hh : 2^(k+1) = 2*2^k := by rw [Nat.pow_succ]; omega
    rw [hh] at hpow
    omega

/-- Every exact first-return parent is forced to be the unique even parent
    for a near-top target whose 2u+5 is not divisible by nine. -/
theorem any_parent_near_top (u n k h q : Nat) (hn : 4 ≤ n)
    (hl : 3*2^n ≤ u) (hu : u ≤ 4*2^n)
    (hmod : (2*u+5)%9 ≠ 0)
    (hb : 6*2^k-1 ≤ u ∧ u ≤ 8*2^k-3)
    (heq : 2*u = 8*2^k+h+k) (hq : ResetParent q u) : q=h := by
  rcases hq with ⟨j,hj,heqj⟩ | ⟨j,t,d,hd,hj,hout,heqj⟩
  · have he : j=k := even_band_scale_unique u j k hj hb
    rw [he] at heqj
    omega
  · by_cases ht : t=0
    · subst t
      have ht0 : 2*u+5=3*d := by simpa using hout
      exact False.elim (near_top_no_odd_tzero u n hn hl hu ⟨j,d,by simpa using hj,ht0⟩)
    · have ht1 : 1≤t := by omega
      have hex : t+1=2+(t-1) := by omega
      have hz : 3^(t+1)%9=0 := by
        rw [hex,Nat.pow_add]
        simp
      have hdiv : (2*u+5)%9=0 := by
        rw [hout,Nat.mul_mod,hz]
        simp
      exact False.elim (hmod hdiv)

private theorem ray_band2 (n : Nat) (hn:10≤n) :
    3*2^n ≤ secondPred n ∧ secondPred n ≤ 4*2^n ∧
    6*2^(n-1)-1 ≤ secondPred n ∧ secondPred n ≤ 8*2^(n-1)-3 := by
  have hb := ray_bound n hn
  have he : 2^n=2*2^(n-1) := by
    have hf : 2^n=2^((n-1)+1) := congrArg (fun m : Nat => 2^m) (by omega)
    rw [Nat.pow_succ] at hf
    omega
  dsimp [secondPred]
  rw [he]
  omega

private theorem ray_band3 (n : Nat) (hn:10≤n) :
    3*2^n ≤ thirdPred n ∧ thirdPred n ≤ 4*2^n ∧
    6*2^(n-1)-1 ≤ thirdPred n ∧ thirdPred n ≤ 8*2^(n-1)-3 := by
  have hb := ray_bound n hn
  have he : 2^n=2*2^(n-1) := by
    have hf : 2^n=2^((n-1)+1) := congrArg (fun m : Nat => 2^m) (by omega)
    rw [Nat.pow_succ] at hf
    omega
  dsimp [thirdPred]
  rw [he]
  omega

private theorem second_to_third (n:Nat) (hn:10≤n) :
    ResetParent (thirdPred n) (secondPred n) := by
  have hb := ray_band2 n hn
  have hbound := ray_bound n hn
  have hr : 2*secondPred n=8*2^(n-1)+thirdPred n+(n-1) := by
    have he : 2^n=2*2^(n-1) := by
      have hf : 2^n=2^((n-1)+1) := congrArg (fun m : Nat => 2^m) (by omega)
      rw [Nat.pow_succ] at hf; omega
    dsimp [secondPred,thirdPred]
    rw [he]
    omega
  exact Or.inl ⟨n-1,⟨hb.2.2.1,hb.2.2.2⟩,hr⟩

private theorem third_to_fourth (n:Nat) (hn:10≤n) :
    ResetParent (fourthPred n) (thirdPred n) := by
  have hb := ray_band3 n hn
  have hbound := ray_bound n hn
  have hr : 2*thirdPred n=8*2^(n-1)+fourthPred n+(n-1) := by
    have he : 2^n=2*2^(n-1) := by
      have hf : 2^n=2^((n-1)+1) := congrArg (fun m : Nat => 2^m) (by omega)
      rw [Nat.pow_succ] at hf; omega
    dsimp [thirdPred,fourthPred]
    rw [he]
    omega
  exact Or.inl ⟨n-1,⟨hb.2.2.1,hb.2.2.2⟩,hr⟩

private theorem unique_second_to_third (q n:Nat) (hn:10≤n)
    (hres:n%18=10 ∨ n%18=17)
    (hq:ResetParent q (secondPred n)) : q=thirdPred n := by
  have hb := ray_band2 n hn
  have hbound := ray_bound n hn
  have he : 2^n=2*2^(n-1) := by
    have hf : 2^n=2^((n-1)+1) := congrArg (fun m : Nat => 2^m) (by omega)
    rw [Nat.pow_succ] at hf; omega
  have hr : 2*secondPred n=8*2^(n-1)+thirdPred n+(n-1) := by
    dsimp [secondPred,thirdPred]
    rw [he]
    omega
  exact any_parent_near_top (secondPred n) n (n-1) (thirdPred n) q
    (by omega) hb.1 hb.2.1 (ray2_nondiv9 n hn hres)
    ⟨hb.2.2.1,hb.2.2.2⟩ hr hq

private theorem unique_third_to_fourth (q n:Nat) (hn:10≤n)
    (hres:n%18=10 ∨ n%18=17)
    (hq:ResetParent q (thirdPred n)) : q=fourthPred n := by
  have hb := ray_band3 n hn
  have hbound := ray_bound n hn
  have he : 2^n=2*2^(n-1) := by
    have hf : 2^n=2^((n-1)+1) := congrArg (fun m : Nat => 2^m) (by omega)
    rw [Nat.pow_succ] at hf; omega
  have hr : 2*thirdPred n=8*2^(n-1)+fourthPred n+(n-1) := by
    dsimp [thirdPred,fourthPred]
    rw [he]
    omega
  exact any_parent_near_top (thirdPred n) n (n-1) (fourthPred n) q
    (by omega) hb.1 hb.2.1 (ray3_nondiv9 n hn hres)
    ⟨hb.2.2.1,hb.2.2.2⟩ hr hq

/-- In two surviving all-index congruence classes, actual blank-root
    reachability of the second predecessor is equivalent to that of the
    fourth, with two uniquely forced genuine source reset edges. -/
theorem second_reachable_iff_fourth (n:Nat) (hn:10≤n)
    (hres:n%18=10 ∨ n%18=17) :
    ReachC (2,0) (secondPred n,0) ↔ ReachC (2,0) (fourthPred n,0) := by
  have he1 := second_to_third n hn
  have he2 := third_to_fourth n hn
  have hb := ray_bound n hn
  have hne2 : secondPred n ≠ 2 := by dsimp [secondPred]; omega
  have hne3 : thirdPred n ≠ 2 := by dsimp [thirdPred]; omega
  constructor
  · intro hroot
    have hc : ResetChain 2 (secondPred n) := (root_reset_chain_iff (secondPred n)).mp hroot
    obtain ⟨q,hchain,hparent⟩ := reset_chain_last hc hne2
    have hforced := unique_second_to_third q n hn hres hparent
    rw [hforced] at hchain
    have hc3 : ResetChain 2 (thirdPred n) := hchain
    obtain ⟨q2,hchain2,hparent2⟩ := reset_chain_last hc3 hne3
    have hforced2 := unique_third_to_fourth q2 n hn hres hparent2
    rw [hforced2] at hchain2
    exact (root_reset_chain_iff (fourthPred n)).mpr hchain2
  · intro hroot
    have hc : ResetChain 2 (fourthPred n) := (root_reset_chain_iff (fourthPred n)).mp hroot
    exact (root_reset_chain_iff (secondPred n)).mpr ((hc.append he2).append he1)

/-- Four uniformly forced exact first-reset inverse steps for the genuine
    fatal source heights in n≡10,17 (mod 18); still no nonhalting result. -/
theorem genuine_fatal_iff_fourth (n:Nat) (hn:10≤n)
    (hres:n%18=10 ∨ n%18=17) :
    ReachC (2,0) (fatal n,0) ↔ ReachC (2,0) (fourthPred n,0) := by
  have hres4 : n%18=10 ∨ n%18=11 ∨ n%18=16 ∨ n%18=17 := by
    rcases hres with h|h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
  exact (genuine_fatal_iff_second_even n hn hres4).trans
    (second_reachable_iff_fourth n hn hres)

#print axioms near_top_no_odd_tzero
#print axioms any_parent_near_top
#print axioms unique_second_to_third
#print axioms unique_third_to_fourth
#print axioms genuine_fatal_iff_fourth
end CascadeAgent10Four
