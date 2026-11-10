import ForkCore
set_option maxHeartbeats 0
namespace BB746Fork

abbrev ResetChain := CascadeResetInverse.ResetChain

private theorem last {s u : Nat} (h : ResetChain s u) (hne : u≠s) :
    ∃ q, ResetChain s q ∧ ResetParent q u := by
  cases h with
  | root => exact False.elim (hne rfl)
  | @append q u h p => exact ⟨q,h,p⟩

private theorem no_even_band (k u j : Nat) (hk : 1≤k)
    (hl : 4*2^k-3<u) (hh : u<6*2^k-1) :
    ¬(6*2^j-1≤u ∧ u≤8*2^j-3) := by
  intro hj
  by_cases hlt : j<k
  · have hp : 2^(j+1)≤2^k := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.pow_succ] at hp
    have hpj : 1≤2^j := Nat.one_le_pow j 2 (by decide)
    omega
  · have hp : 2^k≤2^j := Nat.pow_le_pow_right (by decide) (by omega)
    have hpk : 1≤2^k := Nat.one_le_pow k 2 (by decide)
    omega

private theorem gap_no_parent (k u : Nat) (hk : 1≤k)
    (hl : 4*2^k-3<u) (hh : u<6*2^k-1)
    (hmod : u%3≠2) (q : Nat) : ¬ResetParent q u := by
  intro hp
  rcases hp with ⟨j,hband,_⟩ | ⟨j,t,d,_,_,hout,_⟩
  · exact no_even_band k u j hk hl hh hband
  · have hpow : 3^(t+1)=3*3^t := by rw [Nat.pow_succ]; omega
    rw [hpow] at hout
    have h3 : 2*u+5=3*(3^t*d) := by simpa only [Nat.mul_assoc] using hout
    have hm : u%3=2 := by omega
    exact hmod hm

private theorem gap_no_root (k u : Nat) (hk : 1≤k)
    (hl : 4*2^k-3<u) (hh : u<6*2^k-1)
    (hmod : u%3≠2) : ¬ResetChain 2 u := by
  have hne : u≠2 := by
    have hp : 2≤2^k := by
      have hb : 2^1≤2^k := Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) hk
      simpa using hb
    omega
  intro hr
  obtain ⟨q,_,hq⟩ := last hr hne
  exact gap_no_parent k u hk hl hh hmod q hq

private theorem only_even_parent (k u z q : Nat)
    (hband : 6*2^k-1≤u ∧ u≤8*2^k-3)
    (heq : 2*u=8*2^k+z+k)
    (hmod : u%3≠2) (hp : ResetParent q u) : q=z := by
  rcases hp with ⟨j,hbj,heqj⟩ | ⟨j,t,d,_,_,hout,_⟩
  · have hjk : j=k := even_unique u j k hbj hband
    rw [hjk] at heqj
    omega
  · have hpow : 3^(t+1)=3*3^t := by rw [Nat.pow_succ]; omega
    rw [hpow] at hout
    have h3 : 2*u+5=3*(3^t*d) := by simpa only [Nat.mul_assoc] using hout
    have hm : u%3=2 := by omega
    exact False.elim (hmod hm)

/-- Two-layer, genuine-root predecessor obstruction. The hypotheses are
source reset-height statements. No finite-search cutoff is used. -/
theorem two_layer_root_exclusion (k x h y z : Nat)
    (hk : 4≤k)
    (hxhigh : 6*2^k≤x)
    (hxguard : x+k+5<8*2^k)
    (hxnarrow : 4*x+10<27*2^k)
    (hxnot81 : (2*x+5)%81≠0)
    (hxeven : 2*x=8*2^k+h+k)
    (hxodd : 27*(2*2^k+y+k+3)=8*(2*x+5))
    (hxband : 6*2^k-1≤x ∧ x≤8*2^k-3)
    (hhgaplo : 4*2^k-3<h) (hhgaphi : h<6*2^k-1)
    (hhmod : h%3≠2)
    (hyband : 6*2^(k-2)-1≤y ∧ y≤8*2^(k-2)-3)
    (hyrel : 2*y=8*2^(k-2)+z+(k-2))
    (hymod : y%3≠2)
    (hzgaplo : 4*2^(k-2)-3<z) (hzgaphi : z<6*2^(k-2)-1)
    (hzmod : z%3≠2) :
    ¬ResetChain 2 x := by
  have hnoth := gap_no_root k h (by omega) hhgaplo hhgaphi hhmod
  have hnotz := gap_no_root (k-2) z (by omega) hzgaplo hzgaphi hzmod
  have hnoty : ¬ResetChain 2 y := by
    intro hr
    have hyne : y≠2 := by omega
    obtain ⟨q,hq,hp⟩ := last hr hyne
    have hqz := only_even_parent (k-2) y z q hyband hyrel hymod hp
    rw [hqz] at hq
    exact hnotz hq
  intro hr
  have hxne : x≠2 := by omega
  obtain ⟨q,hq,hp⟩ := last hr hxne
  rcases narrow_exact_two k x h y q (by omega) hxhigh hxguard
     hxnarrow hxnot81 hxeven hxodd hxband hp with rfl | rfl
  · exact hnoth hq
  · exact hnoty hq

#print axioms two_layer_root_exclusion
end BB746Fork
