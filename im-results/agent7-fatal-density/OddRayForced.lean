import UniqueEvenBand
set_option maxHeartbeats 0
namespace CascadeOddRay

/-- Deficit from the upper edge of the fatal-height dyadic band after j even inverse steps. -/
def deficit (n:Nat):Nat→Nat
  | 0=>n+4
  | j+1=>2*deficit n j+(n-1)

def ray (n j:Nat):Nat:=4*2^n-deficit n j

private theorem deficit_min (n j:Nat):3≤deficit n j:=by
  induction j with
  | zero=>simp [deficit]
  | succ j ih=>simp only [deficit];omega

private theorem deficit_two_mod (n j:Nat):
    deficit n (j+2)%3=deficit n j%3:=by
  simp only [deficit]
  omega

private theorem odd_deficit_mod (n m:Nat) (hn:1≤n):
    deficit n (2*m+1)%3=1:=by
  induction m with
  | zero=>simp [deficit];omega
  | succ m ih=>
    have hper:=deficit_two_mod n (2*m+1)
    have hm:2*(m+1)+1=2*m+1+2:=by omega
    rw [hm,hper]
    exact ih

private theorem pow_mod3 (n:Nat): 2^n%3=1 ∨ 2^n%3=2:=by
  induction n with
  | zero=>exact Or.inl (by decide)
  | succ n ih=>
    rw [Nat.pow_succ,Nat.mul_mod]
    rcases ih with h|h
    · exact Or.inr (by simp [h])
    · exact Or.inl (by simp [h])

private theorem deficit_odd_mod (n j:Nat) (hn:1≤n) (hj:j%2=1):
    deficit n j%3=1:=by
  have hm:j=2*(j/2)+1:=by omega
  rw [hm]
  exact odd_deficit_mod n (j/2) hn

theorem odd_ray_not_two (n j:Nat) (hn:1≤n) (hj:j%2=1)
    (hmargin:deficit n j ≤ 4*2^n):ray n j%3≠2:=by
  have hm:=deficit_odd_mod n j hn hj
  have hcon:ray n j+deficit n j=4*2^n:=by
    dsimp [ray];omega
  have hh:=congrArg (fun x:Nat=>x%3) hcon
  rcases pow_mod3 n with h|h
  · omega
  · omega

private theorem bound_n_pow (n:Nat) (hn:4≤n):n+2≤2^n:=by
  have h: ∀k:Nat,k+4+2≤2^(k+4):=by
    intro k
    induction k with
    | zero=>decide
    | succ k ih=>
      rw [show k+1+4=k+4+1 by omega,Nat.pow_succ]
      omega
  have he:n=(n-4)+4:=by omega
  rw [he]
  exact h (n-4)

private theorem power_halve (n:Nat) (hn:4≤n):
   2^n=2*2^(n-1):=by
  have he:n=(n-1)+1:=by omega
  calc
    2^n=2^((n-1)+1):=congrArg (fun t:Nat=>2^t) he
    _ =2*2^(n-1):=by rw [Nat.pow_succ];omega

private theorem ray_band (n j:Nat) (hn:4≤n)
    (hmargin:deficit n j≤2^n+1):
    6*2^(n-1)-1≤ray n j ∧ ray n j≤8*2^(n-1)-3:=by
  have hmin:=deficit_min n j
  have hp:=power_halve n hn
  dsimp [ray]
  omega

private theorem ray_next_eq (n j:Nat) (hn:4≤n)
    (hmargin:deficit n j≤2^n+1):
    2*ray n j=8*2^(n-1)+ray n (j+1)+(n-1):=by
  have hmin:=deficit_min n j
  have hp:=power_halve n hn
  have hn2:=bound_n_pow n hn
  have hdnext:deficit n (j+1)=2*deficit n j+(n-1):=rfl
  have hb: deficit n j≤4*2^n:=by omega
  have hbnext: deficit n (j+1)≤4*2^n:=by omega
  have h0:ray n j+deficit n j=4*2^n:=by dsimp[ray];omega
  have h1:ray n (j+1)+deficit n (j+1)=4*2^n:=by dsimp[ray];omega
  omega

/-- At every odd inverse-ray depth in the high even band, all source-genuine
    first-reset inverse heights are forced to be the next ray element. -/
theorem odd_ray_parent_iff (n j q:Nat) (hn:4≤n) (hj:j%2=1)
    (hmargin:deficit n j≤2^n+1):
    CascadeResetInverse.ResetParent q (ray n j) ↔ q=ray n (j+1):=by
  have hb:=ray_band n j hn hmargin
  have heq:=ray_next_eq n j hn hmargin
  have hp:1≤2^n:=Nat.one_le_pow n 2 (by decide)
  have hrel:deficit n j≤4*2^n:=by omega
  have hmod:=odd_ray_not_two n j (by omega) hj hrel
  constructor
  · intro hq
    exact CascadeUniformFatal.any_parent_equals_even
      (ray n j) (n-1) (ray n (j+1)) q hb heq hmod hq
  · intro hq
    subst q
    exact Or.inl ⟨n-1,hb,heq⟩

/-- True blank-origin source-C reset reachability equivalence at every
    positive odd ray depth, without a fixed-depth cutoff. -/
theorem odd_ray_root_iff (n j:Nat) (hn:4≤n) (hj:j%2=1)
    (hmargin:deficit n j≤2^n+1):
    CascadeSweep.ReachC (2,0) (ray n j,0) ↔
    CascadeSweep.ReachC (2,0) (ray n (j+1),0):=by
  have hb:=ray_band n j hn hmargin
  have hne:ray n j≠2:=by
    have hp:1≤2^(n-1):=Nat.one_le_pow (n-1) 2 (by decide)
    omega
  constructor
  · intro hr
    have hc:= (CascadeResetInverse.root_reset_chain_iff (ray n j)).mp hr
    obtain ⟨q,hchain,hparent⟩:= CascadeUniformFatal.reset_chain_last hc hne
    have hq: q=ray n (j+1):= (odd_ray_parent_iff n j q hn hj hmargin).mp hparent
    rw [hq] at hchain
    exact (CascadeResetInverse.root_reset_chain_iff (ray n (j+1))).mpr hchain
  · intro hr
    have hc:= (CascadeResetInverse.root_reset_chain_iff (ray n (j+1))).mp hr
    have hstep:CascadeResetInverse.ResetParent (ray n (j+1)) (ray n j):=
      (odd_ray_parent_iff n j (ray n (j+1)) hn hj hmargin).mpr rfl
    exact (CascadeResetInverse.root_reset_chain_iff (ray n j)).mpr
      (CascadeResetInverse.ResetChain.append hc hstep)

#print axioms odd_ray_parent_iff
#print axioms odd_ray_root_iff
#print axioms odd_ray_not_two
end CascadeOddRay
