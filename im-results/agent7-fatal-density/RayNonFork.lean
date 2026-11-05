import FourEven
import OddRayDeep
import RayResidues
set_option maxHeartbeats 0
namespace CascadeFiveForced
open CascadeOddRay CascadeRayPeriod CascadeResetInverse

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

private theorem deficit_min (n j:Nat):3≤deficit n j:=by
  induction j with
  | zero=>simp[deficit]
  | succ j ih=>simp only[deficit];omega

private theorem power_halve (n:Nat) (hn:4≤n):
    2^n=2*2^(n-1):=by
  have he:n=(n-1)+1:=by omega
  calc
    2^n = 2^((n-1)+1):=congrArg (fun t:Nat=>2^t) he
    _ = 2*2^(n-1):=by rw[Nat.pow_succ];omega

theorem ray_band (n j:Nat) (hn:4≤n)
    (hmargin:deficit n j≤2^n):
    3*2^n≤ray n j ∧ ray n j≤4*2^n ∧
    6*2^(n-1)-1≤ray n j ∧ ray n j≤8*2^(n-1)-3:=by
  have hmin:=deficit_min n j
  have hp:=power_halve n hn
  dsimp[ray]
  omega

theorem ray_next_eq (n j:Nat) (hn:4≤n)
    (hmargin:deficit n j≤2^n):
    2*ray n j=8*2^(n-1)+ray n (j+1)+(n-1):=by
  have hmin:=deficit_min n j
  have hp:=power_halve n hn
  have hn2:=bound_n_pow n hn
  have hdnext:deficit n (j+1)=2*deficit n j+(n-1):=rfl
  have hb:deficit n j≤4*2^n:=by omega
  have hbnext:deficit n (j+1)≤4*2^n:=by omega
  have h0:ray n j+deficit n j=4*2^n:=by dsimp[ray];omega
  have h1:ray n (j+1)+deficit n (j+1)=4*2^n:=by dsimp[ray];omega
  omega

theorem signed_ray_eq_numerator (n j:Nat) (hn:4≤n)
    (hmargin:deficit n j≤2^n):
    signedZ n j=(2*ray n j+5:Int):=by
  have hclosed:=deficit_closed n j (by omega:1≤n)
  have hmul: 2^(j+1)*(2*n+3)=2*(deficit n j+(n-1)):=by
    calc
      _ = 2*(2^j*(2*n+3)):=by rw[Nat.pow_succ];ac_rfl
      _ = 2*(deficit n j+(n-1)):=by rw[hclosed]
  have hr:ray n j+deficit n j=4*2^n:=by
    dsimp[ray];omega
  have hab:(8*2^n+2*n+3:Nat)=2*ray n j+5+2^(j+1)*(2*n+3):=by
    rw [hmul]
    omega
  have hnat:(8*2^n+2*n+3:Nat)-2^(j+1)*(2*n+3)=2*ray n j+5:=by omega
  have hle:2^(j+1)*(2*n+3)≤8*2^n+2*n+3:=by omega
  change ((8*2^n+2*n+3:Nat):Int)-
    ((2^(j+1)*(2*n+3):Nat):Int) = 2*(ray n j:Int)+5
  calc
    _ = (((8*2^n+2*n+3:Nat)-2^(j+1)*(2*n+3):Nat):Int) :=
      (Int.ofNat_sub hle).symm
    _ = ((2*ray n j+5:Nat):Int) := congrArg Nat.cast hnat
    _ = 2*(ray n j:Int)+5:=by push_cast;omega

/-- An authentic near-top inverse ray target that is not divisible by nine
    has exactly its single even source first-reset parent. -/
theorem nonfork_parent_iff (n j q:Nat) (hn:4≤n)
    (hmargin:deficit n j≤2^n)
    (hmod:signedZ n j%9≠0):
    ResetParent q (ray n j) ↔ q=ray n (j+1):=by
  have hb:=ray_band n j hn hmargin
  have heq:=ray_next_eq n j hn hmargin
  have hnum:=signed_ray_eq_numerator n j hn hmargin
  have hnum_nat:(2*ray n j+5)%9≠0:=by
    have hmodInt:((2*(ray n j:Int)+5)%9≠0):=by
      rw[←hnum]
      exact hmod
    exact_mod_cast hmodInt
  constructor
  · intro hq
    exact CascadeAgent10Four.any_parent_near_top (ray n j) n (n-1)
      (ray n (j+1)) q hn hb.1 hb.2.1 hnum_nat ⟨hb.2.2.1,hb.2.2.2⟩ heq hq
  · intro hq
    subst q
    exact Or.inl ⟨n-1,⟨hb.2.2.1,hb.2.2.2⟩,heq⟩

/-- An exact genuine blank-root equivalence along any near-top nonfork ray edge. -/
theorem nonfork_root_iff (n j:Nat) (hn:4≤n)
    (hmargin:deficit n j≤2^n)
    (hmod:signedZ n j%9≠0):
    CascadeSweep.ReachC (2,0) (ray n j,0) ↔
    CascadeSweep.ReachC (2,0) (ray n (j+1),0):=by
  have hb:=ray_band n j hn hmargin
  have hne:ray n j≠2:=by
    have hp:1≤2^n:=Nat.one_le_pow n 2 (by decide)
    omega
  constructor
  · intro hr
    have hc:ResetChain 2 (ray n j):=(root_reset_chain_iff (ray n j)).mp hr
    obtain ⟨q,hchain,hparent⟩:=CascadeUniformFatal.reset_chain_last hc hne
    have hq:q=ray n (j+1):=(nonfork_parent_iff n j q hn hmargin hmod).mp hparent
    rw[hq] at hchain
    exact (root_reset_chain_iff (ray n (j+1))).mpr hchain
  · intro hr
    have hc:ResetChain 2 (ray n (j+1)):=(root_reset_chain_iff (ray n (j+1))).mp hr
    have hstep:ResetParent (ray n (j+1)) (ray n j):=
      (nonfork_parent_iff n j (ray n (j+1)) hn hmargin hmod).mpr rfl
    exact (root_reset_chain_iff (ray n j)).mpr (ResetChain.append hc hstep)

#print axioms nonfork_root_iff
#print axioms nonfork_parent_iff
end CascadeFiveForced
