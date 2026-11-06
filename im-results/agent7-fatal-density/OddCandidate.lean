import RayForkPrune
set_option maxHeartbeats 0
namespace CascadeOddCandidate
open CascadeOddRay CascadeFiveForced CascadeRayForkPrune CascadeResetInverse

private theorem power_quarter (n:Nat) (hn:6≤n):
    2^n=4*2^(n-2):=by
  have he:n=(n-2)+2:=by omega
  calc
    2^n=2^((n-2)+2):=congrArg (fun t:Nat=>2^t) he
    _=4*2^(n-2):=by rw[Nat.pow_add];omega

/-- Every integral quotient d of the near-top signed ray numerator Z/9
    generates an authentic source first-reset odd t=1 predecessor q, with
    the exact reset-level band and both original grammar equations checked. -/
theorem one_odd_parent_exists (n j d:Nat) (hn:6≤n)
    (hmargin:16*deficit n j+27*n+16≤2^n)
    (hd:9*d+2*deficit n j=8*2^n+5):
    ∃q, OddParent q (ray n j) ∧
      q+2*2^n+n+3=4*d:=by
  have hp:=power_quarter n hn
  have hb:deficit n j≤2^n:=by omega
  have hray:ray n j+deficit n j=4*2^n:=by
    dsimp [ray]
    omega
  have heq:9*d=2*ray n j+5:=by omega
  have hpositive:2*2^n+n+3≤4*d:=by omega
  let q:=4*d-(2*2^n+n+3)
  have hq:q+2*2^n+n+3=4*d:=by dsimp[q];omega
  have hodd:d%2=1:=by omega
  have hband:6*2^(n-2)+1≤2*d∧2*d≤8*2^(n-2)-1:=by omega
  have hin:OddParent q (ray n j):=by
    refine ⟨n-2,1,d,hodd,?_,?_,?_⟩
    · simpa only [show (2:Nat)^1=2 by decide, Nat.mul_comm] using hband
    · have h9:(3:Nat)^(1+1)=9:=by decide
      rw[h9]
      omega
    · have h2:(2:Nat)^1=2:=by decide
      rw[h2]
      have hpow:8*2^(n-2)=2*2^n:=by omega
      rw[hpow]
      omega
  exact ⟨q,hin,hq⟩

/-- The candidate actually exists and is source-genuine but cannot be attached
    to the true blank root whenever its Z/9 quotient is 1 modulo 3. -/
theorem quotient_one_genuine_branch_dead (n j d:Nat) (hn:6≤n)
    (hsector:n%6=4∨n%6=5)
    (hmargin:16*deficit n j+27*n+16≤2^n)
    (hd:9*d+2*deficit n j=8*2^n+5)
    (hmodd:d%3=1):
    ∃q, OddParent q (ray n j) ∧
      ¬CascadeSweep.ReachC (2,0) (q,0):=by
  obtain ⟨q,hodd,hq⟩:=one_odd_parent_exists n j d hn hmargin hd
  exact ⟨q,hodd,odd_tone_quotient_one_dead n j q d hn hsector
    hmargin hd hq hmodd⟩

#print axioms one_odd_parent_exists
#print axioms quotient_one_genuine_branch_dead
end CascadeOddCandidate
