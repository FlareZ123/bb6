import OddCandidate
import RayTriplePeriod
set_option maxHeartbeats 0
namespace CascadeNineFork
open CascadeOddRay CascadeFiveForced CascadeRayForkPrune CascadeResetInverse CascadeRayPeriod

private theorem odd_scale_unique (v k j:Nat)
  (hb:6*2^k+1≤v∧v≤8*2^k-1)
  (hj:6*2^j+1≤v∧v≤8*2^j-1): k=j:=by
  by_cases heq:k=j
  · exact heq
  by_cases hlt:k<j
  · have hp:2^(k+1)≤2^j:=Nat.pow_le_pow_right (by decide:0<(2:Nat)) (by omega)
    have he:2^(k+1)=2*2^k:=by rw[Nat.pow_succ];omega
    rw[he] at hp
    omega
  · have hp:2^(j+1)≤2^k:=Nat.pow_le_pow_right (by decide:0<(2:Nat)) (by omega)
    have he:2^(j+1)=2*2^j:=by rw[Nat.pow_succ];omega
    rw[he] at hp
    omega

private theorem pow_quarter (n:Nat) (hn:6≤n):2^n=4*2^(n-2):=by
  have he:n=(n-2)+2:=by omega
  have hp:2^n=2^((n-2)+2):=congrArg (fun m:Nat=>2^m) he
  rw[Nat.pow_add] at hp
  omega

/-- An authentic signed-ray numerator congruent to 9 modulo 27 admits no
    blank-root-reachable odd first-reset predecessor under the dyadic margin. -/
theorem residue_nine_all_odd_unrooted (n j:Nat) (hn:6≤n)
  (hsector:n%6=4∨n%6=5)
  (hmargin:16*deficit n j+27*n+16≤2^n)
  (h9:signedZ n j%27=9):
  ∀q, OddParent q (ray n j) →
    ¬CascadeSweep.ReachC (2,0) (q,0):=by
  intro q hparent
  obtain ⟨k,t,d,hdodd,htband,heq,hlin⟩:=hparent
  have hm:deficit n j≤2^n:=by omega
  have hb:=ray_band n j (by omega:4≤n) hm
  have hsigned:=signed_ray_eq_numerator n j (by omega:4≤n) hm
  have hnum:(2*ray n j+5)%27=9:=by
    rw[hsigned] at h9
    exact_mod_cast h9
  have ht1:t=1:=by
    by_cases ht0:t=0
    · subst t
      have hz:2*ray n j+5=3*d:=by simpa using heq
      exact False.elim (CascadeAgent10Four.near_top_no_odd_tzero
         (ray n j) n (by omega) hb.1 hb.2.1 ⟨k,d,by simpa using htband,hz⟩)
    · have ht:1≤t:=by omega
      by_cases htone:t=1
      · exact htone
      have ht2:2≤t:=by omega
      have hex:t+1=3+(t-2):=by omega
      have hp3:3^(t+1)%27=0:=by rw[hex,Nat.pow_add];simp
      have hzero:(2*ray n j+5)%27=0:=by rw[heq,Nat.mul_mod,hp3];simp
      exact False.elim (by omega)
  subst t
  have h9d:9*d=2*ray n j+5:=by simpa using heq.symm
  have hray:ray n j+deficit n j=4*2^n:=by dsimp [ray];omega
  have hddef:9*d+2*deficit n j=8*2^n+5:=by omega
  have hpow:=pow_quarter n hn
  have hband:6*2^(n-2)+1≤2*d∧2*d≤8*2^(n-2)-1:=by omega
  have hk:k=n-2:=odd_scale_unique (2*d) k (n-2)
    (by simpa using htband) hband
  rw[hk] at hlin
  have hq:q+2*2^n+n+3=4*d:=by omega
  have hmod:d%3=1:=by omega
  exact CascadeRayForkPrune.odd_tone_quotient_one_dead n j q d hn hsector
    hmargin hddef hq hmod

#print axioms residue_nine_all_odd_unrooted
end CascadeNineFork
