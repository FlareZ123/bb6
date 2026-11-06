import RayTwoTierNoTwo
set_option maxHeartbeats 0
namespace CascadeRayTThreeGap
open CascadeResetInverse CascadeSweep CascadeOddRay CascadeFiveForced
open CascadeRayTwoTierNoTwo CascadeRayTwoTierSelector CascadeForkOddDead

private theorem odd_band_unique (u k l:Nat)
  (hk:6*2^k+1≤u ∧ u≤8*2^k-1)
  (hl:6*2^l+1≤u ∧ u≤8*2^l-1):k=l:=by
  by_cases he:k=l
  · exact he
  by_cases hklt:k<l
  · have hp:2^(k+1)≤2^l:=Nat.pow_le_pow_right (by decide:0<(2:Nat)) (by omega)
    rw[Nat.pow_succ] at hp
    omega
  · have hp:2^(l+1)≤2^k:=Nat.pow_le_pow_right (by decide:0<(2:Nat)) (by omega)
    rw[Nat.pow_succ] at hp
    omega

/-- Source genuine t=3 odd parents near the top of any canonical ray
    are confined to a unique scale n-3 and then to a reset-image gap. -/
theorem ray_tthree_parent_gap (n j k d q:Nat) (hn:20≤n)
  (hm:2048*deficit n j+16384*n+16384≤2^n)
  (hz:2*ray n j+5=81*d)
  (hb:6*2^k+1≤8*d ∧ 8*d≤8*2^k-1)
  (he:16*d=8*2^k+q+k+5):
  2^(n-1)<q ∧ 2*q+2<3*2^(n-1):=by
  have hp:2^n=8*2^(n-3):=by
    have he:n=(n-3)+3:=by omega
    calc
      2^n=2^((n-3)+3):=congrArg (fun x:Nat=>2^x) he
      _=8*2^(n-3):=by rw[Nat.pow_add];omega
  have hs:2^n=2*2^(n-1):=by
    have he:n=(n-1)+1:=by omega
    calc
      2^n=2^((n-1)+1):=congrArg (fun x:Nat=>2^x) he
      _=2*2^(n-1):=by rw[Nat.pow_succ];omega
  have hr:ray n j+deficit n j=4*2^n:=by dsimp[ray];omega
  have hband:6*2^(n-3)+1≤8*d ∧ 8*d≤8*2^(n-3)-1:=by
    constructor <;> omega
  have hk:k=n-3:=odd_band_unique (8*d) k (n-3) hb hband
  rw[hk] at he
  have hlinear:81*q+32*deficit n j+81*n+82=47*2^n:=by omega
  constructor <;> omega

/-- Genuine blank-root reachability excludes every high-margin t=3
    off-ray parent whose residue is 0 or 1 modulo 3. -/
theorem ray_tthree_parent_dead (n j k d q:Nat) (hn:20≤n)
  (hm:2048*deficit n j+16384*n+16384≤2^n)
  (hz:2*ray n j+5=81*d)
  (hb:6*2^k+1≤8*d ∧ 8*d≤8*2^k-1)
  (he:16*d=8*2^k+q+k+5)
  (hmod:q%3≠2):
  ¬ReachC (2,0) (q,0):=by
  have hh:=ray_tthree_parent_gap n j k d q hn hm hz hb he
  exact root_excludes_nonimage q hmod
    (gap_avoids_even_images (n-1) q (by omega) hh.1 hh.2)

#print axioms ray_tthree_parent_gap
#print axioms ray_tthree_parent_dead
end CascadeRayTThreeGap
