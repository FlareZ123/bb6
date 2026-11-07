import RayTThreeGap
import RayNoSeamResidue
import RayTThreeLowGeometry
set_option maxHeartbeats 0
namespace CascadeTThreeLow
open CascadeResetInverse CascadeSweep CascadeUniformFatal CascadeOddRay CascadeSeam CascadeForkOddDead

private theorem odd_band_unique (u k l:Nat)
  (hk:6*2^k+1≤u ∧ u≤8*2^k-1)
  (hl:6*2^l+1≤u ∧ u≤8*2^l-1):k=l:=by
  by_cases he:k=l
  · exact he
  by_cases hkl:k<l
  · have hp:2^(k+1)≤2^l:=Nat.pow_le_pow_right (by decide:0<(2:Nat)) (by omega)
    rw[Nat.pow_succ] at hp
    omega
  · have hp:2^(l+1)≤2^k:=Nat.pow_le_pow_right (by decide:0<(2:Nat)) (by omega)
    rw[Nat.pow_succ] at hp
    omega

/-- Uniform authentic blank-source exclusion of q in the t3 middle gap
    whenever its odd numerator has valuation at most one. Exact parent
    grammar is exhausted: no even parent; no t>=1 odd parent; every t0
    predecessor enters a forbidden even-image gap with residue different from 2. -/
theorem third_low_mid_gap_root_dead (n q:Nat) (hn:20≤n)
  (hsector:n%6=4 ∨ n%6=5)
  (hlo:9*2^(n-4)+5*n+40≤q)
  (hhi:q+5*n+40≤10*2^(n-4))
  (hnot9:(2*q+5)%9≠0) :
  ¬ReachC (2,0) (q,0) := by
  intro hroot
  have hqne:q≠2:=by
    have hp:0<2^(n-4):=Nat.pow_pos (by decide)
    omega
  have hchain:ResetChain 2 q:=(root_reset_chain_iff q).mp hroot
  obtain ⟨h,hparents,hparent⟩:=reset_chain_last hchain hqne
  have hscale:2^(n-1)=8*2^(n-4):=by
    have hh:n-1=(n-4)+3:=by omega
    calc
      2^(n-1)=2^((n-4)+3):=congrArg (fun x:Nat=>2^x) hh
      _=8*2^(n-4):=by rw[Nat.pow_add];simp only [show (2:Nat)^3=8 by decide];ac_rfl
  have hqgap:2^(n-1)<q ∧ 2*q+2<3*2^(n-1):=by
    rw[hscale]
    constructor <;> omega
  rcases hparent with ⟨k,hb,heq⟩ | ⟨k,t,d,hd,hb,hout,heq⟩
  · exact False.elim ((gap_avoids_even_images (n-1) q (by omega)
      hqgap.1 hqgap.2) k hb)
  · by_cases ht:t=0
    · subst t
      have hdq:3*d=2*q+5:=by simpa using hout.symm
      have hbb:6*2^(n-4)+1≤d ∧ d≤8*2^(n-4)-1:=by
        constructor <;> omega
      have hk:k=n-4:=odd_band_unique d k (n-4) (by simpa using hb) hbb
      have hhe:2*d=8*2^(n-4)+h+(n-4)+5:=by
        rw[hk] at heq
        simpa using heq
      have hgeom:=third_precursor_gap n q d h hn hlo hhi hdq hhe
      have hmod:=third_precursor_residue n q d h
        (source_even_residue n hn hsector) hdq hnot9 hhe
      have hreach:ReachC (2,0) (h,0):=(root_reset_chain_iff h).mpr hparents
      exact (root_excludes_nonimage h hmod
        (gap_avoids_even_images (n-2) h (by omega) hgeom.1 hgeom.2)) hreach
    · have ht1:1≤t:=by omega
      have hex:t+1=2+(t-1):=by omega
      have hz:3^(t+1)%9=0:=by rw[hex,Nat.pow_add];simp
      have hzero:(2*q+5)%9=0:=by rw[hout,Nat.mul_mod,hz];simp
      exact hnot9 hzero

/-- A genuine source-C t=3 odd inverse of a high-margin canonical
    #746 ray reset with a low-valuation precursor is excluded from the
    actual C(2,0) blank-reset orbit, uniformly in n,j. -/
theorem ray_tthree_low_source_dead (n j k d q:Nat) (hn:20≤n)
 (hsector:n%6=4 ∨ n%6=5)
 (hm:2048*deficit n j+16384*n+16384≤2^n)
 (hz:2*ray n j+5=81*d)
 (hb:6*2^k+1≤8*d ∧ 8*d≤8*2^k-1)
 (he:16*d=8*2^k+q+k+5)
 (hnot9:(2*q+5)%9≠0):
 ¬ReachC (2,0) (q,0) := by
  have hpp:2^n=8*2^(n-3):=by
    have hp1:2^n=16*2^(n-4):=(pow_shift n hn).1
    have hp2:2^(n-3)=2*2^(n-4):=(pow_shift n hn).2.2
    omega
  have hray:ray n j+deficit n j=4*2^n:=by
    have hD:deficit n j≤4*2^n:=by omega
    dsimp[ray]
    omega
  have hband:6*2^(n-3)+1≤8*d ∧ 8*d≤8*2^(n-3)-1:=by
    constructor <;> omega
  have hk:k=n-3:=odd_band_unique (8*d) k (n-3) hb hband
  have heq:16*d=2^n+q+(n-3)+5:=by
    rw[hk] at he
    rw[hpp]
    exact he
  have hlinear:81*q+32*deficit n j+81*n+82=47*2^n:=by omega
  obtain ⟨hlo,hhi⟩:=third_parent_interval n (deficit n j) q hn hm hlinear
  exact third_low_mid_gap_root_dead n q hn hsector hlo hhi hnot9

#print axioms third_low_mid_gap_root_dead
#print axioms ray_tthree_low_source_dead
end CascadeTThreeLow
