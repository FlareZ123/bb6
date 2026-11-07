import RayTThreeLowRoot
import RayTThreeExtendedGeometry
set_option maxHeartbeats 0
namespace CascadeTThreeLow
open CascadeResetInverse CascadeSweep CascadeUniformFatal CascadeOddRay CascadeRayOddStrip

private theorem odd_scale_unique (u k l:Nat)
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

/-- All-first-reset exact root obstruction in the third-valuation q gap.
    The source q cannot have an even parent, nor an odd t=1/t=2 parent;
    high t>=3 is gated by its numerator modulo 81. Its only remaining
    t=0 parent h lies in a narrower gap and is barred if v3(2h+5)<2. -/
theorem third_mid_gap_two_gate_dead (n q d h:Nat) (hn:20≤n)
 (hlo:9*2^(n-4)+5*n+40≤q)
 (hhi:q+5*n+40≤10*2^(n-4))
 (htight:8*q+40*n+320≤75*2^(n-4))
 (hd:3*d=2*q+5)
 (he:2*d=8*2^(n-4)+h+(n-4)+5)
 (hnot81:(2*q+5)%81≠0)
 (hnot9:(2*h+5)%9≠0) :
 ¬ReachC (2,0) (q,0) := by
  intro hroot
  have hqne:q≠2:=by
    have hp:0<2^(n-4):=Nat.pow_pos (by decide)
    omega
  have hchain:ResetChain 2 q:=(root_reset_chain_iff q).mp hroot
  obtain ⟨a,hparents,hparent⟩:=reset_chain_last hchain hqne
  have hscale:2^(n-1)=8*2^(n-4):=by
    have hh:n-1=(n-4)+3:=by omega
    calc
      2^(n-1)=2^((n-4)+3):=congrArg (fun x:Nat=>2^x) hh
      _=8*2^(n-4):=by rw[Nat.pow_add];simp only [show (2:Nat)^3=8 by decide];ac_rfl
  have hqgap:2^(n-1)<q ∧ 2*q+2<3*2^(n-1):=by
    rw[hscale]
    constructor <;> omega
  rcases hparent with ⟨k,hb,heq⟩ | ⟨k,t,d',hdodd,hb,hout,heq⟩
  · exact False.elim ((gap_avoids_even_images (n-1) q (by omega)
      hqgap.1 hqgap.2) k hb)
  · by_cases ht0:t=0
    · subst t
      have hdd: d'=d:=by
        have hz:2*q+5=3*d':=by simpa using hout
        omega
      subst d'
      have hband:6*2^(n-4)+1≤d ∧ d≤8*2^(n-4)-1:=by
        constructor <;> omega
      have hk:k=n-4:=odd_scale_unique d k (n-4) (by simpa using hb) hband
      have ha:a=h:=by
        rw[hk] at heq
        simp only [show (2:Nat)^0=1 by decide] at heq
        omega
      subst a
      have hgeom:=third_precursor_narrow n q d h hn hlo htight hd he
      have hreach:ReachC (2,0) (h,0):=(root_reset_chain_iff h).mpr hparents
      exact (narrow_gap_root_excluded (n-2) h (by omega) hgeom.1 hgeom.2
        (Or.inr hnot9)) hreach
    · by_cases ht1:t=1
      · subst t
        have hz:2*q+5=9*d':=by simpa using hout
        have hgeom:=third_tone_gap n q d' hn hlo hhi hz
        exact False.elim ((gap_avoids_odd_images (n-2) (2*d')
          hgeom.1 hgeom.2) k (by simpa using hb))
      · by_cases ht2:t=2
        · subst t
          have hz:2*q+5=27*d':=by simpa using hout
          have hgeom:=third_ttwo_gap n q d' hn hlo hhi hz
          exact False.elim ((gap_avoids_odd_images (n-3) (4*d')
            hgeom.1 hgeom.2) k (by simpa using hb))
        · have ht3:3≤t:=by omega
          have hex:t+1=4+(t-3):=by omega
          have hpow:3^(t+1)%81=0:=by rw[hex,Nat.pow_add];simp
          have hzero:(2*q+5)%81=0:=by rw[hout,Nat.mul_mod,hpow];simp
          exact hnot81 hzero

/-- Transport the two-gate t3 obstruction to the complete genuine source
    odd inverse relation along any high-margin canonical ray. The literal
    extra d0,h equations identify the t=0 first parent of q. -/
theorem ray_tthree_two_gate_source_dead (n j k d q d0 h:Nat) (hn:20≤n)
 (hm:2048*deficit n j+16384*n+16384≤2^n)
 (hz:2*ray n j+5=81*d)
 (hb:6*2^k+1≤8*d ∧ 8*d≤8*2^k-1)
 (hreset:16*d=8*2^k+q+k+5)
 (hd0:3*d0=2*q+5)
 (he0:2*d0=8*2^(n-4)+h+(n-4)+5)
 (hnot81:(2*q+5)%81≠0)
 (hnot9:(2*h+5)%9≠0):
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
  have hk:k=n-3:=odd_scale_unique (8*d) k (n-3) hb hband
  have heq:16*d=2^n+q+(n-3)+5:=by
    rw[hk,hpp] at hreset
    exact hreset
  have hlinear:81*q+32*deficit n j+81*n+82=47*2^n:=by omega
  obtain ⟨hlo,hhi⟩:=third_parent_interval n (deficit n j) q hn hm hlinear
  have htight:=third_parent_upper_tight n (deficit n j) q hn hm hlinear
  exact third_mid_gap_two_gate_dead n q d0 h hn hlo hhi htight hd0 he0 hnot81 hnot9

#print axioms third_mid_gap_two_gate_dead
#print axioms ray_tthree_two_gate_source_dead
end CascadeTThreeLow
