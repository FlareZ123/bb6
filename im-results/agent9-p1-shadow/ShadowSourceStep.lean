import ShadowCast
import ShadowDepthSource
import ShadowParitySource
import ShadowSourceTransport

namespace BB6.Shadow
open BB6.Agent1Quarter
open BB6.Agent47P1

theorem original_odd_shadow_step
    (N L m t b d w z alpha k c b0 d0 : Nat)
    (hcone : OddCone b0 d0 b d m)
    (hrootmass : b0+d0+2*L+3=56*2^N)
    (hL : 8≤L)
    (hoff : L+m=w+z)
    (hw : 4≤w) (hz : 0<z)
    (hcoord : 2^m*(b+4*w)=alpha*2^N)
    (hb : 8≤b) (hb4 : b%4=0) (hd : d%2=1)
    (hi : inverseAt b d t=some (k,c))
    (hcodd : c%2=1) (hk : 2≤k)
    (hchild : (2*k-4)%4=0)
    (hsafe : m+t+3≤N) :
    ∃ (r zp wp alphap : Nat),
      z=2^t*r ∧
      2*zp+1=L+m+t+r ∧
      0<zp ∧ 4≤wp ∧ wp+zp=L+m+t+1 ∧
      alphap=alpha+112*2^m*(2^t-1) ∧
      2^(m+t+1)*((2*k-4)+4*wp)=alphap*2^N := by
  have hmassNat0 := odd_cone_mass b0 d0 b d m hcone
  have hmassNat : b+d+2*m+2*L+3=56*2^N := by omega
  have hmle : m≤N := by omega
  have henc := unscale_coordinate N m b w alpha hmle hcoord
  obtain ⟨r,hr⟩ :=
    source_odd_depth_divides_offset N L m t b d w z alpha k c
      hmassNat hoff henc (by omega) hsafe hi hcodd
  have hparity := source_odd_child_iff_integral
    N L m t b d w z alpha k c r hmassNat hoff henc hb hb4 hd
    hsafe hi hcodd hk hr
  have hodd : (L+m+t+r)%2=1 := by
    have heven := hparity.mp hchild
    omega
  let zp := (L+m+t+r)/2
  have hnext : 2*zp+1=L+m+t+r := by dsimp [zp]; omega
  have hmargin := shadow_step_preserves_offset
    L m z t r zp hL hz (by omega : z+4≤L+m) hr hnext
  let wp := L+m+t+1-zp
  have hwbound : 4≤wp := by dsimp [wp]; omega
  have hwoff : wp+zp=L+m+t+1 := by dsimp [wp]; omega
  let alphap := alpha+112*2^m*(2^t-1)
  have hpoly := original_odd_edge_polynomial
    N L m t b d w z alpha k c r zp b0 d0 hcone hrootmass
    hoff hcoord hb hb4 hd hi hcodd hr hnext
  have hnat := shadow_poly_cast N L m t k zp alpha hk (by omega) hpoly
  refine ⟨r,zp,wp,alphap,hr,hnext,hmargin.1,hwbound,hwoff,rfl,?_⟩
  simpa only [wp, alphap] using hnat

#print axioms original_odd_shadow_step
end BB6.Shadow
