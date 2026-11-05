import ShadowAlgebra
import OddConeMass
import P1InverseLog

namespace BB6.Shadow
open BB6.Agent47P1
open BB6.Agent1Quarter

/-- Exact integer coefficient transport for an authentic P1 odd inverse
    edge from the original OddCone and inverseAt definitions. -/
theorem original_odd_edge_polynomial
    (N L m t b d w z alpha k c r zp b0 d0 : Nat)
    (hcone : OddCone b0 d0 b d m)
    (hrootmass : b0+d0+2*L+3=56*2^N)
    (hoff : L+m=w+z)
    (hcoord : 2^m*(b+4*w)=alpha*2^N)
    (hb : 8≤b) (hb4 : b%4=0) (hd : d%2=1)
    (hi : inverseAt b d t = some (k,c))
    (hcodd : c%2=1)
    (hz : z=2^t*r)
    (hnext : 2*zp+1=L+m+t+r) :
    2*(2: Int)^m*(2: Int)^t*
      (2*(k:Int)-4+4*((L:Int)+m+t+1-zp)) =
    ((alpha:Int)+112*(2:Int)^m*((2:Int)^t-1))*(2:Int)^N := by
  have hconeMass := odd_cone_mass b0 d0 b d m hcone
  have hmassNat : b+d+2*m+2*L+3=56*2^N := by omega
  have hmassI : (b:Int)+(d:Int)+2*(m:Int)=56*(2:Int)^N-2*(L:Int)-3 := by
    have hcast : (b:Int)+(d:Int)+2*(m:Int)+2*(L:Int)+3=56*(2:Int)^N := by
      exact_mod_cast hmassNat
    omega
  have hoffI : (L:Int)+(m:Int)-(z:Int)=(w:Int) := by
    have hc : (L:Int)+(m:Int)=(w:Int)+(z:Int) := by exact_mod_cast hoff
    omega
  have hcoordI : (2:Int)^m*((b:Int)+4*((L:Int)+m-z))=
      (alpha:Int)*(2:Int)^N := by
    rw [hoffI]
    exact_mod_cast hcoord
  have hhalfNat : b=2*(b/2) := by omega
  have hhalfI : (b:Int)=2*((b/2:Nat):Int) := by exact_mod_cast hhalfNat
  have hpower := inverseAt_power b d t k c hi
  have hpowerI : (2:Int)^t*((c:Int)+3)=(d:Int)+((b/2:Nat):Int)+3 := by
    exact_mod_cast hpower.symm
  have hcostNat := inverseAt_odd_cost b d t k c (by omega) hb4 hd hi hcodd
  have hcostI : 2*(k:Int)+(c:Int)+2*(t:Int)+2=(b:Int)+(d:Int) := by
    have heqNat : 2*k+c+2*t+2=b+d := by omega
    exact_mod_cast heqNat
  have hzI : (z:Int)=(2:Int)^t*(r:Int) := by exact_mod_cast hz
  have hnextI : 2*(zp:Int)=(L:Int)+(m:Int)+(t:Int)-1+(r:Int) := by
    have hn : 2*(zp:Int)+1=(L:Int)+(m:Int)+(t:Int)+(r:Int) := by
      exact_mod_cast hnext
    omega
  exact polynomial_step ((2:Int)^m) ((2:Int)^t) ((2:Int)^N)
    (alpha:Int) (b:Int) (d:Int) ((b/2:Nat):Int) (k:Int)
    (c:Int) (L:Int) (m:Int) (t:Int) (z:Int) (r:Int) (zp:Int)
    hmassI hcoordI hhalfI hpowerI hcostI hzI hnextI

#print axioms original_odd_edge_polynomial
end BB6.Shadow
