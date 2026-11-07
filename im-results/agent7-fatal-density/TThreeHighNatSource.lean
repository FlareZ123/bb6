import RayNonFork
import TThreeHighNatBridge
set_option maxHeartbeats 0
namespace CascadeTranslatedRayDepth
open CascadeOddRay CascadeFiveForced CascadeRayPeriod

/-- Original-source ray parameter form of the Nat-to-Int dyadic bound. -/
theorem high_source_ray_bounds (n j d q e r : Nat)
    (hn : 20 ≤ n)
    (hm : 2048*deficit n j+16384*n+16384≤2^n)
    (hz : 2*ray n j+5=81*d)
    (hrel : 16*d=2^n+q+(n-3)+5)
    (hgate : 2*q+5=81*e)
    (hrrel : 16*e=8*2^(n-6)+r+(n-6)+5) :
    10934*((2^(n-4):Nat):Int)-961*(n:Int)+18609≤6561*(r:Int) ∧
    6561*(r:Int)≤10942*((2^(n-4):Nat):Int)-10177*(n:Int)+6321 := by
  have hmarginSmall : deficit n j≤2^n := by omega
  have hclosed := CascadeOddRay.deficit_closed n j (by omega)
  have hzSource := CascadeFiveForced.signed_ray_eq_numerator n j (by omega) hmarginSmall
  have hzSigned : signedZ n j=81*(d:Int) := by
    rw [hzSource]
    exact_mod_cast hz
  have hzExpanded : (8:Int)*(2:Int)^n+2*n+3-(2:Int)^(j+1)*(2*n+3)=81*(d:Int) := by
    simp only [signedZ, Int.natCast_add, Int.natCast_mul, Int.natCast_pow] at hzSigned
    change (8:Int)*(2:Int)^n+2*n+3-(2:Int)^(j+1)*(2*n+3)=81*(d:Int) at hzSigned
    exact hzSigned
  exact high_source_nat_bounds n j (deficit n j) d q e r hn hclosed hm hzExpanded hrel hgate hrrel

#print axioms high_source_ray_bounds
end CascadeTranslatedRayDepth
