import Lean
set_option maxHeartbeats 0
namespace CascadeRayPeriod

/-- Signed continuation of the exact C-reset numerator at canonical
    even-ray depth j, n the fatal index. For valid nonnegative ray heights,
    signedZ n j is exactly 2*ray n j+5. -/
def signedZ (n j : Nat) : Int :=
  (8*(2^n:Nat)+2*n+3:Nat) - (2^(j+1)*(2*n+3):Nat)

private theorem pow_six (j:Nat): (2^(j+6):Nat)=64*2^j:=by
  rw [Nat.pow_add]
  have hb:(2:Nat)^6=64:=by decide
  rw [hb]
  omega

/-- The signed inverse numerator is genuinely period six modulo nine,
    uniformly in the fatal index and the ray depth, with no finite cutoff. -/
theorem signed_ray_six_period (n j:Nat):
    signedZ n (j+6)%9=signedZ n j%9:=by
  have hp:(2^((j+6)+1):Nat)=64*2^(j+1):=by
    have he:j+6+1=j+1+6:=by omega
    rw [he]
    exact pow_six (j+1)
  have hpi: ((2:Int)^((j+6)+1))=64*(2:Int)^(j+1):=by
    exact_mod_cast hp
  dsimp [signedZ]
  rw [hpi]
  simp only [Int.mul_assoc]
  omega

#print axioms signed_ray_six_period
end CascadeRayPeriod
