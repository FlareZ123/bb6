import RayDepthResidue
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000

namespace CascadeQDepthHensel
open CascadeRayDepthHensel CascadeRayDepthResidue CascadeRayPeriod

def qNumerator (n j : Nat) : Int :=
  8*signedZ n j - 9*((2:Int)^(n+2)+2*n+1)

theorem q_mod_three_even_iff (n j : Nat)
    (hn : n%6=4 ∨ n%6=5) :
    qNumerator n j%3=0 ↔ j%2=0 := by
  have hmod : qNumerator n j%3 = (8:Int)*(signedZ n j%3)%3 := by
    simp [qNumerator, Int.sub_emod, Int.mul_emod]
  rw [hmod]
  have h := signedZ_mod_three_even_iff n j hn
  constructor
  · intro hz
    have hz' : signedZ n j%3=0 := by omega
    exact h.mp hz'
  · intro hj
    have hz' : signedZ n j%3=0 := h.mpr hj
    simp [hz']

/-- The Q/U numerator has the same unique ternary depth selector as signedZ,
    but with the lift coefficient multiplied by eight. -/
def qDepthResidue (n : Nat) : Nat → Nat
  | 0 => 0
  | k+1 =>
      let b := qDepthResidue n k
      let a : Int := 8*(2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k
      let q : Int := qNumerator n b/(3:Int)^(k+1)
      b+henselDigit q a*depthPeriod k

theorem depthPeriod_pos (k : Nat) : 0<depthPeriod k := by
  change 0<2*3^k
  exact Nat.mul_pos (by decide) (Nat.pow_pos (by decide))

theorem depthPeriod_next (k : Nat) :
    depthPeriod (k+1)=3*depthPeriod k := by
  simp only [depthPeriod,Nat.pow_succ]
  omega

theorem qCoeff_unit (n b k : Nat)
    (hn : n%6=4 ∨ n%6=5) :
    (8*(2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k)%3 ≠ 0 := by
  let x : Int := (2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k
  have hx : x%3≠0 := by simpa [x] using rayCoeff_unit n b k hn
  have h8 : (8:Int)%3=2 := by decide
  have hmul : ((8:Int)*x)%3=((8:Int)%3*(x%3))%3 := Int.mul_emod _ _ _
  have hxform : 8*(2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k=(8:Int)*x := by
    dsimp [x]
    ac_rfl
  rw [hxform,hmul,h8]
  intro hz
  have hx0 : x%3=0 := by omega
  exact hx hx0

end CascadeQDepthHensel
