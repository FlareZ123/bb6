import Lean
set_option maxHeartbeats 0
namespace CascadeTranslatedRayDepth

/-- Linear consequence of the exact high-q margin and source equations. -/
theorem tight_bounds_from_linear (n : Nat) (p A q r : Int)
    (hmargin : 2048*A+14336*n+18432≤16*p)
    (hqlinear : 81*q=752*p-49*n-114-32*A)
    (hA0 : 2*n+3≤A)
    (hrformula : 81*r=32*q+80-162*p-81*n+81) :
    10934*p-961*n+18609≤6561*r ∧
    6561*r≤10942*p-10177*n+6321 := by
  have hA : 128*A+896*n+1152≤p := by omega
  have hqLower : 324*q≥3007*p+700*n+696 := by omega
  have hqUpper : 81*q≤752*p-113*n-210 := by omega
  have hlower : 6561*r≥10934*p-961*n+18609 := by omega
  have hupper : 6561*r≤10942*p-10177*n+6321 := by omega
  exact ⟨hlower,hupper⟩

/-- Tight bounds for the second t=3 parent from the Int-cast source equations. -/
theorem tThreeHighSecondParent_tight_bounds_int (n j : Nat) (p A d q e r : Int)
    (hpow1 : (2:Int)^n=16*p)
    (hpow2 : (2:Int)^(n-3)=2*p)
    (hmargin : 2048*A+14336*n+18432≤16*p)
    (hAdef : (2*n+3)*(2:Int)^j=A)
    (hz : (8:Int)*(2:Int)^n+2*n+3-(2:Int)^(j+1)*(2*n+3)=81*d)
    (hrel : 16*d=(2:Int)^n+q+n+2)
    (hgate : 2*q+5=81*e)
    (hrrel : 16*e+1=(2:Int)^(n-3)+r+n) :
    10934*p-961*n+18609≤6561*r ∧
    6561*r≤10942*p-10177*n+6321 := by
  have hpowJ : (2:Int)^(j+1)=2*(2:Int)^j := by
    rw [Int.pow_succ]
    exact Int.mul_comm _ _
  have hAterm : (2*n+3)*(2:Int)^(j+1)=2*A := by
    calc
      (2*n+3)*(2:Int)^(j+1)=(2*n+3)*(2*(2:Int)^j) := by rw [hpowJ]
      _=2*((2*n+3)*(2:Int)^j) := by ac_rfl
      _=2*A := by rw [hAdef]
  have hz' : (8:Int)*(2:Int)^n+2*n+3-2*A=81*d := by
    rw [Int.mul_comm ((2:Int)^(j+1)) (2*n+3),hAterm] at hz
    exact hz
  have hqlinear : 81*q=752*p-49*n-114-32*A := by omega
  have hrformula : 81*r=32*q+80-162*p-81*n+81 := by omega
  have hpow1j : 1≤2^j := Nat.one_le_pow j 2 (by decide)
  have hA0Nat : 2*n+3≤(2*n+3)*2^j := by
    have h := Nat.mul_le_mul_left (2*n+3) hpow1j
    simpa using h
  have hA0Int : (2:Int)*n+3≤(2*n+3:Int)*(2:Int)^j := by exact_mod_cast hA0Nat
  have hA0 : 2*n+3≤A := by rw [←hAdef]; exact hA0Int
  exact tight_bounds_from_linear n p A q r hmargin hqlinear hA0 hrformula

/-- The first two odd-parent scales of r lie strictly inside dyadic gaps. -/
theorem tThreeHighSecondParent_first_two_odd_scales
    (n : Nat) (p r : Int)
    (hn : 20≤n) (hp : (n:Int)≤p)
    (hlower : 10934*p-961*n+18609≤6561*r)
    (hupper : 6561*r≤10942*p-10177*n+6321) :
    3*6561*p<6561*(2*r+5) ∧
    2*6561*(2*r+5)<9*6561*p ∧
    9*6561*p<4*6561*(2*r+5) ∧
    8*6561*(2*r+5)<27*6561*p := by
  have hnumLower : 21868*p-1922*n+70023≤6561*(2*r+5) := by omega
  have hnumUpper : 6561*(2*r+5)≤21884*p-20354*n+45447 := by omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  · omega

#print axioms tight_bounds_from_linear
#print axioms tThreeHighSecondParent_tight_bounds_int
#print axioms tThreeHighSecondParent_first_two_odd_scales
end CascadeTranslatedRayDepth
