import DrainCorrectionGrowth
import FatalFamilyInverseArithmetic

namespace BB6.Agent41FatalInverse
open BB6.Agent49CorrectionGrowth

def E (b : Nat) : Int := excess b

theorem equations : DrainEquations E drift := by
  constructor
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro q hq; unfold E; rw [excess_three q hq]
  · intro q; unfold E; have hh := excess_one q; omega
  · intro q; unfold E; have hh := excess_two q; omega
  · intro q hq
    conv => lhs; rw [drift]
    simp [show 3*q≠0 by omega, show (3*q)%3=0 by omega, show (3*q)/3=q by omega]
  · intro q
    conv => lhs; rw [drift]
    simp [show 3*q+1≠0 by omega, show (3*q+1)%3=1 by omega, show (3*q+1)/3=q by omega]
  · intro q
    conv => lhs; rw [drift]
    simp [show 3*q+2≠0 by omega, show (3*q+2)%3=2 by omega, show (3*q+2)/3=q by omega]

 theorem actual_left (k t : Nat) (ht : t < 3^k) :
    (image (base k-(2*t+1)):Int) + 2 =
      3*(base k:Int)-2*((k:Int)+1)+5 ↔
    (k:Int)+1 = 3*(t:Int)-1-2*(ordinary k t).1-(ordinary k t).2 := by
  simpa [image,E,Int.natCast_add,Int.natCast_mul] using left_image_iff E drift equations k t ht

 theorem actual_right (k t : Nat) (ht : 2*t < 3^k) :
    (image (base k-2*t):Int) + 3 =
      3*(base k:Int)-2*((k:Int)+1)+5 ↔
    3*((k:Int)+1) = 3*(t:Int)+(balanced k t).1+2*(balanced k t).2+1 := by
  simpa [image,E,Int.natCast_add,Int.natCast_mul] using right_image_iff E drift equations k t ht

#print axioms equations
#print axioms actual_left
#print axioms actual_right
end BB6.Agent41FatalInverse
