import BModularSource
import Agent10ModSeven

namespace BB6.Agent30B

private theorem affine_mod7_from_shifted (n z f : Nat)
    (h : (f+8)%7 = (5^n*(z+8))%7) :
    f%7 = (5^n*z+(8*5^n+6))%7 := by
  have hadded : (f+14)%7 = (5^n*(z+8)+6)%7 := by
    calc
      (f+14)%7 = ((f+8)+6)%7 := by omega
      _ = (((f+8)%7)+6)%7 := (Nat.mod_add_mod (f+8) 7 6).symm
      _ = (((5^n*(z+8))%7)+6)%7 := by rw [h]
      _ = (5^n*(z+8)+6)%7 := Nat.mod_add_mod _ 7 6
  have htarget : 5^n*(z+8)+6=5^n*z+(8*5^n+6) := by
    simp [Nat.mul_add, Nat.mul_comm, Nat.add_assoc]
  calc
    f%7 = (f+14)%7 := by omega
    _ = (5^n*(z+8)+6)%7 := hadded
    _ = (5^n*z+(8*5^n+6))%7 := by rw [htarget]

end BB6.Agent30B
