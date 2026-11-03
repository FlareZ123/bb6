import GBase

namespace BB6.Agent10IterBarrier

theorem F_midpoint (k z : Nat) :
  F (k+1) z + F (k+1) (z+2^(k+1))+7 = 2*F (k+1) (z+2^k) ∨
  F (k+1) z + F (k+1) (z+2^(k+1)) = 2*F (k+1) (z+2^k)+7 := by
  have h1 : F k (z+2^k) = F k z+3^k := by
    simpa using F_shift k z 1
  have h2 : F k (z+2^(k+1)) = F k z+2*3^k := by
    have he : z+2^(k+1)=z+2^k*2 := by
      simp [Nat.pow_succ, Nat.mul_comm]
    rw [he, F_shift k z 2]
    omega
  have ht : (3^k)%2=1 := by
    simp [Nat.pow_mod]
  simpa [F, h1, h2] using G_midpoint (F k z) (3^k) ht

#print axioms F_midpoint
end BB6.Agent10IterBarrier
