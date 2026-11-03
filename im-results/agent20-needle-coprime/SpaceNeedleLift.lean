import SpaceNeedleDensity

namespace SpaceNeedlePrime

def liftQ (A B P c q : Nat) : Nat → Nat
  | 0 => q
  | n+1 => P * liftQ A B P c q n + c * B

theorem affine_power_lift (A B K L q c n : Nat)
    (hseed : 2^K=A*q+B)
    (hperiod : 2^L=1+A*c) :
    2^(K+L*n)=A*(liftQ A B (2^L) c q n)+B := by
  induction n with
  | zero => simpa [liftQ] using hseed
  | succ n ih =>
    have hk : K+L*(n+1)=(K+L*n)+L := by simp [Nat.mul_succ, Nat.add_assoc]
    rw [hk, Nat.pow_add, ih]
    change (A*liftQ A B (2^L) c q n+B)*(2^L) =
      A*((2^L)*liftQ A B (2^L) c q n + c*B)+B
    rw [hperiod]
    simp [Nat.mul_add,Nat.add_mul,Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

def den (v : Nat) := 2^(v+1)+3
def bias (v : Nat) := 3*2^v+v+3

theorem exponent_den_iff (v q k : Nat) :
    2^v*(2*q+3)+v+3*(q+1)=2^k ↔
    2^k=den v*q+bias v := by
  unfold den bias
  rw [Nat.pow_succ']
  constructor <;> intro h
  · have hiden : 2^v*(2*q+3)+v+3*(q+1) = (2*2^v+3)*q+(3*2^v+v+3) := by
      simp [Nat.add_mul,Nat.mul_add,Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    omega
  · have hiden : 2^v*(2*q+3)+v+3*(q+1) = (2*2^v+3)*q+(3*2^v+v+3) := by
      simp [Nat.add_mul,Nat.mul_add,Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    omega

theorem predecessor_period_lift (v q K L c n : Nat)
    (hseed : 2^v*(2*q+3)+v+3*(q+1)=2^K)
    (hperiod : 2^L=1+den v*c) :
    ∃ q', 2^v*(2*q'+3)+v+3*(q'+1)=2^(K+L*n) := by
  let q' := liftQ (den v) (bias v) (2^L) c q n
  refine ⟨q',?_⟩
  apply (exponent_den_iff v q' (K+L*n)).mpr
  exact affine_power_lift (den v) (bias v) K L q c n
      ((exponent_den_iff v q K).mp hseed) hperiod

#print axioms predecessor_period_lift
end SpaceNeedlePrime
