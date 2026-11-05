import Lean
namespace BB6.Shadow

/-- Convert an exact integer shadow transport identity into natural
    coordinate transport when each subtraction remains nonnegative. -/
theorem shadow_poly_cast
 (N L m t k zp alpha : Nat)
 (hk : 2≤k)
 (hz : zp≤L+m+t+1)
 (hpoly :
    2*(2: Int)^m*(2: Int)^t*
      (2*(k:Int)-4+4*((L:Int)+m+t+1-zp)) =
    ((alpha:Int)+112*(2:Int)^m*((2:Int)^t-1))*(2:Int)^N) :
  2^(m+t+1)*((2*k-4)+4*(L+m+t+1-zp)) =
    (alpha+112*2^m*(2^t-1))*2^N := by
  have hbI : (((2*k-4):Nat):Int)=2*(k:Int)-4 := by omega
  have hwI : (((L+m+t+1-zp):Nat):Int)=(L:Int)+m+t+1-zp := by omega
  have htpos : 1≤2^t := Nat.one_le_pow _ _ (by decide)
  have hpowcast : ((2^t:Nat):Int)=(2:Int)^t := by norm_cast
  have htI : (((2^t-1):Nat):Int)=(2:Int)^t-1 := by omega
  have hpowI : (2:Int)^(m+t+1)=2*(2:Int)^m*(2:Int)^t := by
    simp [Int.pow_add, Int.pow_succ, Int.mul_assoc, Int.mul_comm]
  have hcast :
      (((2^(m+t+1)*((2*k-4)+4*(L+m+t+1-zp))):Nat):Int) =
      (((alpha+112*2^m*(2^t-1))*2^N:Nat):Int) := by
    push_cast
    rw [hbI, hwI, htI, hpowI]
    exact hpoly
  exact_mod_cast hcast

/-- A scaled coefficient witness becomes an ordinary dyadic encoding. -/
theorem unscale_coordinate
    (N m b w alpha : Nat)
    (hm : m≤N)
    (h : 2^m*(b+4*w)=alpha*2^N) :
    b+4*w=alpha*2^(N-m) := by
  have hpow : 2^N=2^m*2^(N-m) := by
    have he : m+(N-m)=N := by omega
    calc
      2^N = 2^(m+(N-m)) := by rw [he]
      _ = 2^m*2^(N-m) := by rw [Nat.pow_add]
  have hs : 2^m*(b+4*w)=2^m*(alpha*2^(N-m)) := by
    calc
      2^m*(b+4*w) = alpha*2^N := h
      _ = 2^m*(alpha*2^(N-m)) := by rw [hpow]; simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  exact Nat.mul_left_cancel (Nat.two_pow_pos m) hs

#print axioms shadow_poly_cast
#print axioms unscale_coordinate
end BB6.Shadow
