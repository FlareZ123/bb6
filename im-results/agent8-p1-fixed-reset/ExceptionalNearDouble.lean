import Lean
namespace BB6.Agent8Exceptional
theorem exceptional_near_double_of_exponential
    (n m : Nat) (hm : n+4 ≤ m)
    (he : 6*2^n ≤ (n+m+3)*2^(m+1-n)) :
    2^(2*n-m) ≤ n+1 := by
  by_cases hbig : 2*n ≤ m
  · have hz : 2*n-m=0 := by omega
    simp [hz]
  · have hmb : m < 2*n := by omega
    let r : Nat := m-n
    let q : Nat := 2*n-m
    have hsum : r+q=n := by dsimp [r,q]; omega
    have hpow : (2:Nat)^n=2^r*2^q := by rw [← hsum, Nat.pow_add]
    have hnext : m+1-n=r+1 := by dsimp [r]; omega
    have hpow_next : (2:Nat)^(m+1-n)=2^r*2 := by rw [hnext, Nat.pow_succ]
    have hcoeff : n+m+3 ≤ 3*(n+1) := by omega
    have hrpos : 0 < 6*(2:Nat)^r :=
      Nat.mul_pos (by decide) (Nat.pow_pos (by decide))
    have hle : (6*2^r)*2^q ≤ (6*2^r)*(n+1) := by
      calc
        (6*2^r)*2^q = 6*2^n := by rw [hpow]; simp only [Nat.mul_assoc]
        _ ≤ (n+m+3)*2^(m+1-n) := he
        _ = (n+m+3)*(2^r*2) := by rw [hpow_next]
        _ ≤ 3*(n+1)*(2^r*2) := Nat.mul_le_mul_right _ hcoeff
        _ = (6*2^r)*(n+1) := by
          calc
            3*(n+1)*(2^r*2) = ((3*2)*2^r)*(n+1) := by ac_rfl
            _ = (6*2^r)*(n+1) := rfl
    exact Nat.le_of_mul_le_mul_left hle hrpos
theorem exceptional_near_double_log
    (n m : Nat) (hm : n+4 ≤ m)
    (he : 6*2^n ≤ (n+m+3)*2^(m+1-n)) :
    2*n ≤ m + Nat.log2 (n+1) := by
  have hpow := exceptional_near_double_of_exponential n m hm he
  have hlog : 2*n-m ≤ Nat.log2 (n+1) :=
    (Nat.le_log2 (by omega)).2 hpow
  omega
#print axioms BB6.Agent8Exceptional.exceptional_near_double_of_exponential
#print axioms BB6.Agent8Exceptional.exceptional_near_double_log
end BB6.Agent8Exceptional
