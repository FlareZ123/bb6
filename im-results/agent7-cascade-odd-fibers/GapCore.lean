import Std

namespace GapCore

/-- An odd coefficient cannot lie within less than one power of two below an even one. -/
theorem no_near_miss (n p s u k : Nat) (hs : n < s)
    (heven : u%2=0) (hodd : k%2=1)
    (hscale : 2*p=u*s) (hup : k*s ≤ 2*p+n) :
    k*s+s ≤ 2*p := by
  have hklt : k<u := by
    by_cases h : k<u
    · exact h
    · have hu : u≤k := by omega
      have hu_lt : u<k := by omega
      have hle : u+1≤k := by omega
      have hmul := Nat.mul_le_mul_right s hle
      have hx : (u+1)*s=u*s+s := by simp [Nat.add_mul]
      omega
  have hk : k+1≤u := by omega
  have hmul := Nat.mul_le_mul_right s hk
  have hx : (k+1)*s=k*s+s := by simp [Nat.add_mul]
  omega

/-- Next doubled inverse is above the largest smaller-scale image upper endpoint. -/
theorem terminal_lower_gap (n p s u k : Nat) (hs:n<s)
    (heven:u%2=0) (hodd:k%2=1) (hscale:2*p=u*s)
    (hup:k*s≤2*p+n) :
    4*p-3 < 8*p+n-1-k*(2*s) := by
  have hgap := no_near_miss n p s u k hs heven hodd hscale hup
  have htwice : k*(2*s)=2*(k*s) := by
    simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  omega

#print axioms no_near_miss
#print axioms terminal_lower_gap

end GapCore
