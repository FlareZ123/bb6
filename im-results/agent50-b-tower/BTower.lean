import BReduction

namespace BB6.Agent50
open BB6.BReduction

/-- A single Machine B parity-drain round multiplies payload-plus-one by at least 3/2. -/
theorem F_payload_factor (p d : Nat) :
    3*(d+1) ≤ 2*((F (p,d)).2+1) := by
  simp only [F]
  omega

/-- A universal geometric lower bound valid for all initial parity/payload pairs. -/
theorem iterF_payload_factor (n p d : Nat) :
    3^n*(d+1) ≤ 2^n*((iterF n (p,d)).2+1) := by
  induction n generalizing p d with
  | zero => simp [iterF]
  | succ n ih =>
    have hf := F_payload_factor p d
    have hfa := Nat.mul_le_mul_left (3^n) hf
    have hi := ih (F (p,d)).1 (F (p,d)).2
    have hpair : ((F (p,d)).1,(F (p,d)).2) = F (p,d) := by
      cases F (p,d) <;> rfl
    rw [hpair] at hi
    have hia := Nat.mul_le_mul_left 2 hi
    calc
      3^(n+1)*(d+1) = 3^n*(3*(d+1)) := by simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm]
      _ ≤ 3^n*(2*((F (p,d)).2+1)) := hfa
      _ = 2*(3^n*((F (p,d)).2+1)) := by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ 2*(2^n*((iterF n (F (p,d))).2+1)) := hia
      _ = 2^(n+1)*((iterF (n+1) (p,d)).2+1) := by
        simp only [iterF, Nat.pow_succ]
        simp [Nat.mul_assoc, Nat.mul_comm]

/-- The hypothetical reset counter grows geometrically in its *previous value*. -/
theorem reset_superexp_step (n : Nat) :
    2*3^(resetA n)+7*2^(resetA n) ≤
      2^(resetA n) * resetA (n+1) := by
  have h := iterF_payload_factor (resetA n) 0 0
  simp only [Nat.zero_add, Nat.mul_one] at h
  have hm := Nat.mul_le_mul_left 2 h
  have hsum := Nat.add_le_add_right hm (7*2^(resetA n))
  calc
    2*3^(resetA n)+7*2^(resetA n)
        ≤ 2*(2^(resetA n)*((iterF (resetA n) (0,0)).2+1))+7*2^(resetA n) := hsum
    _ = 2^(resetA n)*(2*((iterF (resetA n) (0,0)).2+1)+7) := by
      simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]
    _ = 2^(resetA n)*resetA (n+1) := by
      change 2^(resetA n)*(2*((iterF (resetA n) (0,0)).2+1)+7) =
        2^(resetA n)*(2*(iterF (resetA n) (0,0)).2+9)
      congr 1

/-- Elementary inequality used to turn the factor 3/2 into a binary-power bound. -/
theorem pow3_binary (a : Nat) : 2^(a+a/2) ≤ 3^a := by
  have hev (m : Nat) : 2^(3*m) ≤ 3^(2*m) := by
    calc
      2^(3*m) = 8^m := by simp [Nat.pow_mul]
      _ ≤ 9^m := Nat.pow_le_pow_left (by decide) m
      _ = 3^(2*m) := by simp [Nat.pow_mul]
  have hodd (m : Nat) : 2^(3*m+1) ≤ 3^(2*m+1) := by
    calc
      2^(3*m+1) = 2*(2^(3*m)) := by simp [Nat.pow_add, Nat.mul_comm]
      _ ≤ 2*(3^(2*m)) := Nat.mul_le_mul_left 2 (hev m)
      _ ≤ 3*(3^(2*m)) := by omega
      _ = 3^(2*m+1) := by simp [Nat.pow_add, Nat.mul_comm]
  rcases Nat.mod_two_eq_zero_or_one a with he | ho
  · have hn : a = 2*(a/2) := by omega
    have hd : a+a/2 = 3*(a/2) := by omega
    calc
      2^(a+a/2) = 2^(3*(a/2)) := by congr 1 <;> omega
      _ ≤ 3^(2*(a/2)) := hev (a/2)
      _ = 3^a := by congr 1 <;> omega
  · have hn : a = 2*(a/2)+1 := by omega
    have hd : a+a/2 = 3*(a/2)+1 := by omega
    calc
      2^(a+a/2) = 2^(3*(a/2)+1) := by congr 1 <;> omega
      _ ≤ 3^(2*(a/2)+1) := hodd (a/2)
      _ = 3^a := by congr 1 <;> omega

/-- Every hypothetical Machine B reset exceeds a power of its preceding index. -/
theorem reset_binary_tower (n : Nat) :
    2^(resetA n/2+1)+7 ≤ resetA (n+1) := by
  have hc := pow3_binary (resetA n)
  have hm := Nat.mul_le_mul_left 2 hc
  have hsum := Nat.add_le_add_right hm (7*2^(resetA n))
  have hprod :
      2^(resetA n)*(2^(resetA n/2+1)+7) ≤
        2^(resetA n)*resetA (n+1) := by
    calc
      2^(resetA n)*(2^(resetA n/2+1)+7) =
        2*2^(resetA n+resetA n/2)+7*2^(resetA n) := by
          simp [Nat.pow_add, Nat.pow_succ, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ 2*3^(resetA n)+7*2^(resetA n) := hsum
      _ ≤ 2^(resetA n)*resetA (n+1) := reset_superexp_step n
  exact Nat.le_of_mul_le_mul_left hprod (Nat.pow_pos (by decide))

#print axioms F_payload_factor
#print axioms iterF_payload_factor
#print axioms reset_superexp_step
#print axioms pow3_binary
#print axioms reset_binary_tower

end BB6.Agent50
