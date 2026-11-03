import Std

namespace SheepValOne

inductive Step : Nat → Nat → Prop where
  | special (a : Nat) : Step (3 * 2^a) (3 * 2^a + a + 3)
  | generic (a u : Nat) (odd : u % 2 = 1) (large : 5 ≤ u) :
      Step (2^a * u) (2^a * u + a + (u-1)/2)

inductive Steps : Nat → Nat → Prop where
  | refl (x : Nat) : Steps x x
  | cons {x y z : Nat} (h : Step x y) (t : Steps y z) : Steps x z

def T (i k v : Nat) : Nat := 2 * (5^i * 4^k * v - 1)

/-- One ordinary Sheep section return, whose successor is already even. -/
theorem one_step (w : Nat) (hw : 2 ≤ w) :
    Step (2*(4*w-1)) (2*(5*w-1)) := by
  have hOdd : (4*w-1)%2=1 := by omega
  have hLarge : 5 ≤ 4*w-1 := by omega
  have h := Step.generic 1 (4*w-1) hOdd hLarge
  have heq : 2*(4*w-1)+1+((4*w-1)-1)/2 = 2*(5*w-1) := by omega
  simpa only [show (2:Nat)^1=2 by decide, heq] using h

/-- A general exact transition of the closed-form coherent family. -/
theorem stage_step (i k v : Nat) (hv : 2 ≤ v) :
    Step (T i (k+1) v) (T (i+1) k v) := by
  have hp5 : 0 < 5^i := Nat.pow_pos (by decide)
  have hp4 : 0 < 4^k := Nat.pow_pos (by decide)
  have hs : 1 ≤ 5^i * 4^k := Nat.mul_pos hp5 hp4
  have hvm := Nat.mul_le_mul_right v hs
  have hw : 2 ≤ 5^i * 4^k * v := Nat.le_trans hv (by simpa using hvm)
  have h := one_step (5^i * 4^k * v) hw
  have hleft : 5^i * 4^(k+1) * v = 4 * (5^i * 4^k * v) := by
    rw [Nat.pow_succ]; ac_rfl
  have hright : 5^(i+1) * 4^k * v = 5 * (5^i * 4^k * v) := by
    rw [Nat.pow_succ]; ac_rfl
  unfold T
  rw [hleft, hright]
  exact h

/-- A full L-step trajectory with explicit endpoint for any large enough seed v. -/
theorem stage_run (i k v : Nat) (hv : 2 ≤ v) :
    Steps (T i k v) (T (i+k) 0 v) := by
  induction k generalizing i with
  | zero =>
      simpa using Steps.refl (T i 0 v)
  | succ k ih =>
      have h := stage_step i k v hv
      have ht := ih (i+1)
      have hz : i + (k+1) = i+1+k := by omega
      rw [hz]
      exact Steps.cons h ht

/-- Every source stage of this family has exact valuation one. -/
theorem stage_source_mod4 (i k v : Nat) (hv : 2 ≤ v) :
    (T i (k+1) v) % 4 = 2 := by
  have hp5 : 0 < 5^i := Nat.pow_pos (by decide)
  have hp4 : 0 < 4^k := Nat.pow_pos (by decide)
  have hs : 1 ≤ 5^i * 4^k := Nat.mul_pos hp5 hp4
  have hw : 1 ≤ 5^i * 4^k * v := by
    have hv1 : 1 ≤ v := by omega
    exact Nat.le_trans hv1 (by simpa using Nat.mul_le_mul_right v hs)
  have hleft : 5^i * 4^(k+1) * v = 4 * (5^i * 4^k * v) := by
    rw [Nat.pow_succ]; ac_rfl
  unfold T
  rw [hleft]
  omega

private theorem five_pow_odd (i : Nat) : 5^i % 2 = 1 := by
  induction i with
  | zero => decide
  | succ i ih =>
      rw [Nat.pow_succ, Nat.mul_mod, ih]

/-- For odd seed v, the last state exits the valuation-one layer. -/
theorem stage_end_mod4 (i v : Nat) (hv : v % 2 = 1) :
    (T i 0 v) % 4 = 0 := by
  have hodd : (5^i * v)%2=1 := by
    rw [Nat.mul_mod, five_pow_odd, hv]
  simp only [T, Nat.pow_zero, Nat.mul_one]
  omega

#print axioms one_step
#print axioms stage_step
#print axioms stage_run
#print axioms stage_source_mod4
#print axioms stage_end_mod4
end SheepValOne
