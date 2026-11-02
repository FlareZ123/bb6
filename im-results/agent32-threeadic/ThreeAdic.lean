import Lean.Elab.Tactic.Omega
namespace BB6.ThreeAdic

/-- An abstract modulo-three affine section transition.
    Its control update and additive offset depend on the control state and
    current remainder, but not on the quotient. -/
def next (trans : Nat → Nat → Nat × Nat) (c : Nat × Nat) : Nat × Nat :=
  let (s',off) := trans c.2 (c.1 % 3)
  (8*(c.1/3)+off,s')

def iter (trans : Nat → Nat → Nat × Nat) : Nat → Nat × Nat → Nat × Nat
  | 0,c => c
  | j+1,c => iter trans j (next trans c)

private theorem exp_factor (k d : Nat) :
    3^(k+1)*d = 3*(3^k*d) := by
  rw [Nat.pow_succ]
  ac_rfl

private theorem div_factor (n q : Nat) :
    (n+3*q)/3 = n/3+q := by omega
private theorem mod_factor (n q : Nat) :
    (n+3*q)%3 = n%3 := by omega

theorem next_congr (trans : Nat → Nat → Nat × Nat)
    (k n s d : Nat) :
  next trans (n+3^(k+1)*d,s) =
    let z := next trans (n,s)
    (z.1+3^k*(8*d),z.2) := by
  have hf := exp_factor k d
  simp only [hf, next, mod_factor, div_factor]
  have hprod : 8*(3^k*d) = 3^k*(8*d) := by ac_rfl
  simp only [Nat.mul_add]
  rw [hprod]
  congr 1 <;> omega

/-- Exact symbolic k-stage input sensitivity: adding 3^k*d to the counter
    preserves the control state and shifts output counter by 8^k*d. -/
theorem iter_congr (trans : Nat → Nat → Nat × Nat)
    (k n s d : Nat) :
  iter trans k (n+3^k*d,s) =
    let z := iter trans k (n,s)
    (z.1+8^k*d,z.2) := by
  induction k generalizing n s d with
  | zero => simp [iter]
  | succ k ih =>
      change iter trans k (next trans (n+3^(k+1)*d,s)) = _
      rw [next_congr trans k n s d]
      let z := next trans (n,s)
      have h := ih z.1 z.2 (8*d)
      change iter trans k (z.1+3^k*(8*d),z.2) = _
      rw [h]
      simp only [z, iter, Nat.pow_succ, Nat.mul_assoc]

/-- For j stages, any extra k powers of three remain a predictable offset.
    A quantitative finite-prefix 3-adic locality theorem. -/
theorem iter_prefix_congr (trans : Nat → Nat → Nat × Nat)
    (j k n s d : Nat) :
  iter trans j (n+3^(j+k)*d,s) =
    let z := iter trans j (n,s)
    (z.1+3^k*(8^j*d),z.2) := by
  have h := iter_congr trans j n s (3^k*d)
  have h3 : 3^(j+k)*d=3^j*(3^k*d) := by
    rw [Nat.pow_add]; ac_rfl
  rw [h3, h]
  simp only [Nat.mul_left_comm]

#print axioms next_congr
#print axioms iter_congr
#print axioms iter_prefix_congr
end BB6.ThreeAdic
