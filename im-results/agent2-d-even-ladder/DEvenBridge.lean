import Lean.Elab.Tactic.Omega

namespace BB6.DPeriodicEvenBridge

/-- A uniformly bounded multiplier for the even-depth source-section bridge. -/
def multiplier : Nat → Nat
  | 0 => 315
  | r + 1 => 57 * multiplier r % 512

theorem multiplier_lt (r : Nat) : multiplier r < 512 := by
  cases r with
  | zero => decide
  | succ r =>
    change 57 * multiplier r % 512 < 512
    exact Nat.mod_lt _ (by decide)

theorem multiplier_odd (r : Nat) : multiplier r % 2 = 1 := by
  induction r with
  | zero => decide
  | succ r ih =>
    change (57 * multiplier r % 512) % 2 = 1
    omega

theorem multiplier_pos (r : Nat) : 0 < multiplier r := by
  have h := multiplier_odd r
  omega

private theorem power_shift (r : Nat) :
    3 ^ (2 * (r + 1) + 1) = 9 * 3 ^ (2 * r + 1) := by
  have heq : 2 * (r + 1) + 1 = (2 * r + 1) + 2 := by omega
  rw [heq, Nat.pow_add]
  have h3 : 3 ^ 2 = 9 := by decide
  rw [h3]
  omega

/-- An exact all-depth modular residue, with no bounded search. -/
theorem multiplier_residue (r : Nat) :
    (3 ^ (2 * r + 1) * multiplier r) % 512 = 433 := by
  induction r with
  | zero => decide
  | succ r ih =>
    rw [power_shift]
    change (9 * 3 ^ (2 * r + 1) * (57 * multiplier r % 512)) % 512 = 433
    rw [Nat.mul_mod_mod]
    have hrearrange : 9 * 3 ^ (2 * r + 1) * (57 * multiplier r) =
        (9 * 57) * (3 ^ (2 * r + 1) * multiplier r) := by ac_rfl
    rw [hrearrange, Nat.mul_mod]
    have hconstant : 9 * 57 % 512 = 1 := by decide
    rw [hconstant]
    simpa using ih

/-- Three source-macro endpoints from X(9v+7,3r+3) have exactly the
    unary size and packet required for 2r consecutive E-triple returns. -/
theorem even_bridge_parameters (r : Nat) :
    ∃ (v U : Nat), 0 < U ∧ U < 512 ∧
      512 * v + 434 = 3 ^ (2 * r + 1) * U + 1 ∧
      2 * (3 * r + 3) = 3 * (2 * r) + 6 := by
  let U := multiplier r
  let X := 3 ^ (2 * r + 1) * U
  refine ⟨X / 512, U, multiplier_pos r, multiplier_lt r, ?_, by omega⟩
  have hres : X % 512 = 433 := multiplier_residue r
  have hdiv := Nat.mod_add_div X 512
  omega

/-- Multipliers evolve through an ordinary modular power. -/
theorem multiplier_add (r s : Nat) :
    multiplier (r + s) = 57 ^ s * multiplier r % 512 := by
  induction s with
  | zero =>
    simp [Nat.mod_eq_of_lt (multiplier_lt r)]
  | succ s ih =>
    rw [Nat.add_succ]
    change 57 * multiplier (r+s) % 512 = _
    rw [ih, Nat.mul_mod_mod]
    have hp : 57 ^ (s+1) = 57 * 57^s := by
      rw [Nat.pow_succ]
      ac_rfl
    rw [hp]
    ac_rfl

/-- The multiplier has period 64, independently of the depth. -/
theorem multiplier_period64 (r : Nat) : multiplier (r+64) = multiplier r := by
  rw [multiplier_add, Nat.mul_mod]
  have hp : 57 ^ 64 % 512 = 1 := by decide
  rw [hp]
  simp [Nat.mod_eq_of_lt (multiplier_lt r)]

/-- The multiplier does not return to its initial value at any earlier
    positive index; hence 64 is its exact least positive period. -/
theorem multiplier_first_repeat_64 (p : Nat) (hp : 0 < p) (hsmall : p < 64) :
    multiplier p ≠ multiplier 0 := by
  have ht : ∀ j : Fin 64, 0 < j.val → multiplier j.val ≠ multiplier 0 := by decide
  exact ht ⟨p, hsmall⟩ hp

#print axioms even_bridge_parameters
#print axioms multiplier_period64
#print axioms multiplier_first_repeat_64
end BB6.DPeriodicEvenBridge
