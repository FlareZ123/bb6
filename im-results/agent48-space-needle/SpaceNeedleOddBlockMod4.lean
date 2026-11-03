import SpaceNeedleOddBlocks
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0

namespace BB6.Agent48.SpaceNeedle

private theorem pow_two_mod_five_period (n : Nat) :
    (2:Nat)^(4*n)%5=1 := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [show 4*(n+1)=4*n+4 by omega, Nat.pow_add, Nat.mul_mod,ih]

/-- An elementary exact characterization of powers of two that equal
one modulo five. -/
theorem power_two_one_mod_five_iff (K : Nat) :
    (2:Nat)^K%5=1 ↔ K%4=0 := by
  let q := K/4
  let r := K%4
  have hq : K=4*q+r := by dsimp [q,r]; omega
  have hr : r<4 := by dsimp [r]; omega
  have hmod : (2:Nat)^K%5=(2:Nat)^r%5 := by
    rw [hq, Nat.pow_add,Nat.mul_mod,pow_two_mod_five_period]
    simp
  rw [hmod]
  constructor
  · intro h
    have hcases : r=0∨r=1∨r=2∨r=3 := by omega
    rcases hcases with h0|h1|h2|h3
    · simpa [r,h0] using h0
    · simp [h1] at h
    · simp [h2] at h
    · simp [h3] at h
  · intro h
    have heq : r=0 := h
    rw [heq]

/-- Immediate arrival at a power-of-two terminal counter after a nonempty
maximal odd run forces terminal exponent divisible by four. -/
theorem odd_block_terminal_exponent_mod_four
    (t m K : Nat) (ht : 0<t) (hm : 0<m)
    (h : 5^t*m-1=2^K-2) : K%4=0 := by
  have h5 : 5 ∣ 5^t := by
    cases t with
    | zero => omega
    | succ t =>
      refine ⟨5^t,?_⟩
      simp [Nat.pow_succ',Nat.mul_comm]
  have h5small : 5 ≤ 5^t := by
    have hh := Nat.pow_le_pow_right (by omega : 0<5) ht
    simpa using hh
  have hmult : 5^t ≤ 5^t*m := by
    have hh := Nat.mul_le_mul_left (5^t) (show 1≤m by omega)
    simpa using hh
  have hp : (2:Nat)^K = 5^t*m+1 := by
    have hlarge : 5 ≤ 5^t*m := Nat.le_trans h5small hmult
    omega
  rcases h5 with ⟨a,ha⟩
  have hmod : (2:Nat)^K%5=1 := by
    rw [hp,ha]
    simp [Nat.add_mod,Nat.mul_mod]
  exact (power_two_one_mod_five_iff K).mp hmod

end BB6.Agent48.SpaceNeedle
#print axioms BB6.Agent48.SpaceNeedle.power_two_one_mod_five_iff
#print axioms BB6.Agent48.SpaceNeedle.odd_block_terminal_exponent_mod_four
