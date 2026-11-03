import SpaceNeedleOddBlockMod4
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0

namespace BB6.Agent48.SpaceNeedle

private theorem pow_two_mod_twentyfive_period (n : Nat) :
    (2:Nat)^(20*n)%25=1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [show 20*(n+1)=20*n+20 by omega, Nat.pow_add, Nat.mul_mod, ih]

/-- Exactly the multiples of twenty give 2^K congruent to one modulo25. -/
theorem power_two_one_mod_twentyfive_iff (K : Nat) :
    (2:Nat)^K%25=1 ↔ K%20=0 := by
  let q := K/20
  let r := K%20
  have hq : K=20*q+r := by dsimp [q,r]; omega
  have hr : r<20 := by dsimp [r]; omega
  have hmod : (2:Nat)^K%25=(2:Nat)^r%25 := by
    rw [hq, Nat.pow_add, Nat.mul_mod, pow_two_mod_twentyfive_period]
    simp
  rw [hmod]
  constructor
  · intro h
    have hcases : r=0∨r=1∨r=2∨r=3∨r=4∨r=5∨r=6∨r=7∨r=8∨r=9∨r=10∨r=11∨r=12∨r=13∨r=14∨r=15∨r=16∨r=17∨r=18∨r=19 := by omega
    rcases hcases with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19
    · simpa [r,h0] using h0
    · simp [h1] at h
    · simp [h2] at h
    · simp [h3] at h
    · simp [h4] at h
    · simp [h5] at h
    · simp [h6] at h
    · simp [h7] at h
    · simp [h8] at h
    · simp [h9] at h
    · simp [h10] at h
    · simp [h11] at h
    · simp [h12] at h
    · simp [h13] at h
    · simp [h14] at h
    · simp [h15] at h
    · simp [h16] at h
    · simp [h17] at h
    · simp [h18] at h
    · simp [h19] at h
  · intro h
    have heq : r=0 := h
    rw [heq]

/-- Terminal right after a block of at least two odd calls requires
exponent multiple of twenty, in addition to the modulo-four gate. -/
theorem odd_block_terminal_exponent_mod_twenty
    (t m K : Nat) (ht : 2≤t) (hm : 0<m)
    (h : 5^t*m-1=2^K-2) : K%20=0 := by
  have h25 : 25 ∣ 5^t := by
    cases t with
    | zero => omega
    | succ t =>
      cases t with
      | zero => omega
      | succ u =>
        refine ⟨5^u,?_⟩
        simp only [Nat.pow_succ']
        rw [show (25:Nat)=5*5 by decide]
        ac_rfl
  have hl : 5≤5^t := by
    have hh := Nat.pow_le_pow_right (by omega : 0<5) (show 1≤t by omega)
    simpa using hh
  have hmult : 5^t ≤ 5^t*m := by
    have hh := Nat.mul_le_mul_left (5^t) (show 1≤m by omega)
    simpa using hh
  have hp : (2:Nat)^K = 5^t*m+1 := by
    have hlarge : 5 ≤ 5^t*m := Nat.le_trans hl hmult
    omega
  rcases h25 with ⟨a,ha⟩
  have hmod : (2:Nat)^K%25=1 := by
    rw [hp,ha]
    simp [Nat.add_mod,Nat.mul_mod]
  exact (power_two_one_mod_twentyfive_iff K).mp hmod

end BB6.Agent48.SpaceNeedle
#print axioms BB6.Agent48.SpaceNeedle.power_two_one_mod_twentyfive_iff
#print axioms BB6.Agent48.SpaceNeedle.odd_block_terminal_exponent_mod_twenty
