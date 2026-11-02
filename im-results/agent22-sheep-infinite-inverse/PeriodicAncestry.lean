import InfiniteAncestry
namespace BB6.Agent22.PeriodicAncestry
open BB6.Agent22.InfiniteAncestry

private theorem pow_mul_factor (d q t : Nat) :
    (1+d*t)*(1+d*q) = 1+d*(t+q+d*t*q) := by
  simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one]
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  omega

/-- Exact quotient for powering numbers congruent to one modulo d. -/
def W (d q : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => W d q n + q + d*(W d q n)*q

theorem pow_one_mod (d q n : Nat) :
    (1+d*q)^n = 1+d*W d q n := by
  induction n with
  | zero => simp [W]
  | succ n ih =>
    rw [Nat.pow_succ, ih]
    simpa only [W] using pow_mul_factor d q (W d q n)

theorem W_ge_q (d q n : Nat) : q ≤ W d q (n+1) := by
  simp only [W]
  omega

/-- A power-of-two exponent divisible by 5400 that still admits
an arbitrary 3-adic generic-preimage chain. -/
def exponent (n : Nat) : Nat := (2*3^(n+1))*5400

def quotient (n : Nat) : Nat :=
  W (3^(n+2)) (Q (n+1)) 5400

theorem exponent_divisible_5400 (n : Nat) : 5400 ∣ exponent n := by
  refine ⟨2*3^(n+1), ?_⟩
  unfold exponent
  ac_rfl

theorem quotient_ge_four (n : Nat) : 4 ≤ quotient n := by
  unfold quotient
  have h := W_ge_q (3^(n+2)) (Q (n+1)) 5399
  have he : 5399+1=5400 := by decide
  rw [he] at h
  have hq := Q_step_ge_four n
  omega

theorem exponent_congruence (n : Nat) :
    2^(exponent n) = 1+3^(n+2)*quotient n := by
  have hbase := power_three_lifting (n+1)
  have hp := pow_one_mod (3^(n+2)) (Q (n+1)) 5400
  unfold exponent quotient
  rw [Nat.pow_mul, hbase]
  exact hp
/-- All ancestors for exponents forced into the residue-zero class mod 5400. -/
def ancestorPeriodic (n i : Nat) : Nat :=
  1 + 2^i * 3^((n+2)-i) * quotient n

theorem periodic_ancestor_zero (n : Nat) :
    ancestorPeriodic n 0 = 2^(exponent n) := by
  have hp := exponent_congruence n
  unfold ancestorPeriodic
  have he : n+2-0=n+2 := by omega
  rw [he]
  simp only [Nat.pow_zero, Nat.one_mul]
  exact hp.symm

private theorem ancestorPeriodic_step_relation (n i : Nat) (hi : i+1 ≤ n+2) :
    2*(ancestorPeriodic n i) + 1 = 3*(ancestorPeriodic n (i+1)) := by
  have he : (n+2)-i = ((n+2)-(i+1))+1 := by omega
  have hp3 : 3^((n+2)-i) = 3^((n+2)-(i+1))*3 := by
    rw [he,Nat.pow_succ]
  have hp2 : 2^(i+1) = 2^i*2 := by rw [Nat.pow_succ]
  unfold ancestorPeriodic
  rw [hp3,hp2]
  simp only [Nat.mul_add, Nat.add_mul]
  have hmul :
      2*((2^i*(3^((n+2)-(i+1))*3))*quotient n) =
        3*((2^i*2*3^((n+2)-(i+1)))*quotient n) := by ac_rfl
  omega

private theorem ancestorPeriodic_generic (n i : Nat) :
    5 ≤ ancestorPeriodic n (i+1) ∧ (ancestorPeriodic n (i+1))%2=1 := by
  let v := 2^i * 3^((n+2)-(i+1)) * quotient n
  have hx : ancestorPeriodic n (i+1)=1+2*v := by
    unfold ancestorPeriodic v
    rw [Nat.pow_succ]
    ac_rfl
  have hq : 4 ≤ quotient n := quotient_ge_four n
  have hpos : 0<2^i * 3^((n+2)-(i+1)) :=
    Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))
  have hbig : quotient n ≤ v := by
    exact Nat.le_mul_of_pos_left _ hpos
  rw [hx]
  constructor <;> omega

theorem periodic_ancestor_predecessor (n i : Nat) (hi : i+1 ≤ n+2) :
    SheepBridge.SectionNext (ancestorPeriodic n (i+1)) (ancestorPeriodic n i) := by
  obtain ⟨hge,hodd⟩ := ancestorPeriodic_generic n i
  have heq := ancestorPeriodic_step_relation n i hi
  have htarget : ancestorPeriodic n (i+1)+(ancestorPeriodic n (i+1)-1)/2 =
      ancestorPeriodic n i := by omega
  have hnext := SheepBridge.SectionNext.general 0 (ancestorPeriodic n (i+1)) hge hodd
  simpa [htarget] using hnext

theorem periodic_finite_ancestry (n i : Nat) (hi : i≤n+1) :
    SectionChain i (ancestorPeriodic n i) (ancestorPeriodic n 0) := by
  induction i with
  | zero => exact SectionChain.refl _
  | succ i ih =>
    exact SectionChain.cons (periodic_ancestor_predecessor n i (by omega)) (ih (by omega))

/-- No finite-depth inverse-tree leaf-closure argument can eliminate every
halting power in the exponent class 0 modulo 5400, because that class contains
powers with genuine generic Sheep return-predecessor chains of every depth. -/
theorem class_zero_has_arbitrarily_deep_generic_ancestry (n : Nat) :
    ∃ j t : Nat, 5400 ∣ j ∧ SectionChain n t (2^j) := by
  refine ⟨exponent n, ancestorPeriodic n n, exponent_divisible_5400 n, ?_⟩
  rw [←periodic_ancestor_zero n]
  exact periodic_finite_ancestry n n (by omega)

#print axioms BB6.Agent22.PeriodicAncestry.class_zero_has_arbitrarily_deep_generic_ancestry

end BB6.Agent22.PeriodicAncestry
