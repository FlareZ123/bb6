import Lean

/-!
A small, standalone arithmetic lemma for the branch-10 affine family in the
BB(6) six-state investigation.

ExactV2Pair k A B encodes v₂(A)=k and v₂(B)=k+1 without introducing a
partial valuation function: both odd cofactors are explicit witnesses.
The inverse coefficient maps F and S/E lower k by one. At k=0, splitting
q into even/odd halves doubles both coefficients and resets k to one.
-/

def IsOddNat (n : Nat) : Prop := ∃ t, n = 2 * t + 1

def ExactV2Pair (k A B : Nat) : Prop :=
  ∃ u v, IsOddNat u ∧ IsOddNat v ∧ A = 2 ^ k * u ∧ B = 2 ^ (k + 1) * v

theorem isOdd_add_two_mul {u v : Nat} (hu : IsOddNat u) : IsOddNat (u + 2 * v) := by
  rcases hu with ⟨t, ht⟩
  refine ⟨t + v, ?_⟩
  omega

theorem isOdd_two_mul_add {u v : Nat} (hv : IsOddNat v) : IsOddNat (2 * u + v) := by
  rcases hv with ⟨t, ht⟩
  refine ⟨u + t, ?_⟩
  omega

theorem pow_succ_div_two (k u : Nat) : (2 ^ (k + 1) * u) / 2 = 2 ^ k * u := by
  have hp : 2 ^ (k + 1) = 2 ^ k * 2 := by simp [Nat.pow_succ]
  have hn : 2 ^ (k + 1) * u = 2 * (2 ^ k * u) := by
    simp [hp, Nat.mul_comm, Nat.mul_left_comm]
  rw [hn]
  exact Nat.mul_div_cancel_left (2 ^ k * u) (by decide)

theorem pow_succ2_div_four (k u : Nat) : (2 ^ (k + 2) * u) / 4 = 2 ^ k * u := by
  have hp : 2 ^ (k + 2) = 2 ^ k * 4 := by simp [Nat.pow_succ, Nat.mul_assoc]
  have hn : 2 ^ (k + 2) * u = 4 * (2 ^ k * u) := by
    simp [hp, Nat.mul_assoc, Nat.mul_comm]
  rw [hn]
  exact Nat.mul_div_cancel_left (2 ^ k * u) (by decide)

/-- F: (A,B)=(2^(k+1)u,2^(k+2)v) maps to (A/2,B+A) at level k. -/
theorem exactV2_F (k u v : Nat) (hu : IsOddNat u) :
    ExactV2Pair k ((2 ^ (k + 1) * u) / 2) (2 ^ (k + 2) * v + 2 ^ (k + 1) * u) := by
  refine ⟨u, u + 2 * v, hu, isOdd_add_two_mul hu, ?_, ?_⟩
  · exact pow_succ_div_two k u
  · calc
      2 ^ (k + 2) * v + 2 ^ (k + 1) * u
          = (2 ^ (k + 1) * 2) * v + 2 ^ (k + 1) * u := by rw [Nat.pow_succ]
      _ = 2 ^ (k + 1) * (2 * v) + 2 ^ (k + 1) * u := by rw [Nat.mul_assoc]
      _ = 2 ^ (k + 1) * (2 * v + u) := by rw [Nat.mul_add]
      _ = 2 ^ (k + 1) * (u + 2 * v) := by rw [Nat.add_comm (2 * v) u]

/-- S/E: (A,B)=(2^(k+1)u,2^(k+2)v) maps to (A+B/4,B/2) at level k. -/
theorem exactV2_SE (k u v : Nat) (hv : IsOddNat v) :
    ExactV2Pair k (2 ^ (k + 1) * u + (2 ^ (k + 2) * v) / 4) ((2 ^ (k + 2) * v) / 2) := by
  refine ⟨2 * u + v, v, isOdd_two_mul_add hv, hv, ?_, ?_⟩
  · calc
      2 ^ (k + 1) * u + (2 ^ (k + 2) * v) / 4
          = 2 ^ (k + 1) * u + 2 ^ k * v := by rw [pow_succ2_div_four]
      _ = (2 ^ k * 2) * u + 2 ^ k * v := by rw [Nat.pow_succ]
      _ = 2 ^ k * (2 * u) + 2 ^ k * v := by rw [Nat.mul_assoc]
      _ = 2 ^ k * (2 * u + v) := by rw [Nat.mul_add]
  · exact pow_succ_div_two (k + 1) v

/-- Exact parameter reindexing when q is even. -/
theorem affine_split_even (A a B b q : Nat) (hq : q % 2 = 0) :
    A * q + a = (2 * A) * (q / 2) + a ∧
    B * q + b = (2 * B) * (q / 2) + b := by
  have hq' : q = 2 * (q / 2) := by
    have h := Nat.mod_add_div q 2
    omega
  constructor
  · calc
      A * q + a = A * (2 * (q / 2)) + a := by
        have hA : A * q = A * (2 * (q / 2)) := congrArg (fun z => A * z) hq'
        rw [hA]
      _ = (2 * A) * (q / 2) + a := by simp [Nat.mul_comm, Nat.mul_left_comm]
  · calc
      B * q + b = B * (2 * (q / 2)) + b := by
        have hB : B * q = B * (2 * (q / 2)) := congrArg (fun z => B * z) hq'
        rw [hB]
      _ = (2 * B) * (q / 2) + b := by simp [Nat.mul_comm, Nat.mul_left_comm]

/-- Exact parameter reindexing when q is odd. -/
theorem affine_split_odd (A a B b q : Nat) (hq : q % 2 = 1) :
    A * q + a = (2 * A) * (q / 2) + (A + a) ∧
    B * q + b = (2 * B) * (q / 2) + (B + b) := by
  have hq' : q = 2 * (q / 2) + 1 := by
    have h := Nat.mod_add_div q 2
    omega
  constructor
  · calc
      A * q + a = A * (2 * (q / 2) + 1) + a := by
        have hA : A * q = A * (2 * (q / 2) + 1) := congrArg (fun z => A * z) hq'
        rw [hA]
      _ = A * (2 * (q / 2)) + A + a := by simp [Nat.mul_add]
      _ = (2 * A) * (q / 2) + (A + a) := by simp [Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · calc
      B * q + b = B * (2 * (q / 2) + 1) + b := by
        have hB : B * q = B * (2 * (q / 2) + 1) := congrArg (fun z => B * z) hq'
        rw [hB]
      _ = B * (2 * (q / 2)) + B + b := by simp [Nat.mul_add]
      _ = (2 * B) * (q / 2) + (B + b) := by simp [Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem odd_pow2_succ (n : Nat) : IsOddNat (2 ^ (n + 1) + 1) := by
  refine ⟨2 ^ n, ?_⟩
  calc
    2 ^ (n + 1) + 1 = 2 ^ n * 2 + 1 := by rw [Nat.pow_succ]
    _ = 2 * 2 ^ n + 1 := by rw [Nat.mul_comm]

theorem odd_pow2_sub_one (n : Nat) : IsOddNat (2 ^ (n + 1) - 1) := by
  refine ⟨2 ^ n - 1, ?_⟩
  have hp : 2 ^ (n + 1) = 2 ^ n * 2 := by rw [Nat.pow_succ]
  have hle : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
  omega

/-- The initial branch-10 coefficients have exact 2-adic orders 5 and 6. -/
theorem initial_affine_coefficients (n : Nat) :
    ExactV2Pair 5 (64 * 2 ^ n + 32) (64 * (2 ^ (n + 1) - 1)) := by
  refine ⟨2 ^ (n + 1) + 1, 2 ^ (n + 1) - 1,
    odd_pow2_succ n, odd_pow2_sub_one n, ?_, ?_⟩
  · have hp : 2 ^ (n + 1) = 2 ^ n * 2 := by rw [Nat.pow_succ]
    have h32 : 2 ^ 5 = 32 := by decide
    rw [h32, hp]
    omega
  · have h64 : 2 ^ 6 = 64 := by decide
    rw [h64]

/-- A positive natural parameter strictly decreases under q -> floor(q/2). -/
theorem half_lt_self (q : Nat) (hq : 0 < q) : q / 2 < q := by
  omega

/-- Doubling both coefficients at the parity split resets the exact orders to 1 and 2. -/
theorem split_child_exactV2 (u v : Nat) (hu : IsOddNat u) (hv : IsOddNat v) :
    ExactV2Pair 1 (2 * u) (4 * v) := by
  refine ⟨u, v, hu, hv, ?_, ?_⟩
  · have h : 2 ^ 1 = 2 := by decide
    rw [h]
  · have h : 2 ^ 2 = 4 := by decide
    rw [h]
