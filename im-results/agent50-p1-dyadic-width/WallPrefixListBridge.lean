import Lean
/-!
# Exact characteristic-prefix bridge for the P1 telescoping wall identity

This is the arithmetic interface between Agent43's source list invariant and
Agent50's Boolean carry certificates. `costWeightedSum` and `bitExpr` are
definitionally equal to the corresponding source and carry expressions.
No bound on the witness list or on the prefix depth is assumed.
-/
namespace BB6WallBridge

def sumBits (n j : Nat) : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then n + 3 + j else 0) + 2 * sumBits n (j + 1) bs

def bits (A : List Nat) (j : Nat) : Nat → List Bool
  | 0 => []
  | k+1 => (A.contains j) :: bits A (j+1) k

def weight (n s : Nat) := (n+3+s)*2^s

def prefSum (n j : Nat) (A : List Nat) : Nat → Nat
  | 0 => 0
  | k+1 => (if j ∈ A then weight n j else 0) + prefSum n (j+1) A k

theorem bits_length (A : List Nat) (j k : Nat) : (bits A j k).length = k := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih => simp [bits, ih]

theorem prefix_bits (n j k : Nat) (A : List Nat) :
    prefSum n j A k = 2^j * sumBits n j (bits A j k) := by
  induction k generalizing j with
  | zero => simp [prefSum, bits, sumBits]
  | succ k ih =>
    rw [prefSum, bits, sumBits, ih, Nat.mul_add, Nat.pow_succ]
    by_cases h : j ∈ A <;> simp [h, weight, Nat.mul_assoc, Nat.mul_comm]

theorem prefSum_cons (n j k a : Nat) (A : List Nat) (ha : a ∉ A) :
    prefSum n j (a::A) k = prefSum n j A k +
      (if j ≤ a ∧ a < j+k then weight n a else 0) := by
  induction k generalizing j with
  | zero =>
    have hh : ¬(j ≤ a ∧ a < j+0) := by omega
    rw [if_neg hh]
    simp [prefSum]
  | succ k ih =>
    rw [prefSum, prefSum, ih (j+1)]
    by_cases h : j = a
    · subst j
      have hn : ¬ a + 1 ≤ a := by omega
      simp [ha, hn, Nat.add_comm]
    · have he : (j ≤ a ∧ a < j+(k+1)) ↔ (j+1 ≤ a ∧ a < j+1+k) := by omega
      simp [List.mem_cons, h, he, Nat.add_assoc]

def costWeightedSum (n : Nat) : List Nat → Nat
  | [] => 0
  | s::A => weight n s + costWeightedSum n A

theorem pow_dvd (K s : Nat) (h : K ≤ s) : 2^K ∣ 2^s := by
  refine ⟨2^(s-K), ?_⟩
  rw [← Nat.pow_add, Nat.add_sub_of_le h]

theorem weight_mod_zero (n K s : Nat) (h : K ≤ s) : weight n s % 2^K = 0 := by
  obtain ⟨q,hq⟩ := pow_dvd K s h
  apply Nat.mod_eq_zero_of_dvd
  refine ⟨(n+3+s)*q, ?_⟩
  simp only [weight, hq]
  ac_rfl

theorem prefSum_nil (n j k : Nat) : prefSum n j [] k = 0 := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih => simp [prefSum, ih]

theorem weighted_mod_prefix (n K : Nat) (A : List Nat) (hnd : A.Nodup) :
    costWeightedSum n A % 2^K = prefSum n 0 A K % 2^K := by
  induction A with
  | nil => simp [costWeightedSum, prefSum_nil]
  | cons a A ih =>
    obtain ⟨ha, hn⟩ := List.nodup_cons.mp hnd
    rw [costWeightedSum, prefSum_cons n 0 K a A ha, Nat.add_mod, ih hn]
    by_cases h : a < K
    · simp [h, Nat.add_comm, Nat.add_mod]
    · have hz := weight_mod_zero n K a (by omega)
      simp [h, hz]

def bitExpr (n : Nat) (rest : List Bool) : Nat := (n+3)+2*sumBits n 1 rest

theorem weighted_mod_bits (n k : Nat) (A : List Nat) (hnd : A.Nodup) (h0 : 0 ∈ A) :
    ∃ rest : List Bool, rest.length = k ∧
      costWeightedSum n A % 2^(k+1) = bitExpr n rest % 2^(k+1) := by
  refine ⟨bits A 1 k, bits_length A 1 k, ?_⟩
  rw [weighted_mod_prefix n (k+1) A hnd, prefSum, if_pos h0, prefix_bits]
  simp [weight, bitExpr]

theorem wall_identity_implies_bits (n m k S : Nat) (A : List Nat)
    (hnd : A.Nodup) (h0 : 0 ∈ A) (hn : k+1 ≤ n) (hm : k+1 ≤ m)
    (h : 1+7*2^n*S = 2^n*2^m+costWeightedSum n A+(n+3+m)*2^m) :
    ∃ rest : List Bool, rest.length = k ∧ bitExpr n rest % 2^(k+1) = 1 := by
  have hN := Nat.mod_eq_zero_of_dvd (pow_dvd (k+1) n hn)
  have hM := Nat.mod_eq_zero_of_dvd (pow_dvd (k+1) m hm)
  have hpos : 1 < 2^(k+1) := by rw [Nat.pow_succ]; have := Nat.two_pow_pos k; omega
  have hmod := congrArg (fun x : Nat => x % 2^(k+1)) h
  have hL : (1+7*2^n*S)%2^(k+1) = 1 := by
    simp [Nat.add_mod, Nat.mul_mod, hN, Nat.mod_eq_of_lt hpos]
  have hR : (2^n*2^m+costWeightedSum n A+(n+3+m)*2^m)%2^(k+1) = costWeightedSum n A%2^(k+1) := by
    simp [Nat.add_mod, Nat.mul_mod, hN, hM]
  rw [hL, hR] at hmod
  obtain ⟨rest, hlen, heq⟩ := weighted_mod_bits n k A hnd h0
  exact ⟨rest, hlen, heq.symm.trans hmod.symm⟩

/-- Any certified impossible Boolean prefix excludes a wall list satisfying
    the exact telescoping identity. -/
theorem wall_identity_impossible (n m k S : Nat) (A : List Nat)
    (hnd : A.Nodup) (h0 : 0 ∈ A) (hn : k+1 ≤ n) (hm : k+1 ≤ m)
    (hno : ¬ ∃ rest : List Bool, rest.length = k ∧ bitExpr n rest % 2^(k+1) = 1) :
    1+7*2^n*S ≠ 2^n*2^m+costWeightedSum n A+(n+3+m)*2^m := by
  intro h
  exact hno (wall_identity_implies_bits n m k S A hnd h0 hn hm h)

#print axioms prefix_bits
#print axioms prefSum_cons
#print axioms weighted_mod_prefix
#print axioms weighted_mod_bits
#print axioms pow_dvd
#print axioms weight_mod_zero
#print axioms wall_identity_implies_bits
#print axioms wall_identity_impossible
end BB6WallBridge
