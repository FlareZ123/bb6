import BParityAperiodic
import BParityCoding

namespace BB6.Agent24.Discrepancy
open BB6.Agent24

/-- The general T iteration and the special Machine B shifted trajectory coincide. -/
theorem path_orbit (N i : Nat) : Coding.path (orbit N) i = orbit (N+i) := by
  induction i with
  | zero => simp [Coding.path]
  | succ i ih =>
    change Coding.T (Coding.path (orbit N) i) = orbit (N+i+1)
    rw [ih]
    rfl

/-- An explicit finite-prefix condition that precludes a parity period k. -/
theorem parity_disagrees_within_gap (N k m : Nat)
    (hk : 0<k)
    (hgap : orbit (N+k)-orbit N < 2^m) :
    ∃ i : Nat, i<m ∧ (orbit (N+i+k))%2 ≠ (orbit (N+i))%2 := by
  have hl := orbit_lt_shift N k hk
  obtain ⟨i,hi,hd⟩ := Coding.finite_prefix_separates (orbit N) (orbit (N+k)) m hl hgap
  refine ⟨i,hi,?_⟩
  rw [path_orbit, path_orbit] at hd
  have he : N+k+i=N+i+k := by omega
  rw [he] at hd
  exact hd.symm

/-- Elementary global upper bound on every shifted Machine B scalar iterate. -/
theorem orbit_upper (n : Nat) : orbit n ≤ 2^(n+3) := by
  induction n with
  | zero => decide
  | succ n ih =>
      have hs := orbit_step n
      have hlo := orbit_lower n
      have hpow : 2^(n+1+3)=2*2^(n+3) := by
        have he : n+1+3=(n+3)+1 := by omega
        rw [he, Nat.pow_succ]
        omega
      rw [hpow]
      omega

/-- Every putative parity period k must fail within N+k+3 further bits
    after an arbitrary starting offset N. -/
theorem parity_disagrees_linear (N k : Nat) (hk : 0<k) :
    ∃ i : Nat, i<N+k+3 ∧ (orbit (N+i+k))%2 ≠ (orbit (N+i))%2 := by
  have hu := orbit_upper (N+k)
  have hlo := orbit_lower N
  have hstrict := orbit_lt_shift N k hk
  have hgap : orbit (N+k)-orbit N < 2^(N+k+3) := by omega
  exact parity_disagrees_within_gap N k (N+k+3) hk hgap

#print axioms parity_disagrees_linear
#print axioms parity_disagrees_within_gap
end BB6.Agent24.Discrepancy
