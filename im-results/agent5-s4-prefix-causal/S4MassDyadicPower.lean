import S4MassCompletion
import Lean.Elab.Tactic.Omega

namespace S4Mass

/-- A power of two is always available inside the dyadic interval
[n, 2n) for positive n. -/
theorem dyadic_bracket (n : Nat) (hn : 1 ≤ n) :
    ∃ e : Nat, n ≤ 2 ^ e ∧ 2 ^ e < 2 * n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hone : n = 1
    · subst n
      exact ⟨0, by decide, by decide⟩
    · let q := n / 2
      have hqpos : 1 ≤ q := by dsimp [q]; omega
      have hqlt : q < n := by dsimp [q]; omega
      obtain ⟨e, hlo, hhi⟩ := ih q hqlt hqpos
      by_cases heven : n % 2 = 0
      · refine ⟨e + 1, ?_, ?_⟩
        · rw [Nat.pow_succ]; dsimp [q] at hlo hhi; omega
        · rw [Nat.pow_succ]; dsimp [q] at hlo hhi; omega
      · by_cases hstrict : q < 2 ^ e
        · refine ⟨e + 1, ?_, ?_⟩
          · rw [Nat.pow_succ]; dsimp [q] at hlo hhi hstrict; omega
          · rw [Nat.pow_succ]; dsimp [q] at hlo hhi hstrict; omega
        · refine ⟨e + 2, ?_, ?_⟩
          · rw [show e + 2 = (e + 1) + 1 by omega, Nat.pow_succ, Nat.pow_succ]
            dsimp [q] at hlo hhi hstrict; omega
          · rw [show e + 2 = (e + 1) + 1 by omega, Nat.pow_succ, Nat.pow_succ]
            dsimp [q] at hlo hhi hstrict; omega

/-- Every sufficiently large exact suffix mass allows a binary-power
stopping weight with at most three suffix digits, for any fixed offset k. -/
theorem exact_mass_power2_completion (m k : Nat)
    (hm : 10 ≤ m) (hk : k ≤ m) :
    ∃ e : Nat, ∃ xs : List Nat,
      mass xs = m ∧ W xs + k = 2 ^ e ∧ xs.length ≤ 3 := by
  obtain ⟨e, hlo, hhi⟩ := dyadic_bracket (m + k) (by omega)
  obtain ⟨xs, hmass, hweight, hlen⟩ :=
    realize_power_target m k (2 ^ e) hm hk hlo hhi
  exact ⟨e, xs, hmass, hweight, hlen⟩

#print axioms dyadic_bracket
#print axioms exact_mass_power2_completion

end S4Mass
