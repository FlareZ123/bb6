import CrossSparse

namespace BB6.CoverageAdapter

private theorem first_halt_before_none (m : BB6Coverage.Machine) :
    ∀ n, BB6Coverage.run m n BB6Coverage.blank = none →
      ∃ k, BB6Coverage.HaltsAfter m k := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    cases n with
    | zero => simp [BB6Coverage.run] at hn
    | succ k =>
      cases hp : BB6Coverage.run m k BB6Coverage.blank with
      | none => exact ih k (Nat.lt_succ_self k) hp
      | some c => exact ⟨k, by constructor; simp [hp]; exact hn⟩

end BB6.CoverageAdapter
