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

private theorem never_or_first_halt (m : BB6Coverage.Machine) :
    BB6Coverage.NeverHalts m ∨ ∃ n, BB6Coverage.HaltsAfter m n := by
  classical
  by_cases hex : ∃ n, BB6Coverage.run m n BB6Coverage.blank = none
  · obtain ⟨n, hn⟩ := hex
    exact Or.inr (first_halt_before_none m n hn)
  · left
    intro n
    cases h : BB6Coverage.run m n BB6Coverage.blank with
    | none => exact False.elim (hex ⟨n, h⟩)
    | some c => rfl

private theorem bounded_to_decided (B : Nat) (m : BB6Coverage.Machine)
    (h : BoundedRuntime B m) : BB6Coverage.DecidedBelow B m := by
  rcases never_or_first_halt m with hn | ⟨n,hh⟩
  · exact Or.inl hn
  · exact Or.inr ⟨n, h n hh, hh⟩

end BB6.CoverageAdapter
