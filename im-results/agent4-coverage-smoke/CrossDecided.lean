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

/-- Import any actual Agent13 source-certified subtree directly into the
    original Agent8 DecidedBelow-B complete-search proof-object vocabulary. -/
theorem import_source_tree_as_decided_cover (B : Nat)
    (p : BB6.Coverage.PartialMachine) (tree : BB6.Coverage.CoverTree B p) :
    BB6Coverage.Cover (BB6Coverage.DecidedBelow B) (sparseTo8 p) := by
  apply BB6Coverage.Cover.leaf
  intro m hm
  have hc := (import_source_tree_as_cover_leaf B p tree).sound m hm
  exact bounded_to_decided B m hc

#print axioms import_source_tree_as_decided_cover
end BB6.CoverageAdapter
