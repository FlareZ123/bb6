import CanonicalTwoParentGraft

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent3Raw120Canonical76Graft
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent8TNFPath
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent47CanonicalTwoParent

/-- Exact raw120 table, independent of the expensive sibling proof closures. -/
abbrev parent : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨true,false,4⟩)

noncomputable def roster75 := graftRoster parent [] roster76

theorem parent_present :
    ∃ e ∈ roster76, sameTable e.2 parent = true := by decide

theorem roster75_count : roster75.length = 75 := by decide

theorem raw120_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide

/-- Stable conditional consumer of the accepted raw107/raw114 roster.
    The parent theorem is explicit so this layer can compile independently
    of the fourteen nontrivial raw120 children and their generated objects. -/
theorem roster75_sound
    (h76 : ∀ m, compatible root m → WeightedBound 7014 m ∨
      ∃ e ∈ roster76, TNFQuotientCompatible e.2 m)
    (h120 : ∀ m, compatible parent m → WeightedBound 224707 m) :
    ∀ m, compatible root m → WeightedBound 224707 m ∨
      ∃ e ∈ roster75, TNFQuotientCompatible e.2 m := by
  have hwide : ∀ m, compatible root m → WeightedBound 224707 m ∨
      ∃ e ∈ roster76, TNFQuotientCompatible e.2 m := by
    intro m hm
    rcases h76 m hm with h | h
    · left
      intro k d hk hd
      exact Nat.le_trans (h k d hk hd) (by decide)
    · exact Or.inr h
  exact graftRoster_sound raw120_root hwide
    (fun m hm => Or.inl (h120 m hm))

theorem exact_at_target (B : Nat) (hB : 224707 ≤ B)
    (h76 : ∀ m, compatible root m → WeightedBound 7014 m ∨
      ∃ e ∈ roster76, TNFQuotientCompatible e.2 m)
    (h120 : ∀ m, compatible parent m → WeightedBound 224707 m)
    (hLeaves : ∀ e ∈ roster75, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB
    (roster75_sound h76 h120) hLeaves champ

#print axioms parent_present
#print axioms roster75_count
#print axioms roster75_sound
#print axioms exact_at_target
end BB6.Agent3Raw120Canonical76Graft
