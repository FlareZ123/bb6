import Raw10Box8Cycle

namespace BB6.Agent50Raw10Box8Consumer
open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent49BoxBridge
open BB6.Agent49Box
open BB6.Agent13CrossRouteHeldLeaf109
open BB6.Agent50Raw10Box8
open BB6.Agent47Canonical78

/-- The exact certified set now includes the 65 side witnesses, the original
    held leaf, and the disjoint 625-completion F0=0RC lasso cylinder. -/
def certifiedTables : List PartialMachine :=
  sideTables ++ [held, table]

/-- All complement rectangles are retained after consuming the extra cycle
    cylinder; no rectangle is silently discarded. -/
def raw10RemainderWithCycle : List (Box Slot Transition) :=
  remainder firstOneB0_1LC certifiedTables

theorem raw10RemainderWithCycle_exact (m : Machine) :
    (∃ r ∈ raw10RemainderWithCycle, Fits r m) ↔
    compatible firstOneB0_1LC m ∧
      (∀ w ∈ b0_1lcSideWitnesses, ¬ compatible (unpackTable w.table) m) ∧
      ¬ compatible held m ∧ ¬ compatible table m := by
  rw [raw10RemainderWithCycle, remainder_exact]
  simp only [certifiedTables, List.mem_append, sideTables, List.mem_map,
    List.mem_cons, List.mem_singleton]
  constructor
  · rintro ⟨hp, hn⟩
    refine ⟨hp, ?_, ?_, ?_⟩
    · intro w hw
      exact hn _ (Or.inl ⟨w, hw, rfl⟩)
    · exact hn held (Or.inr (Or.inl rfl))
    · exact hn table (Or.inr (Or.inr rfl))
  · rintro ⟨hp, hs, hh, ht⟩
    refine ⟨hp, ?_⟩
    intro q hq
    rcases hq with hside | htail
    · obtain ⟨w, hw, rfl⟩ := hside
      exact hs w hw
    · rcases htail with rfl | rfl
      · exact hh
      · exact ht

theorem raw10RemainderWithCycle_disjoint :
    raw10RemainderWithCycle.Pairwise Disjoint :=
  remainder_disjoint _ _

/-- The existing score-B consumer now has one additional checked nonhalting
    cylinder. Every residual box remains an explicit open obligation. -/
def raw10CoverWithCycle (B : Nat) (hB : 7014 ≤ B)
    (hHeld : ∀ m, compatible held m → WeightedBound B m)
    (hOpen : ∀ r ∈ raw10RemainderWithCycle,
      ∀ m, Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) firstOneB0_1LC :=
  coverFromRemainder B firstOneB0_1LC certifiedTables
    (fun q hq m hm => by
      rcases List.mem_append.mp hq with hs | htail
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hs
        have hb := b0_1lcSideWitnesses_safe w hw m hm
        intro k d hk hd
        exact Nat.le_trans (hb k d hk hd) hB
      · rcases List.mem_cons.mp htail with hHeldMem | hTableMem
        · have he : q = held := by simpa using hHeldMem
          subst q
          exact hHeld m hm
        · have he : q = table := by simpa using hTableMem
          subst q
          exact (cover B).sound hm)
    hOpen

/-- Conditional exact-BB6 composition with the 625-table cylinder consumed.
    The theorem still requires every remaining rectangle and every other
    canonical residual to be covered at the same weighted score B. -/
theorem exact_from_raw10_remainder_with_cycle (B : Nat) (hB : 7014 ≤ B)
    (hHeld : ∀ m, compatible held m → WeightedBound B m)
    (hOpen : ∀ r ∈ raw10RemainderWithCycle,
      ∀ m, Fits r m → WeightedBound B m)
    (hOther : ∀ e ∈ BB6.Agent47Canonical78.roster,
      e.2 ≠ firstOneB0_1LC → Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B := by
  apply BB6.Agent47Canonical78.exact_at_target B hB _ champ
  intro e he
  by_cases h : e.2 = firstOneB0_1LC
  · rw [h]
    exact raw10CoverWithCycle B hB hHeld hOpen
  · exact hOther e he h

#print axioms raw10RemainderWithCycle_exact
#print axioms raw10RemainderWithCycle_disjoint
#print axioms raw10CoverWithCycle
#print axioms exact_from_raw10_remainder_with_cycle
end BB6.Agent50Raw10Box8Consumer
