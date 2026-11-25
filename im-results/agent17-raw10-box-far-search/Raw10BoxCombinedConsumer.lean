import Raw10Box8CycleConsumer
import Raw10Box0Halt

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent17Raw10CombinedConsumer

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent49Box
open BB6.Agent49BoxBridge
open BB6.Agent13CrossRouteHeldLeaf109
open BB6.Agent50Raw10Box8
open BB6.Agent50Raw10Box8Consumer
open BB6.Agent50Raw10Box0Halt
open BB6.Agent47Canonical78

/-- Add the independent 25^8 two-step halt cylinder after the 65 side
    witnesses, the held leaf, and the 625-completion cycle cylinder. -/
def certifiedTablesWithCycleAndHalt : List PartialMachine :=
  sideTables ++ [held, table, haltTable]

/-- Exact residual after all currently proposed raw10 cylinders are consumed.
    Every remaining rectangle is deliberately retained. -/
def raw10RemainderWithCycleAndHalt : List (Box Slot Transition) :=
  remainder firstOneB0_1LC certifiedTablesWithCycleAndHalt

theorem raw10RemainderWithCycleAndHalt_exact (m : Machine) :
    (∃ r ∈ raw10RemainderWithCycleAndHalt, Fits r m) ↔
    compatible firstOneB0_1LC m ∧
      (∀ w ∈ b0_1lcSideWitnesses,
        ¬ compatible (unpackTable w.table) m) ∧
      ¬ compatible held m ∧
      ¬ compatible table m ∧
      ¬ compatible haltTable m := by
  rw [raw10RemainderWithCycleAndHalt, remainder_exact]
  simp only [certifiedTablesWithCycleAndHalt, List.mem_append, sideTables,
    List.mem_map, List.mem_cons, List.mem_singleton]
  constructor
  · rintro ⟨hp, hn⟩
    refine ⟨hp, ?_, ?_, ?_, ?_⟩
    · intro w hw
      exact hn _ (Or.inl ⟨w, hw, rfl⟩)
    · exact hn held (Or.inr (Or.inl rfl))
    · exact hn table (Or.inr (Or.inr (Or.inl rfl)))
    · exact hn haltTable (Or.inr (Or.inr (Or.inr rfl)))
  · rintro ⟨hp, hs, hh, hc, hhalt⟩
    refine ⟨hp, ?_⟩
    intro q hq
    rcases hq with hside | htail
    · obtain ⟨w, hw, rfl⟩ := hside
      exact hs w hw
    · rcases htail with rfl | rfl | rfl
      · exact hh
      · exact hc
      · exact hhalt

theorem raw10RemainderWithCycleAndHalt_disjoint :
    raw10RemainderWithCycleAndHalt.Pairwise Disjoint :=
  remainder_disjoint _ _

/-- Conditional score-B consumer with both Agent50 cylinders included.
    The halt leaf is lifted monotonically from score 7014 to B. -/
def raw10CoverWithCycleAndHalt (B : Nat) (hB : 7014 ≤ B)
    (hHeld : ∀ m, compatible held m → WeightedBound B m)
    (hOpen : ∀ r ∈ raw10RemainderWithCycleAndHalt,
      ∀ m, Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) firstOneB0_1LC :=
  coverFromRemainder B firstOneB0_1LC certifiedTablesWithCycleAndHalt
    (fun q hq m hm => by
      rcases List.mem_append.mp hq with hs | htail
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hs
        have hb := b0_1lcSideWitnesses_safe w hw m hm
        intro k d hk hd
        exact Nat.le_trans (hb k d hk hd) hB
      · rcases List.mem_cons.mp htail with hHeldMem | htail
        · have he : q = held := by simpa using hHeldMem
          subst q
          exact hHeld m hm
        · rcases List.mem_cons.mp htail with hCycleMem | htail
          · have he : q = table := by simpa using hCycleMem
            subst q
            exact (BB6.Agent50Raw10Box8.cover B).sound hm
          · rcases List.mem_singleton.mp htail with hHaltMem
            have he : q = haltTable := by simpa using hHaltMem
            subst q
            have h7014 := BB6.Agent50Raw10Box0Halt.cover.sound hm
            intro k d hk hd
            exact Nat.le_trans (h7014 k d hk hd) hB)
    hOpen

/-- The final exact-BB6 composition remains conditional on all 41 explicit
    residual rectangles and every other canonical roster entry. -/
theorem exact_from_raw10_remainder_with_cycle_and_halt (B : Nat)
    (hB : 7014 ≤ B)
    (hHeld : ∀ m, compatible held m → WeightedBound B m)
    (hOpen : ∀ r ∈ raw10RemainderWithCycleAndHalt,
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
    exact raw10CoverWithCycleAndHalt B hB hHeld hOpen
  · exact hOther e he h

#print axioms raw10RemainderWithCycleAndHalt_exact
#print axioms raw10RemainderWithCycleAndHalt_disjoint
#print axioms raw10CoverWithCycleAndHalt
#print axioms exact_from_raw10_remainder_with_cycle_and_halt

end BB6.Agent17Raw10CombinedConsumer
