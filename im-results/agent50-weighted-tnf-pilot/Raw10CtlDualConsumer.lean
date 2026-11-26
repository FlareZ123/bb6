import Raw10BoxCore
import Raw10FixedLeaves
import Raw10CtlFootprint
import Raw10CtlFootprintSecond
import Mathlib.Tactic

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Raw10CtlDualConsumer

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent49Box
open BB6.Agent49BoxBridge
open BB6.Agent13CrossRouteHeldLeaf109

abbrev cycleTable : PartialMachine :=
  BB6.Agent13Raw10FixedLeaves.cycleTable
abbrev haltTable : PartialMachine :=
  BB6.Agent13Raw10FixedLeaves.haltTable

abbrev ctlLeaf2 := BB6.Agent50CtlFootprint.ctlLeaf2
abbrev ctlLeaf3 := BB6.Agent50CtlFootprintSecond.ctlLeaf3

/-- The existing 65 side witnesses, held leaf, cycle and halt cylinders. -/
def certifiedTablesWithCycleAndHalt : List PartialMachine :=
  sideTables ++ [held, cycleTable, haltTable]

/-- The cycle cylinder is nonhalting at every weighted score bound. -/
def cycleCover (B : Nat) : Cover (WeightedBound B) cycleTable :=
  Cover.leaf cycleTable (fun m hm =>
    weighted_of_never B m (BB6.Agent13Raw10FixedLeaves.cycle_never m hm))

/-- The forced-halt cylinder is covered at every B >= 7014. -/
def haltCover (B : Nat) (hB : 7014 ≤ B) :
    Cover (WeightedBound B) haltTable :=
  weighted_halt_leaf haltTable B 2
    BB6.Agent13Raw10FixedLeaves.halt_root
    BB6.Agent13Raw10FixedLeaves.halt_exact
    (by
      intro d hd
      exact Nat.le_trans
        (BB6.Agent13Raw10FixedLeaves.halt_delay_bound d hd)
        (by omega))

/-- The four-pair CTL footprint is a nonhalting weighted leaf at every bound. -/
def ctlLeaf2Certificate (B : Nat) : WeightedTNFCertificate B ctlLeaf2 6 :=
  .nonhalt
    (by decide)
    (by decide)
    (by decide)
    (by
      intro m hm
      exact BB6.Agent50CtlFootprint.ctlLeaf2_neverHalts m hm)

/-- The five-pair CTL footprint is a nonhalting weighted leaf at every bound. -/
def ctlLeaf3Certificate (B : Nat) : WeightedTNFCertificate B ctlLeaf3 6 :=
  .nonhalt
    (by decide)
    (by decide)
    (by decide)
    (by
      intro m hm
      exact BB6.Agent50CtlFootprintSecond.ctlLeaf3_neverHalts m hm)

/-- Subtract the five-pair CTL cylinder first, then the four-pair cylinder.
    This order matches the exact first-mismatch crosswalk. -/
def certifiedTablesWithBothCtl : List PartialMachine :=
  certifiedTablesWithCycleAndHalt ++ [ctlLeaf3, ctlLeaf2]

/-- Exact retained complement after both source-pinned CTL footprints. -/
def raw10RemainderWithBothCtl : List (Box Slot Transition) :=
  remainder firstOneB0_1LC certifiedTablesWithBothCtl

theorem raw10RemainderWithBothCtl_exact (m : Machine) :
    (∃ r ∈ raw10RemainderWithBothCtl, Fits r m) ↔
    compatible firstOneB0_1LC m ∧
      (∀ w ∈ b0_1lcSideWitnesses,
        ¬ compatible (unpackTable w.table) m) ∧
      ¬ compatible held m ∧
      ¬ compatible cycleTable m ∧
      ¬ compatible haltTable m ∧
      ¬ compatible ctlLeaf2 m ∧
      ¬ compatible ctlLeaf3 m := by
  rw [raw10RemainderWithBothCtl, remainder_exact]
  simp only [certifiedTablesWithBothCtl, List.mem_append,
    certifiedTablesWithCycleAndHalt, sideTables, List.mem_map,
    List.mem_cons, List.mem_singleton]
  constructor
  · rintro ⟨hp, hn⟩
    refine ⟨hp, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro w hw
      exact hn _ (Or.inl ⟨w, hw, rfl⟩)
    · exact hn held (Or.inr (Or.inl rfl))
    · exact hn cycleTable (Or.inr (Or.inr (Or.inl rfl)))
    · exact hn haltTable (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact hn ctlLeaf2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    · exact hn ctlLeaf3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · rintro ⟨hp, hs, hh, hcycle, hhalt, hctl2, hctl3⟩
    refine ⟨hp, ?_⟩
    intro q hq
    rcases hq with hside | htail
    · obtain ⟨w, hw, rfl⟩ := hside
      exact hs w hw
    · rcases htail with hHeldMem | htail
      · have he : q = held := by simpa using hHeldMem
        subst q
        exact hh
      · rcases htail with hCycleMem | htail
        · have he : q = cycleTable := by simpa using hCycleMem
          subst q
          exact hcycle
        · rcases htail with hHaltMem | htail
          · have he : q = haltTable := by simpa using hHaltMem
            subst q
            exact hhalt
          · rcases htail with hCtl3Mem | hCtl2Mem
            · have he : q = ctlLeaf3 := by simpa using hCtl3Mem
              subst q
              exact hctl3
            · have he : q = ctlLeaf2 := by simpa using hCtl2Mem
              subst q
              exact hctl2

theorem raw10RemainderWithBothCtl_disjoint :
    raw10RemainderWithBothCtl.Pairwise Disjoint :=
  remainder_disjoint _ _

theorem raw10RemainderWithBothCtl_count :
    raw10RemainderWithBothCtl.length = 51 := by
  decide

private def allSlots : List Slot :=
  (List.finRange 6).flatMap fun q => [(q, false), (q, true)]

private def boxMass (b : Box Slot Transition) : Nat :=
  (allSlots.map fun s => (b s).length).prod

/-- The two source cylinders conflict at C1: one fixes 1LE, the other 1RC. -/
theorem ctlLeaves_disjoint (m : Machine) :
    ¬ (compatible ctlLeaf2 m ∧ compatible ctlLeaf3 m) := by
  rintro ⟨h2, h3⟩
  have hleaf2 :
      ctlLeaf2 (2, true) =
        some (BB6.Agent50CtlFootprint.candidate2 (2, true)) := by
    decide
  have hleaf3 :
      ctlLeaf3 (2, true) =
        some (BB6.Agent50CtlFootprintSecond.candidate3 (2, true)) := by
    decide
  have h2move := h2 (2, true)
    (BB6.Agent50CtlFootprint.candidate2 (2, true)) hleaf2
  have h3move := h3 (2, true)
    (BB6.Agent50CtlFootprintSecond.candidate3 (2, true)) hleaf3
  have hneq :
      BB6.Agent50CtlFootprint.candidate2 (2, true) ≠
        BB6.Agent50CtlFootprintSecond.candidate3 (2, true) := by
    decide
  exact hneq (h2move.symm.trans h3move)

theorem ctlLeaves_assignedCount :
    (allSlots.filter fun s =>
      (ctlLeaf2 s).isSome || (ctlLeaf3 s).isSome).length = 6 := by
  decide

theorem raw10RemainderWithBothCtl_mass :
    (raw10RemainderWithBothCtl.map boxMass).sum =
      90_578_812_307_475 := by
  decide

/-- Conditional score-B cover for the Raw10 parent after consuming both CTL
    cylinders. All 51 retained boxes and the held-leaf obligation stay explicit. -/
def raw10CoverWithBothCtl (B : Nat) (hB : 7014 ≤ B)
    (hHeld : ∀ m, compatible held m → WeightedBound B m)
    (hOpen : ∀ r ∈ raw10RemainderWithBothCtl,
      ∀ m, Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) firstOneB0_1LC :=
  coverFromRemainder B firstOneB0_1LC certifiedTablesWithBothCtl
    (fun q hq m hm => by
      rcases List.mem_append.mp hq with hbase | hctl
      · rcases List.mem_append.mp hbase with hs | htail
        · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hs
          have hb := b0_1lcSideWitnesses_safe w hw m hm
          intro k d hk hd
          exact Nat.le_trans (hb k d hk hd) hB
        · rcases List.mem_cons.mp htail with hHeldMem | htail
          · have he : q = held := by simpa using hHeldMem
            subst q
            exact hHeld m hm
          · rcases List.mem_cons.mp htail with hCycleMem | htail
            · have he : q = cycleTable := by simpa using hCycleMem
              subst q
              exact (cycleCover B).sound hm
            · rcases List.mem_singleton.mp htail with hHaltMem
              have he : q = haltTable := by simpa using hHaltMem
              subst q
              exact (haltCover B hB).sound hm
      · rcases List.mem_cons.mp hctl with hCtl3Mem | htail
        · have he : q = ctlLeaf3 := by simpa using hCtl3Mem
          subst q
          exact (ctlLeaf3Certificate B).sound hm
        · have he : q = ctlLeaf2 := by simpa using htail
          subst q
          exact (ctlLeaf2Certificate B).sound hm)
    hOpen

#print axioms cycleCover
#print axioms haltCover
#print axioms ctlLeaf2Certificate
#print axioms ctlLeaf3Certificate
#print axioms raw10RemainderWithBothCtl_exact
#print axioms raw10RemainderWithBothCtl_disjoint
#print axioms raw10RemainderWithBothCtl_count
#print axioms ctlLeaves_disjoint
#print axioms ctlLeaves_assignedCount
#print axioms raw10RemainderWithBothCtl_mass
#print axioms raw10CoverWithBothCtl

end BB6.Agent50Raw10CtlDualConsumer
