import Low43RootPhysical
import NoFatalGuard
import W4HeadMax
import W4HeadPrefix
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 65536

namespace BB429Low43RootNext

open BB6Coverage BB6Bubble
open BB429OddExcursion BB429FinishScanEDelta
open BB429W4HeadMax BB429W4HeadPrefix
open BB429Low43Physical BB429Low43RootPhysical
open BB429PhysicalBridge BB429DeltaPhysicalBridge
open BB429NoFatalGuard

/-- The root-relevant low-43 entry J(119,35) reaches its exact C/0
    frontier after 1484 original-table moves. -/
theorem root_low43_119_entry_max :
    runWithMax 1484 (junc 119 0 35) =
      some (low43_C0_zipper 17 50, 40, 40) := by
  decide

/-- The entry itself is guarded: its terminal C/0 has a blank right
    neighbour, and no earlier C/0/1 occurs. -/
theorem root_low43_119_entry_no_fatal :
    runNoFatal 1484 (junc 119 0 35) =
      some (low43_C0_zipper 17 50) := by
  decide

/-- From the exact v=17,k=50 low-43 C/0 frontier, the original source
    returns to J(109,66) in 2120 steps. The full prefix maximum is +1. -/
theorem root_low43_119_continuation_max :
    runWithMax 2120 (low43_C0_zipper 17 50) =
      some (junc 109 0 66, -68, 1) := by
  decide

/-- The complete continuation is C/0/1-free, including its initial
    harmless C/0 checkpoint. -/
theorem root_low43_119_continuation_no_fatal :
    runNoFatal 2120 (low43_C0_zipper 17 50) =
      some (junc 109 0 66) := by
  decide

/-- Compose the exact entry and continuation. The prepared J(119,35)
    state reaches J(109,66) in 3604 steps, with displacement -28 and
    maximum rightward displacement +41. -/
theorem root_low43_119_to_109_max :
    runWithMax 3604 (junc 119 0 35) =
      some (junc 109 0 66, -28, 41) := by
  have h1 : runWithMax 1484 (junc 119 0 35) =
      some (low43_C0_zipper 17 50, 40, 40) :=
    root_low43_119_entry_max
  have h2 : runWithMax 2120 (low43_C0_zipper 17 50) =
      some (junc 109 0 66, -68, 1) :=
    root_low43_119_continuation_max
  have ht : 1484 + 2120 = 3604 := by omega
  rw [← ht, runWithMax_add, h1]
  simp [h2, Int.max_def]

/-- The complete prepared J(119,35) branch has an exact no-fatal
    certificate, not merely a head-displacement simulation. -/
theorem root_low43_119_to_109_no_fatal :
    runNoFatal 3604 (junc 119 0 35) =
      some (junc 109 0 66) := by
  have h1 := root_low43_119_entry_no_fatal
  have h2 := root_low43_119_continuation_no_fatal
  simpa [show 1484 + 2120 = 3604 by omega] using
    runNoFatal_compose 1484 2120 (junc 119 0 35)
      (low43_C0_zipper 17 50) (junc 109 0 66) h1 h2

/-- Every primitive source prefix in the complete prepared branch is
    nonfatal in the exact C/0/1 sense. -/
theorem root_low43_119_to_109_prefix_no_fatal (t : Nat)
    (ht : t ≤ 3604) :
    ∃ p, run t (junc 119 0 35) = some p ∧ fatalCZero p = false :=
  runNoFatal_prefix 3604 t (junc 119 0 35) (junc 109 0 66)
    root_low43_119_to_109_no_fatal ht

/-- Lift the prepared return and its complete prefix maximum to every
    physical tape represented by the J(119,35) zipper. -/
theorem root_low43_119_to_109_physical
    (c : Config) (hrep : Represents (junc 119 0 35) c) :
    ∃ d : Config,
      run target429 3604 c = some d ∧
      Represents (junc 109 0 66) d ∧
      d.head = c.head - 28 ∧
      (∀ t : Nat, t ≤ 3604 →
        ∃ e : Config,
          run target429 t c = some e ∧
          e.head ≤ c.head + 41) := by
  let zStart : Zipper := junc 119 0 35
  have hmax :
      runWithMax 3604 zStart =
        some (junc 109 0 66, -28, 41) := by
    simpa [zStart] using root_low43_119_to_109_max
  have hdelta :
      runWithDelta 3604 zStart = some (junc 109 0 66, -28) := by
    simpa [hmax] using runWithMax_toDelta 3604 zStart
  obtain ⟨d,hrun,hrepD,hhead⟩ :=
    source_runWithDelta_rep 3604 zStart c hrep
      (junc 109 0 66) (-28) hdelta
  have hprefix :
      ∀ t : Nat, t ≤ 3604 →
        ∃ e : Config,
          run target429 t c = some e ∧
          e.head ≤ c.head + 41 := by
    intro t ht
    obtain ⟨e,he,hh⟩ :=
      physical_source_max_prefix_bound 3604 t zStart c hrep
        (junc 109 0 66, -28, 41) hmax ht
    exact ⟨e,he,by omega⟩
  exact ⟨d,hrun,hrepD,by simpa using hhead,hprefix⟩

/-- The next prepared low-even r=4k instance is the exact
    J(109,66) -> J(11,282) return (N=33,k=38). Both C/0 visits
    in this 6027-step source segment have blank right neighbours. -/
theorem root_loweven4k_109_to_11_max :
    runWithMax 6027 (junc 109 0 66) =
      some (junc 11 0 282, -209, 76) := by
  decide

theorem root_loweven4k_109_to_11_no_fatal :
    runNoFatal 6027 (junc 109 0 66) =
      some (junc 11 0 282) := by
  decide

/-- Compose low43 and low-even 4k: J(119,35) -> J(11,282) in
    9631 steps, with displacement -237 and maximum +48. -/
theorem root_low43_119_to_11_max :
    runWithMax 9631 (junc 119 0 35) =
      some (junc 11 0 282, -237, 48) := by
  have h1 := root_low43_119_to_109_max
  have h2 := root_loweven4k_109_to_11_max
  have ht : 3604 + 6027 = 9631 := by omega
  rw [← ht, runWithMax_add, h1]
  simp [h2, Int.max_def]

theorem root_low43_119_to_11_no_fatal :
    runNoFatal 9631 (junc 119 0 35) =
      some (junc 11 0 282) := by
  have h1 := root_low43_119_to_109_no_fatal
  have h2 := root_loweven4k_109_to_11_no_fatal
  have ht : 3604 + 6027 = 9631 := by omega
  simpa [ht] using
    runNoFatal_compose 3604 6027 (junc 119 0 35)
      (junc 109 0 66) (junc 11 0 282) h1 h2

theorem root_low43_119_to_11_prefix_no_fatal (t : Nat)
    (ht : t ≤ 9631) :
    ∃ p, run t (junc 119 0 35) = some p ∧ fatalCZero p = false :=
  runNoFatal_prefix 9631 t (junc 119 0 35) (junc 11 0 282)
    root_low43_119_to_11_no_fatal ht

/-- Physical lift of the composed 9631-step prepared branch, including
    its all-prefix head maximum. -/
theorem root_low43_119_to_11_physical
    (c : Config) (hrep : Represents (junc 119 0 35) c) :
    ∃ d : Config,
      run target429 9631 c = some d ∧
      Represents (junc 11 0 282) d ∧
      d.head = c.head - 237 ∧
      (∀ t : Nat, t ≤ 9631 →
        ∃ e : Config,
          run target429 t c = some e ∧
          e.head ≤ c.head + 48) := by
  let zStart : Zipper := junc 119 0 35
  have hmax :
      runWithMax 9631 zStart =
        some (junc 11 0 282, -237, 48) := by
    simpa [zStart] using root_low43_119_to_11_max
  have hdelta :
      runWithDelta 9631 zStart = some (junc 11 0 282, -237) := by
    simpa [hmax] using runWithMax_toDelta 9631 zStart
  obtain ⟨d,hrun,hrepD,hhead⟩ :=
    source_runWithDelta_rep 9631 zStart c hrep
      (junc 11 0 282) (-237) hdelta
  have hprefix :
      ∀ t : Nat, t ≤ 9631 →
        ∃ e : Config,
          run target429 t c = some e ∧
          e.head ≤ c.head + 48 := by
    intro t ht
    obtain ⟨e,he,hh⟩ :=
      physical_source_max_prefix_bound 9631 t zStart c hrep
        (junc 11 0 282, -237, 48) hmax ht
    exact ⟨e,he,by omega⟩
  exact ⟨d,hrun,hrepD,by simpa using hhead,hprefix⟩

#print axioms root_low43_119_entry_max
#print axioms root_low43_119_entry_no_fatal
#print axioms root_low43_119_continuation_max
#print axioms root_low43_119_continuation_no_fatal
#print axioms root_low43_119_to_109_max
#print axioms root_low43_119_to_109_no_fatal
#print axioms root_low43_119_to_109_prefix_no_fatal
#print axioms root_low43_119_to_109_physical
#print axioms root_low43_119_to_11_max
#print axioms root_low43_119_to_11_no_fatal
#print axioms root_low43_119_to_11_prefix_no_fatal
#print axioms root_low43_119_to_11_physical
#print axioms root_loweven4k_109_to_11_max
#print axioms root_loweven4k_109_to_11_no_fatal

end BB429Low43RootNext
