import Low43RootPhysical
import PhysicalNoFatalConverse
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 65536

namespace BB429Low43RootGap381To387

open BB6Coverage BB6Bubble BB429PhysicalFrontier
open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429FinishScanEDelta BB429W4HeadMax BB429W4HeadPrefix
open BB429Low43Delta BB429Low43Physical BB429Low43Continuation
open BB429PhysicalBridge BB429DeltaPhysicalBridge BB429Low43RootPhysical
open BB429PhysicalNoFatalConverse

/-- The exact 44-step entry from J(381,3) into the v=1,k=189
    low43 C/0 zipper. Both the endpoint displacement and the maximum
    head coordinate are attained at +8. -/
theorem root_low43_381_entry_max :
    runWithMax 44 (junc 381 0 3) =
      some (low43_C0_zipper 1 189, 8, 8) := by
  decide

/-- Exact C/0 continuation for the root-relevant v=1,k=189 instance:
    7,338 steps to J(387,2), net displacement -4, maximum +1. -/
theorem root_low43_C0_1_189_max :
    runWithMax 7338 (low43_C0_zipper 1 189) =
      some (junc 387 0 2, -4, 1) := by
  decide

/-- Compose the entry and continuation monitors. The complete 7,382-step
    source run J(381,3) -> J(387,2) has displacement +4 and maximum +9. -/
theorem root_low43_381_to_387_max :
    runWithMax 7382 (junc 381 0 3) =
      some (junc 387 0 2, 4, 9) := by
  have h1 := root_low43_381_entry_max
  have h2 := root_low43_C0_1_189_max
  have ht : 44 + 7338 = 7382 := by omega
  rw [← ht, runWithMax_add, h1]
  simp [h2, Int.max_def]

theorem root_low43_381_to_387_delta :
    runWithDelta 7382 (junc 381 0 3) =
      some (junc 387 0 2, 4) := by
  simpa [root_low43_381_to_387_max] using
    (runWithMax_toDelta 7382 (junc 381 0 3))

/-- Full-tape physical lift of the concrete J(381,3) -> J(387,2)
    transition. It preserves the exact endpoint representation, proves
    the +4 head displacement, bounds every prefix by +9, and excludes
    the fatal C/01 gateway at every primitive prefix. The safety conclusion
    uses the endpoint-live converse, not a second 7,382-step guard scan. -/
theorem root_low43_381_to_387_physical
    (c : Config) (hrep : Represents (junc 381 0 3) c) :
    ∃ d : Config,
      run target429 7382 c = some d ∧
      Represents (junc 387 0 2) d ∧
      d.head = c.head + 4 ∧
      (∀ t : Nat, t ≤ 7382 →
        ∃ e : Config,
          run target429 t c = some e ∧ e.head ≤ c.head + 9) ∧
      (∀ t : Nat, t ≤ 7382 →
        ∃ e : Config,
          run target429 t c = some e ∧ ¬ physicalC01 e) := by
  let zStart : Zipper := junc 381 0 3
  have hmax :
      runWithMax 7382 zStart =
        some (junc 387 0 2, 4, 9) := by
    simpa [zStart] using root_low43_381_to_387_max
  have hdelta :
      runWithDelta 7382 zStart =
        some (junc 387 0 2, 4) := by
    simpa [hmax] using runWithMax_toDelta 7382 zStart
  obtain ⟨d, hrun, hrepD, hhead⟩ :=
    source_runWithDelta_rep 7382 zStart c hrep
      (junc 387 0 2) 4 hdelta
  have hprefixMax :
      ∀ t : Nat, t ≤ 7382 →
        ∃ e : Config,
          run target429 t c = some e ∧ e.head ≤ c.head + 9 := by
    intro t ht
    obtain ⟨e, he, hh⟩ :=
      physical_source_max_prefix_bound 7382 t zStart c hrep
        (junc 387 0 2, 4, 9) hmax ht
    exact ⟨e, he, by omega⟩
  have hstateVal : d.state.val = 0 := hrepD.1
  have hstate : d.state = (⟨0, by decide⟩ : Fin 6) :=
    Fin.ext hstateVal
  have hfree : ¬ physicalC01 d := by
    simp [physicalC01, hstateVal]
  have hlive : rawStep target429 d ≠ none := by
    cases hbit : d.tape d.head <;>
      simp [rawStep, readSlot, hstate, hbit, target429]
  have hprefixSafe :=
    physical_run_prefix_c01_free 7382 c d hrun hfree hlive
  exact ⟨d, hrun, hrepD, hhead, hprefixMax, hprefixSafe⟩

#print axioms root_low43_381_entry_max
#print axioms root_low43_C0_1_189_max
#print axioms root_low43_381_to_387_max
#print axioms root_low43_381_to_387_delta
#print axioms root_low43_381_to_387_physical

end BB429Low43RootGap381To387
