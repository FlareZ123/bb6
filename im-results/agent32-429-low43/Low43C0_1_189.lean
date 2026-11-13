import Low43Physical
import Low43PhysicalNoFatal
import PhysicalNoFatalConverse
import ParityShiftedRootComplete
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 65536

namespace BB429Low43C0_1_189

open BB6Coverage BB6Bubble
open BB429PhysicalFrontier BB429PhysicalBridge
open BB429OddExcursion BB429JPhysical
open BB429DeltaPhysicalBridge BB429PhysicalNoFatalConverse
open BB429Low43Physical BB429Low43PhysicalNoFatal
open BB429ParityShiftedRootComplete

/-- Exact 7,338-step source continuation for the concrete low43 C/0
    context (v=1,k=189).  The endpoint is J(387,2), with displacement -4
    and maximum rightward excursion +1. -/
theorem root_low43_C0_v1_k189_to_junc387_max :
    runWithMax 7338 (low43_C0_zipper 1 189) =
      some (junc 387 0 2, -4, 1) := by
  decide

/-- The corresponding exact source delta. -/
theorem root_low43_C0_v1_k189_to_junc387_delta :
    runWithDelta 7338 (low43_C0_zipper 1 189) =
      some (junc 387 0 2, -4) := by
  simpa [root_low43_C0_v1_k189_to_junc387_max] using
    ((runWithMax_toDelta 7338 (low43_C0_zipper 1 189)).symm)

private theorem live_A_state (c : Config)
    (hstate : c.state = (⟨0, by decide⟩ : Fin 6)) :
    rawStep target429 c ≠ none := by
  have hA0 : target429 ((⟨0, by decide⟩ : Fin 6), false) =
      some ⟨true, true, ⟨1, by decide⟩⟩ := by decide
  have hA1 : target429 ((⟨0, by decide⟩ : Fin 6), true) =
      some ⟨false, false, ⟨5, by decide⟩⟩ := by decide
  cases hb : c.tape c.head with
  | false =>
      have hread : readSlot c = ((⟨0, by decide⟩ : Fin 6), false) := by
        simp [readSlot, hstate, hb]
      simp [rawStep, hread, hA0]
  | true =>
      have hread : readSlot c = ((⟨0, by decide⟩ : Fin 6), true) := by
        simp [readSlot, hstate, hb]
      simp [rawStep, hread, hA1]

/-- Lift the exact C/0 continuation to every complete physical tape
    representing the low43(v=1,k=189) C/0 zipper. -/
theorem root_low43_C0_v1_k189_physical
    (cC : Config) (hrepC : Represents (low43_C0_zipper 1 189) cC) :
    ∃ c₃₈₇ : Config,
      run target429 7338 cC = some c₃₈₇ ∧
      Represents (junc 387 0 2) c₃₈₇ ∧
      c₃₈₇.head = cC.head - 4 ∧
      (∀ t : Nat, t ≤ 7338 →
        ∃ e : Config, run target429 t cC = some e ∧ ¬ physicalC01 e) := by
  obtain ⟨c₃₈₇, hrun, hrep, hhead⟩ :=
    source_runWithDelta_rep 7338 (low43_C0_zipper 1 189) cC hrepC
      (junc 387 0 2) (-4) root_low43_C0_v1_k189_to_junc387_delta
  have hstateval : c₃₈₇.state.val = 0 := by
    simpa [junc, z] using hrep.1
  have hstate : c₃₈₇.state = (⟨0, by decide⟩ : Fin 6) := by
    exact Fin.ext hstateval
  have hfree : ¬ physicalC01 c₃₈₇ := by
    simp [physicalC01, hstateval]
  have hlive : rawStep target429 c₃₈₇ ≠ none :=
    live_A_state c₃₈₇ hstate
  have hp :=
    physical_run_prefix_c01_free 7338 cC c₃₈₇ hrun hfree hlive
  exact ⟨c₃₈₇, hrun, hrep, hhead, hp⟩

/-- The complete 7,382-step physical gap J(381,3) -> J(387,2):
    44 steps to the C/0 record plus the exact 7,338-step continuation.
    Every primitive prefix excludes C/01. -/
theorem junc381_3_to_junc387_2_physical :
    ∃ c₃₈₇ : Config,
      run target429 7382
        {state := A, head := 0, tape := jTape 381 3} = some c₃₈₇ ∧
      Represents (junc 387 0 2) c₃₈₇ ∧
      c₃₈₇.head = 4 ∧
      (∀ t : Nat, t ≤ 7382 →
        ∃ e : Config,
          run target429 t {state := A, head := 0, tape := jTape 381 3} =
            some e ∧ ¬ physicalC01 e) := by
  obtain ⟨cC, hentry, hheadC, hrepC, hstateC, hcurC, hrightC, hpentry⟩ :=
    low43_C0_record_all_prefix_c01_free 1 189
  obtain ⟨c₃₈₇, hcont, hrep₃₈₇, hhead₃₈₇, hpcont⟩ :=
    root_low43_C0_v1_k189_physical cC hrepC
  have htime : 44+7338=7382 := by norm_num
  have hhead : c₃₈₇.head = 4 := by
    rw [hhead₃₈₇, hheadC]
    norm_num
  have hcombined := physical_prefix_compose
    44 7338 {state := A, head := 0, tape := jTape 381 3}
    cC c₃₈₇ hentry hcont hpentry hpcont
  refine ⟨c₃₈₇, ?_, hrep₃₈₇, hhead, ?_⟩
  · simpa [htime] using hcombined.1
  · simpa [htime] using hcombined.2

#print axioms root_low43_C0_v1_k189_to_junc387_max
#print axioms root_low43_C0_v1_k189_to_junc387_delta
#print axioms root_low43_C0_v1_k189_physical
#print axioms junc381_3_to_junc387_2_physical

end BB429Low43C0_1_189
