import Low42Physical
import PhysicalNoFatalConverse

set_option maxHeartbeats 30000000
set_option maxRecDepth 65536

namespace BB429Low42PhysicalNoFatal

open BB6Coverage BB6Bubble
open BB429PhysicalFrontier BB429PhysicalBridge
open BB429OddExcursion BB429FinishScanEDelta
open BB429Low42Physical BB429PhysicalNoFatalConverse

/-- Every physical configuration representing a Junc endpoint is
    non-C/01, since the Junc state is A. -/
theorem junc0_physical_c01_free (u w : Nat) (c : Config)
    (hrep : Represents (junc u 0 w) c) :
    ¬ physicalC01 c := by
  rcases hrep with ⟨hs, _, _, _⟩
  have hstate : c.state.val = 0 := by
    simpa [junc, BB429OddExcursion.z] using hs
  intro hf
  rcases hf with ⟨hsC, _, _⟩
  omega

/-- Every physical Junc endpoint is live: its A/1 transition is defined. -/
theorem junc0_physical_live (u w : Nat) (c : Config)
    (hrep : Represents (junc u 0 w) c) :
    rawStep target429 c ≠ none := by
  rcases hrep with ⟨hs, hc, _, _⟩
  have hstate : c.state.val = 0 := by
    simpa [junc, BB429OddExcursion.z] using hs
  have hbit : c.tape c.head = true := by
    simpa [junc, BB429OddExcursion.z] using hc
  have hstate' : c.state = (⟨0, by decide⟩ : Fin 6) := Fin.ext hstate
  have hslot : readSlot c = (⟨0, by decide⟩, true) := by
    simp [readSlot, hstate', hbit]
  have htable : target429 (⟨0, by decide⟩, true) =
      some ⟨false, false, ⟨5, by decide⟩⟩ := by
    decide
  have hraw : rawStep target429 c =
      some (applyMove c ⟨false, false, ⟨5, by decide⟩⟩) := by
    unfold rawStep
    rw [hslot, htable]
    rfl
  rw [hraw]
  simp

/-- The canonical low42 physical return has avoided C/01 at every
    primitive prefix. The endpoint is a live Junc, so this follows from
    the physical transition table and does not require a zipper lift for
    each prefix. -/
theorem low42_raw_head_all_c01_free (j k : Nat) :
    ∃ c' : Config,
      run target429 (4*j*j+22*j+18*k+79)
        {state:=BB6Bubble.A, head:=0,
         tape:=jTape (j+2*k+1) (2*j)} = some c' ∧
      Represents (junc 0 0 (4*j+4*k+12)) c' ∧
      (∀ t, t ≤ 4*j*j+22*j+18*k+79 →
        ∃ d : Config,
          run target429 t
            {state:=BB6Bubble.A, head:=0,
             tape:=jTape (j+2*k+1) (2*j)} = some d ∧
          ¬ physicalC01 d) := by
  obtain ⟨c', hrun, hrep, _⟩ := low42_raw_head_all j k
  refine ⟨c', hrun, hrep, ?_⟩
  exact physical_run_prefix_c01_free
    (4*j*j+22*j+18*k+79)
    {state:=BB6Bubble.A, head:=0,
     tape:=jTape (j+2*k+1) (2*j)}
    c' hrun
    (junc0_physical_c01_free 0 (4*j+4*k+12) c' hrep)
    (junc0_physical_live 0 (4*j+4*k+12) c' hrep)

#print axioms junc0_physical_c01_free
#print axioms junc0_physical_live
#print axioms low42_raw_head_all_c01_free

end BB429Low42PhysicalNoFatal
