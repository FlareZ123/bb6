import Low42PhysicalNoFatal
import JuncCanonical
import RootShift
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 65536

namespace BB429Low42PhysicalNoFatalAnyHead

open BB6Coverage BB6Bubble
open BB429PhysicalFrontier BB429PhysicalBridge
open BB429OddExcursion BB429FinishScanEDelta
open BB429JPhysical BB429JuncCanonical
open BB429PhysicalNoFatalConverse BB429Low42PhysicalNoFatal

/-- The canonical physical J configuration for Junc(u,0,w). -/
def jConfig (u w : Nat) : Config :=
  {state:=BB6Bubble.A, head:=0, tape:=jTape u w}

/-- The canonical J tape shifted to an arbitrary absolute head is exactly
    the translated-J configuration used by the Junc representation theorem. -/
theorem translatedJ_eq_shift (u w : Nat) (h : Int) :
    translatedJ u w h = shiftConfig h (jConfig u w) := by
  simp [translatedJ, shiftConfig, jConfig]

/-- Translation composes with the exact translated-J representation. -/
theorem shift_translatedJ (u w : Nat) (h k : Int) :
    shiftConfig h (translatedJ u w k) =
      translatedJ u w (k+h) := by
  ext
  · rfl
  · rfl
  · funext x
    simp [shiftConfig, translatedJ]
    congr 1
    omega

/-- C/01-freedom is invariant under physical tape/head translation. -/
theorem physicalC01_shift_free (h : Int) (c : Config)
    (hfree : ¬ physicalC01 c) :
    ¬ physicalC01 (shiftConfig h c) := by
  intro hf
  rcases hf with ⟨hs, hcur, hright⟩
  apply hfree
  have hcur' : c.tape c.head = false := by
    change c.tape ((c.head+h)-h) = false at hcur
    have hpos : (c.head+h)-h = c.head := by omega
    rw [hpos] at hcur
    exact hcur
  have hright' : c.tape (c.head+1) = true := by
    change c.tape (((c.head+h)+1)-h) = true at hright
    have hpos : ((c.head+h)+1)-h = c.head+1 := by omega
    rw [hpos] at hright
    exact hright
  exact ⟨hs, hcur', hright'⟩

/-- The all-parameter low42 physical return applies to every complete
    physical configuration representing its Junc input, not just the
    canonical head-zero representative. It preserves the exact endpoint
    Junc, head displacement, and C/01-freedom at every primitive prefix. -/
theorem low42_raw_head_any_c01_free
    (j k : Nat) (c : Config)
    (hrep : Represents (junc (j+2*k+1) 0 (2*j)) c) :
    ∃ d : Config,
      run target429 (4*j*j+22*j+18*k+79) c = some d ∧
      Represents (junc 0 0 (4*j+4*k+12)) d ∧
      d.head = c.head - ((2*j+4*k+5:Nat):Int) ∧
      (∀ t, t ≤ 4*j*j+22*j+18*k+79 →
        ∃ e : Config, run target429 t c = some e ∧
          ¬ physicalC01 e) := by
  obtain ⟨d0, hrun0, hrep0, hhead0, hprefix0⟩ :=
    low42_raw_head_all_c01_free j k
  have hcanon :
      c = translatedJ (j+2*k+1) (2*j) c.head :=
    represented_junc_eq_translatedJ (j+2*k+1) (2*j) c hrep
  have hshift :
      c = shiftConfig c.head (jConfig (j+2*k+1) (2*j)) := by
    calc
      c = translatedJ (j+2*k+1) (2*j) c.head := hcanon
      _ = shiftConfig c.head (jConfig (j+2*k+1) (2*j)) :=
        translatedJ_eq_shift (j+2*k+1) (2*j) c.head
  have hrun :
      run target429 (4*j*j+22*j+18*k+79) c =
        some (shiftConfig c.head d0) := by
    calc
      run target429 (4*j*j+22*j+18*k+79) c =
          run target429 (4*j*j+22*j+18*k+79)
            (shiftConfig c.head (jConfig (j+2*k+1) (2*j))) := by
              rw [hshift]
      _ = (run target429 (4*j*j+22*j+18*k+79)
            (jConfig (j+2*k+1) (2*j))).map (shiftConfig c.head) :=
          shift_run c.head target429
            (jConfig (j+2*k+1) (2*j))
            (4*j*j+22*j+18*k+79)
      _ = some (shiftConfig c.head d0) := by simp [jConfig, hrun0]
  have hrepD :
      Represents (junc 0 0 (4*j+4*k+12)) (shiftConfig c.head d0) := by
    apply (represented_junc_iff_translatedJ 0 (4*j+4*k+12) _).2
    calc
      shiftConfig c.head d0 =
          shiftConfig c.head (translatedJ 0 (4*j+4*k+12) d0.head) := by
            rw [represented_junc_eq_translatedJ 0 (4*j+4*k+12) d0 hrep0]
      _ = translatedJ 0 (4*j+4*k+12) (d0.head+c.head) :=
        shift_translatedJ 0 (4*j+4*k+12) c.head d0.head
      _ = translatedJ 0 (4*j+4*k+12) (shiftConfig c.head d0).head := by
        simp [shiftConfig]
  have hhead :
      (shiftConfig c.head d0).head =
        c.head - ((2*j+4*k+5:Nat):Int) := by
    change d0.head + c.head =
      c.head - ((2*j+4*k+5:Nat):Int)
    rw [hhead0]
    omega
  have hprefix :
      ∀ t, t ≤ 4*j*j+22*j+18*k+79 →
        ∃ e : Config, run target429 t c = some e ∧
          ¬ physicalC01 e := by
    intro t ht
    obtain ⟨e0, he0, hfree0⟩ := hprefix0 t ht
    refine ⟨shiftConfig c.head e0, ?_, ?_⟩
    · calc
        run target429 t c =
            run target429 t (shiftConfig c.head
              (jConfig (j+2*k+1) (2*j))) := by rw [hshift]
        _ = (run target429 t (jConfig (j+2*k+1) (2*j))).map
              (shiftConfig c.head) :=
            shift_run c.head target429
              (jConfig (j+2*k+1) (2*j)) t
        _ = some (shiftConfig c.head e0) := by simp [jConfig, he0]
    · exact physicalC01_shift_free c.head e0 hfree0
  exact ⟨shiftConfig c.head d0, hrun, hrepD, hhead, hprefix⟩

#print axioms translatedJ_eq_shift
#print axioms shift_translatedJ
#print axioms physicalC01_shift_free
#print axioms low42_raw_head_any_c01_free

end BB429Low42PhysicalNoFatalAnyHead
