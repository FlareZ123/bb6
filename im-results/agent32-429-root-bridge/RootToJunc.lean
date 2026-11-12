import SourceBridge
import High0Physical
import High3Ladder
import JuncCanonical
import Lean.Elab.Tactic.Omega

namespace BB429RootToJunc

open BB6Coverage BB6Bubble BB429PhysicalFrontier BB429JPhysical
open BB429RootEntry BB429High0Physical BB429High3Ladder BB429JuncCanonical

/-- The exact 35-step blank-root endpoint is the translated physical J(0,0)
    configuration used by the source-certified high-zero branch. -/
theorem j00Config_eq_shifted_jConfig :
    j00Config = shiftConfig 3 (jConfig 0 0) := by
  ext <;> simp [j00Config, shiftConfig, jConfig,
    rootTape_matches_physical_j00]

/-- The endpoint of the 110-step high-zero continuation from the authentic
    root J(0,0) state is exactly the translated canonical Junc(0,0,12)
    configuration, not merely a tape with the same finite support. -/
theorem rootAfterHigh0_endpoint_eq :
    rootAfterHigh0.1 = translatedJ 0 12 (-3) := by
  obtain ⟨c, hrun, hrep, hhead⟩ := j_high0_to_junc_raw 0
  have hshift : run target429 110 j00Config =
      some (shiftConfig 3 c) := by
    calc
      run target429 110 j00Config =
          run target429 110 (shiftConfig 3 (jConfig 0 0)) := by
            rw [j00Config_eq_shifted_jConfig]
      _ = (run target429 110 (jConfig 0 0)).map (shiftConfig 3) :=
        run_shiftConfig target429 110 3 (jConfig 0 0)
      _ = some (shiftConfig 3 c) := by
        simpa [jConfig] using
          congrArg (fun o : Option Config => o.map (shiftConfig 3)) hrun
  have hproj := runWithHeadMax_projects source429 110 j00Config
    rootAfterHigh0.1 rootAfterHigh0.2 root_high0_monitor_computes
  have hroot : run target429 110 j00Config = some rootAfterHigh0.1 := by
    simpa [source429_eq_target429] using hproj
  have heq : rootAfterHigh0.1 = shiftConfig 3 c :=
    Option.some.inj (hroot.symm.trans hshift)
  rw [heq]
  have hcanon := represented_junc_eq_translatedJ 0 12 c hrep
  have hhead' : c.head = -6 := by simpa using hhead
  rw [hcanon, hhead']
  ext <;> simp [shiftConfig, translatedJ] <;> omega

/-- Cumulative maximum-head monitor for the genuine blank-root run through
    the high-zero return. The two segments are composed with the monitor's
    exact max law: 35 steps to J(0,0), then 110 steps to Junc(0,0,12). -/
theorem root_after_145_monitor :
    runWithHeadMax target429 145 blank =
      some (translatedJ 0 12 (-3), 12) := by
  have hfirst : runWithHeadMax target429 35 blank =
      some (j00Config, 6) := by
    simpa [source429_eq_target429] using blank_reaches_j00_with_head_max
  have hpair : rootAfterHigh0 = (translatedJ 0 12 (-3), 12) := by
    exact Prod.ext rootAfterHigh0_endpoint_eq root_high0_head_max
  have hsecond : runWithHeadMax target429 110 j00Config =
      some (translatedJ 0 12 (-3), 12) := by
    have h := root_high0_monitor_computes
    rw [hpair] at h
    simpa [source429_eq_target429] using h
  calc
    runWithHeadMax target429 145 blank =
        runWithHeadMax target429 (35 + 110) blank := by omega
    _ = (runWithHeadMax target429 35 blank).bind (fun (d, h₁) =>
          (runWithHeadMax target429 110 d).map
            (fun (e, h₂) => (e, max h₁ h₂))) :=
      runWithHeadMax_add target429 35 110 blank
    _ = some (translatedJ 0 12 (-3), 12) := by
      simp only [hfirst, Option.bind_some, hsecond, Option.map_some]
      have hmax : max (6 : Int) 12 = 12 := by omega
      rw [hmax]

/-- The authentic blank root reaches the exact physical Junc(0,0,12)
    checkpoint after 145 successful raw moves. Its cumulative head maximum
    equals its rightmost marked cell, and the entire right tape tail is blank. -/
theorem root_after_145_junc_frontier :
    runWithHeadMax target429 145 blank =
      some (translatedJ 0 12 (-3), 12) ∧
    Represents (junc 0 0 12) (translatedJ 0 12 (-3)) ∧
    (translatedJ 0 12 (-3)).head = -3 ∧
    (translatedJ 0 12 (-3)).tape 12 = true ∧
    (∀ x, 12 < x → (translatedJ 0 12 (-3)).tape x = false) := by
  refine ⟨root_after_145_monitor, canonical_junc_rep 0 12 (-3), rfl, ?_, ?_⟩
  · simpa [rootAfterHigh0_endpoint_eq] using root_high0_frontier_base.2.1
  · intro x hx
    simpa [rootAfterHigh0_endpoint_eq] using root_high0_frontier_base.2.2 x hx

#print axioms rootAfterHigh0_endpoint_eq
#print axioms root_after_145_monitor
#print axioms root_after_145_junc_frontier

end BB429RootToJunc
