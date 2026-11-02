import CheckpointTransport
import BlankFurther
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 16384

namespace BB6.Agent19.Physical

/-- Extract the state component of a physical observational equality without
    unfolding either source run. This keeps enormous certified checkpoints
    opaque while retaining the exact state projection. -/
private theorem obsEq_state {c d : CryptidBoundary.Cfg}
    (h : BB6.BoundaryPadding.ObsEq c d) : c.st = d.st := by
  change BB6.BoundaryPadding.CfgEq
    (BB6.BoundaryPadding.represent c)
    (BB6.BoundaryPadding.represent d) at h
  exact h.2.2.2

/-- The original certified frozen-source blank configuration is exactly
    the same infinite physical tape as the literal D0 rooted blank input. -/
theorem source_blank_physically_blank :
    realize (boundarySafe CryptidBoundary.blank (by decide) 0) =
      BB6.Portfolio.blank (0 : BB6.Portfolio.State) := by
  simp only [realize,boundarySafe,BB6.BoundaryPadding.represent,
    CryptidBoundary.blank,encode,BB6.Portfolio.translateCfg,
    BB6.Portfolio.blank,Int.zero_add,Int.sub_zero]
  congr 1
  funext i
  by_cases hi0 : i=0
  · subst i
    simp [tape]
  · by_cases hineg : i<0
    · simp [tape,hi0,hineg,BB6.Padding.bitAt_nil]
    · simp [tape,hi0,hineg,BB6.Padding.bitAt_nil]

/-- Agent35's source-certified enormous genuine blank endpoint is still
    a live F/0 configuration. This extracts only the authentic source
    state component of its infinite-blank observational equality. -/
theorem original_blank_big_state :
    (CryptidBoundary.run 19848692333528818046 CryptidBoundary.blank).st = 5 := by
  have h := CryptidBoundary.blank19848692333528818046
  have hs := obsEq_state h
  exact Eq.trans hs (by rfl)

/-- Exact infinite-tape primitive-run existence at the source-authenticated
    19.8-quintillion-step checkpoint of the actual original D0 blank root. -/
theorem actual_D0_blank_big_live :
    BB6.Portfolio.run BB6.Portfolio.D0 19848692333528818046
      (some (BB6.Portfolio.blank (0 : BB6.Portfolio.State))) ≠ none := by
  have hiff := raw_run_none_iff_boundary_frozen
    19848692333528818046 CryptidBoundary.blank (by decide) 0
  rw [source_blank_physically_blank] at hiff
  intro hbad
  have hf := hiff.mp hbad
  rw [original_blank_big_state] at hf
  omega

/-- The entire physical tape is certified at the long genuine blank endpoint,
    including a witness for its physical head position. -/
theorem actual_D0_blank_big_checkpoint :
    ∃ nextOffset : Int,
      BB6.Portfolio.run BB6.Portfolio.D0 19848692333528818046
        (some (BB6.Portfolio.blank (0 : BB6.Portfolio.State))) =
      some (realize (boundarySafe
        (CryptidBoundary.run 19848692333528818046 CryptidBoundary.blank)
        (by rw [original_blank_big_state]; decide) nextOffset)) := by
  have hlive :
      (CryptidBoundary.run 19848692333528818046 CryptidBoundary.blank).st < 6 := by
    rw [original_blank_big_state]
    decide
  have h := source_live_checkpoint
    19848692333528818046 CryptidBoundary.blank
    (CryptidBoundary.run 19848692333528818046 CryptidBoundary.blank)
    (by decide) hlive rfl 0
  rw [source_blank_physically_blank] at h
  exact h

/-- Every earlier primitive-time halting predicate of the original literal
    rooted D0 machine is false. The claim is a finite lower bound, not a
    new BB(6) champion or machine nonhalting theorem. -/
theorem actual_D0_blank_no_earlier_halt (t : Nat)
    (ht : t < 19848692333528818046) :
    ¬ BB6.Portfolio.haltsAt BB6.Portfolio.D0
       (0 : BB6.Portfolio.State) t := by
  intro hh
  have hrun := actual_D0_blank_big_live
  cases h : BB6.Portfolio.run BB6.Portfolio.D0 19848692333528818046
      (some (BB6.Portfolio.blank (0 : BB6.Portfolio.State))) with
  | none => exact hrun h
  | some d =>
    have hle := BB6.Portfolio.no_halt_before_prefix
      BB6.Portfolio.D0 (BB6.Portfolio.blank (0 : BB6.Portfolio.State))
      d 19848692333528818046 t h hh
    omega

#print axioms source_blank_physically_blank
#print axioms original_blank_big_state
#print axioms actual_D0_blank_big_live
#print axioms actual_D0_blank_big_checkpoint
#print axioms actual_D0_blank_no_earlier_halt
end BB6.Agent19.Physical
