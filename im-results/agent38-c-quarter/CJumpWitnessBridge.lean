import CQuarterBridge
import CJumpWitness

namespace BB6Agent38

/-- Original unmodified Agent 11 Machine C accelerator: precise blank-entry
    trajectory reaches the a=2, c=0 boundary after 567,323,514 steps. -/
theorem source_blank_reaches_a2_c0 :
    sourceRun 567323514 (some (5,0,1)) = some (2,62973,0) := by
  rw [source_run_agrees]
  exact blank_reaches_a2_c0

theorem source_run_none (n:Nat) : sourceRun n none = none := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [sourceRun] using ih

theorem source_reach_of_run (n : Nat) (s t : S)
    (h : sourceRun n (some s) = some t)
    (hr : BB6CLine.Reach s) : BB6CLine.Reach t := by
  induction n generalizing s t with
  | zero =>
      have hsame : s=t := by simpa [sourceRun] using h
      subst t
      exact hr
  | succ n ih =>
      cases hn : BB6CLine.nextC s with
      | none => simp [sourceRun,hn,source_run_none] at h
      | some u =>
          have hu : sourceRun n (some u) = some t := by
            simpa [sourceRun,hn] using h
          exact ih u t hu (BB6CLine.Reach.next s u hr hn)

/-- A Lean-kernel verified reachable state from the exact blank configuration. -/
theorem published_blank_reaches_a2_c0 : BB6CLine.Reach (2,62973,0) := by
  exact source_reach_of_run 567323514 (5,0,1) (2,62973,0)
    source_blank_reaches_a2_c0 BB6CLine.Reach.init

/-- The strong rank-progress inequality of Agent 38 is met with equality on
    an actual blank-reachable Machine C transition. -/
theorem reachable_energy_step_exact :
    BB6CLine.Reach (2,62973,0) ∧
    BB6CLine.nextC (2,62973,0) = some (0,1,125947) ∧
    energy (2,62973,0) + 4*rank (0,1,125947) + 4 =
      energy (0,1,125947) + 4*rank (2,62973,0) := by
  constructor
  · exact published_blank_reaches_a2_c0
  constructor <;> decide

#print axioms source_blank_reaches_a2_c0
#print axioms published_blank_reaches_a2_c0
#print axioms reachable_energy_step_exact
end BB6Agent38
