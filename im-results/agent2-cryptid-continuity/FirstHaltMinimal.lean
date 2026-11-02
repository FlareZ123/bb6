import Lean.Elab.Tactic.Omega
import ExactFirstHalt

set_option maxRecDepth 8192

namespace BB6.CryptidFirstHalt
open CryptidBoundary
open BB6.CryptidBRun
open BB6.CryptidExactHalt

/-- The original machine's newly introduced state6 is frozen. -/
theorem frozen_step (c : Cfg) (hc : c.st=6) :
    step c = c := by
  cases c with
  | mk l h r st =>
    simp only at hc
    subst st
    simp [step]

/-- A configuration already in frozen halt state6 remains identical
    under every number of further raw machine transitions. -/
theorem frozen_run (c : Cfg) (hc : c.st=6) (s : Nat) :
    run s c = c := by
  induction s with
  | zero => rfl
  | succ s ih =>
    have hstep : run 1 c = c := by
      simp [run, frozen_step c hc]
    have ht : s+1=1+s := by omega
    rw [ht, run_add, hstep]
    exact ih

/-- If a run ends in F-on-one, it could not have entered the frozen
    halt state6 at any earlier time. -/
theorem no_prior_halt {c : Cfg} {t : Nat}
    (h : (run t c).st = 5) :
    ∀ s, s ≤ t → (run s c).st ≠ 6 := by
  intro s hs h6
  have hr : run t c = run (t-s) (run s c) := by
    calc
      run t c = run (s+(t-s)) c := by congr 1; omega
      _ = run (t-s) (run s c) := by rw [run_add]
  rw [hr, frozen_run (run s c) h6 (t-s)] at h
  omega

/-- Every unary F-section has a prepared finite suffix with a
    *certified first* entry into halt state6 at a specific successor time.

    This theorem applies to arbitrary synthetic F-section inputs only.
    It does not assert a halt or nonhalt from the genuine blank start. -/
theorem every_unary_has_exact_first_halt (n : Nat) :
    ∃ (xs : List Bool) (t : Nat),
      (run (t+1) (I n xs)).st = 6 ∧
      (run t (I n xs)).st = 5 ∧
      (run t (I n xs)).h = true ∧
      ∀ s, s ≤ t → (run s (I n xs)).st ≠ 6 := by
  obtain ⟨xs,t,hs,hh,halt⟩ := every_unary_has_pre_halt_extension_all n
  exact ⟨xs,t,halt,hs,hh,no_prior_halt hs⟩

#print axioms frozen_step
#print axioms frozen_run
#print axioms no_prior_halt
#print axioms every_unary_has_exact_first_halt
end BB6.CryptidFirstHalt
