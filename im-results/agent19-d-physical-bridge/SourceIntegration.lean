import PhysicalBridge
import BoundaryPadding
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19.Physical

/-- Literal six-state-table reconciliation: the original finite-list
    source and the physical model have matching live transitions and
    identical halting predicates at every list-state. -/
theorem list_step_projection (c : SafeCfg) :
    (stepFinite c).map SafeCfg.data =
      if (BB6.Padding.step BB6.BoundaryPadding.delta c.data).state = 6
      then none else some (BB6.Padding.step BB6.BoundaryPadding.delta c.data) := by
  obtain ⟨⟨left,bit,right,st⟩,offset,live⟩ := c
  have hcase : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    change st < 6 at live
    omega
  rcases hcase with h|h|h|h|h|h <;> subst st <;>
    cases bit <;>
    simp [stepFinite, BB6.Padding.step,BB6.BoundaryPadding.delta,
      BB6.Portfolio.D0,BB6.Padding.goLeft,BB6.Padding.goRight] <;> decide

/-- Live and frozen-halt states are related by an exact output projection. -/
def RunRel (finite : Option SafeCfg) (total : BB6.Padding.Config) : Prop :=
  match finite with
  | none => total.state = 6
  | some c => c.data = total

private theorem frozen_six (data : BB6.Padding.Config) (h6 : data.state = 6) :
    BB6.Padding.step BB6.BoundaryPadding.delta data = data := by
  cases data with
  | mk l bit r state =>
    dsimp at h6
    subst state
    cases bit <;> rfl

theorem rel_step (finite : Option SafeCfg) (total : BB6.Padding.Config)
    (hr : RunRel finite total) :
    RunRel (finite.bind stepFinite)
      (BB6.Padding.step BB6.BoundaryPadding.delta total) := by
  cases finite with
  | none =>
    change (BB6.Padding.step BB6.BoundaryPadding.delta total).state = 6
    have hh : total.state = 6 := hr
    rw [frozen_six total hh]
    exact hh
  | some cfg =>
    change cfg.data = total at hr
    subst total
    have hproj := list_step_projection cfg
    cases hs : stepFinite cfg with
    | none =>
      simp only [Option.bind_some,hs,RunRel]
      by_cases hh : (BB6.Padding.step BB6.BoundaryPadding.delta cfg.data).state = 6
      · exact hh
      · simp [hs,hh] at hproj
    | some cfg2 =>
      simp only [Option.bind_some,hs,RunRel]
      by_cases hh : (BB6.Padding.step BB6.BoundaryPadding.delta cfg.data).state = 6
      · simp [hs,hh] at hproj
      · simpa [hs,hh] using hproj

theorem rel_run (n : Nat) (finite : Option SafeCfg)
    (total : BB6.Padding.Config) (hr : RunRel finite total) :
    RunRel (runFinite n finite)
      (BB6.Padding.run BB6.BoundaryPadding.delta n total) := by
  induction n with
  | zero => exact hr
  | succ n ih =>
    change RunRel ((runFinite n finite).bind stepFinite)
      (BB6.Padding.step BB6.BoundaryPadding.delta
        (BB6.Padding.run BB6.BoundaryPadding.delta n total))
    exact rel_step _ _ ih

/-- No simulated horizon: partial raw execution has become undefined iff
    the exact frozen-state finite machine has entered its state 6. -/
theorem source_total_halt_iff (n : Nat) (c : SafeCfg) :
    BB6.Portfolio.run BB6.Portfolio.D0 n (some (realize c)) = none ↔
      (BB6.Padding.run BB6.BoundaryPadding.delta n c.data).state = 6 := by
  have hrun := run_semiconjugacy n (some c)
  have hrel := rel_run n (some c) c.data rfl
  cases hh : runFinite n (some c) with
  | none =>
    simp only [hh,Option.map_none,Option.map_some] at hrun
    simp only [hh,RunRel] at hrel
    rw [hrun]
    simp [hrel]
  | some t =>
    simp only [hh,Option.map_some] at hrun
    have heq : t.data = BB6.Padding.run BB6.BoundaryPadding.delta n c.data := by
      simpa only [hh,RunRel] using hrel
    rw [hrun]
    have hneq : ¬(BB6.Padding.run BB6.BoundaryPadding.delta n c.data).state=6 := by
      rw [←heq]
      exact Nat.ne_of_lt t.running
    simp [hneq]

/-- Any state other than the frozen state 6 can be embedded exactly in the
    physical infinite-tape simulator. -/
def boundarySafe (c : CryptidBoundary.Cfg) (hc : c.st < 6)
    (offset : Int) : SafeCfg :=
  ⟨BB6.BoundaryPadding.represent c, offset, hc⟩

/-- The independent D-table models agree on the first moment of undefined
    halting for EVERY primitive time, including nonhalting prefixes. -/
theorem raw_run_none_iff_boundary_frozen (n : Nat) (c : CryptidBoundary.Cfg)
    (hc : c.st < 6) (offset : Int) :
    BB6.Portfolio.run BB6.Portfolio.D0 n
      (some (realize (boundarySafe c hc offset))) = none ↔
        (CryptidBoundary.run n c).st = 6 := by
  have h := source_total_halt_iff n (boundarySafe c hc offset)
  have heq := BB6.BoundaryPadding.source_run n c
  change BB6.Portfolio.run BB6.Portfolio.D0 n
      (some (realize (boundarySafe c hc offset))) = none ↔
        (BB6.Padding.run BB6.BoundaryPadding.delta n
          (BB6.BoundaryPadding.represent c)).state = 6 at h
  rw [←heq] at h
  exact h

/-- Generic partial-machine semantics: a halt at a live configuration
    is equivalent to eventual undefined raw-run output. -/
theorem halt_iff_eventually_run_none (M : BB6.Portfolio.Machine)
    (c : BB6.Portfolio.Cfg) :
    BB6.Portfolio.HaltsCfg M c ↔
      ∃ n, BB6.Portfolio.run M n (some c) = none := by
  constructor
  · rintro ⟨n,last,hr,hs⟩
    refine ⟨n+1, ?_⟩
    simp [BB6.Portfolio.run, hr, hs]
  · rintro ⟨n,hn⟩
    have h : ∀ n, BB6.Portfolio.run M n (some c) = none →
        BB6.Portfolio.HaltsCfg M c := by
      intro m
      induction m with
      | zero =>
        intro hz
        simp [BB6.Portfolio.run] at hz
      | succ m ih =>
        intro hz
        change (BB6.Portfolio.run M m (some c)).bind (BB6.Portfolio.step M) = none at hz
        cases hm : BB6.Portfolio.run M m (some c) with
        | none => exact ih hm
        | some last =>
          have hs : BB6.Portfolio.step M last = none := by simpa [hm] using hz
          exact ⟨m, last, hm, hs⟩
    exact h n hn

/-- Arbitrary source tapes and head translations, ALL times:
    true raw-machine halting iff the original list interpreter enters its
    absorbing explicit terminal state. -/
theorem physical_halts_iff_boundary_halts (c : CryptidBoundary.Cfg)
    (hc : c.st < 6) (offset : Int) :
    BB6.Portfolio.HaltsCfg BB6.Portfolio.D0
      (realize (boundarySafe c hc offset)) ↔
        ∃ n, (CryptidBoundary.run n c).st = 6 := by
  rw [halt_iff_eventually_run_none]
  exact exists_congr (fun n => raw_run_none_iff_boundary_frozen n c hc offset)

#print axioms raw_run_none_iff_boundary_frozen
#print axioms halt_iff_eventually_run_none
#print axioms physical_halts_iff_boundary_halts
#print axioms list_step_projection
#print axioms rel_step
#print axioms rel_run
#print axioms source_total_halt_iff
end BB6.Agent19.Physical
