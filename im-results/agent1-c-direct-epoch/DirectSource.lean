import DirectEpoch
import ExactDeltaFour
import GenericSection
import Lean.Elab.Tactic.Omega

namespace BB6.Agent1Direct
open BB6.Agent46

/-- The direct branch is a genuine edge of Agent46's unchanged source. -/
theorem source_direct_edge (a k : Nat)
    (ha : 2≤a) (hk : 0<k) (hg : 2*k≤a) :
    secNext (a,k)=some (a-2*k,2*k+2) := by
  simp [secNext,exactSection,show a≠0 by omega,
    show a≠1 by omega,show k≠0 by omega,hg]

/-- Every direct chain is an actual finite orbit of the original section. -/
theorem direct_run_source {n a k x y : Nat}
    (h : Direct n a k x y) :
    BB6.Agent8Section.run secNext n (some (a,k))=some (x,y) := by
  induction h with
  | zero a k => rfl
  | @succ n a k b c h ha hk hg ih =>
      simp only [BB6.Agent8Section.run,ih,Option.bind_some,
        source_direct_edge b c ha hk hg]

theorem direct_to_minimal {n a k x y : Nat}
    (h : Direct n a k x y) : MinimalRun secNext n a k x y := by
  induction h with
  | zero a k => exact MinimalRun.zero a k
  | @succ n a k b c h ha hk hg ih =>
      apply MinimalRun.succ ih (source_direct_edge b c ha hk hg)
      omega

/-- Every source edge of exact gain four comes from the direct branch. -/
theorem minimal_to_direct {n a k x y : Nat}
    (h : MinimalRun secNext n a k x y) : Direct n a k x y := by
  induction h with
  | zero a k => exact Direct.zero a k
  | @succ n a k b c x y h hs hw ih =>
      have hp := (section_delta_four_iff_direct b c x y hs).mp hw
      obtain ⟨ha,hk,hg⟩ := hp
      have hf := source_direct_edge b c ha hk hg
      have hxy : x=b-2*c ∧ y=2*c+2 := by
        have hh : some (x,y) = some (b-2*c,2*c+2) := hs.symm.trans hf
        exact Prod.mk.inj (Option.some.inj hh)
      rcases hxy with ⟨hx,hy⟩
      subst x
      subst y
      exact Direct.succ ih ha hk hg

/-- Exact single-inequality criterion for r+1 successive authentic
    minimum-gain source transitions, for any positive-right input. -/
theorem source_minimal_iff_guard (a k r : Nat) (hk : 0<k) :
    (∃x y, MinimalRun secNext (r+1) a k x y) ↔ Allowed a k r := by
  constructor
  · rintro ⟨x,y,h⟩
    exact direct_last_allowed (minimal_to_direct h)
  · intro hl
    obtain ⟨x,y,hd⟩ := (direct_iff_last_guard a k r hk).mpr hl
    exact ⟨x,y,direct_to_minimal hd⟩

/-- No positive-right Machine C source can sustain gain four indefinitely. -/
theorem source_no_long_minimal (a k x y : Nat) :
    ¬ MinimalRun secNext (a+2*k+4) a k x y := by
  intro h
  exact direct_bounded a k x y (minimal_to_direct h)

#print axioms source_direct_edge
#print axioms direct_run_source
#print axioms minimal_to_direct
#print axioms source_minimal_iff_guard
#print axioms source_no_long_minimal
end BB6.Agent1Direct
