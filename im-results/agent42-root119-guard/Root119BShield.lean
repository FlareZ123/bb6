import Root119BShift
namespace BB6Root119

/-- No length-four left-of-head factor `p q r 0` before the B head. -/
def NoLeft4 (p q r : Bool) (u : Conf) : Prop :=
  ∀ x : Int, x+3 < u.h →
    ¬(u.tape x = p ∧ u.tape (x+1) = q ∧
      u.tape (x+2) = r ∧ u.tape (x+3) = false)

/-- The 10-step B/0 shift never creates a new forbidden 4-word ending in 0
    entirely to the left of its new head. -/
theorem shifted_preserves_noLeft4 (p q r : Bool) (u : Conf)
    (hv : valid u) (hs : NoLeft4 p q r u) :
    NoLeft4 p q r (shifted u) := by
  rcases u with ⟨state,h,t⟩
  obtain ⟨hq,h0,h1,h2,h3,h4,h5⟩ := hv
  change t (h-3) = true at h3
  change ∀ x : Int, x+3<h → ¬(t x=p ∧ t (x+1)=q ∧ t (x+2)=r ∧ t (x+3)=false) at hs
  intro x hx hw
  change x+3 < h-2 at hx
  change shiftTape t h x = p ∧ shiftTape t h (x+1) = q ∧
    shiftTape t h (x+2) = r ∧ shiftTape t h (x+3) = false at hw
  by_cases hfar : x ≤ h-8
  · apply hs x (by omega)
    refine ⟨?_,?_,?_,?_⟩
    · rw [shiftTape_left t h x (by omega)] at hw
      exact hw.1
    · rw [shiftTape_left t h (x+1) (by omega)] at hw
      exact hw.2.1
    · rw [shiftTape_left t h (x+2) (by omega)] at hw
      exact hw.2.2.1
    · rw [shiftTape_left t h (x+3) (by omega)] at hw
      exact hw.2.2.2
  · have hxCases : x = h-7 ∨ x = h-6 := by omega
    rcases hxCases with h7 | h6
    · have hlast : shiftTape t h (x+3) = true := by
        rw [h7]
        have heq : h-7+3 = h-4 := by omega
        rw [heq]
        simp [shiftTape, setBit, show h-4 ≠ h by omega,
          show h-4 ≠ h-1 by omega, show h-4 ≠ h-2 by omega]
      simp [hlast] at hw
    · have hlast : shiftTape t h (x+3) = true := by
        rw [h6]
        have heq : h-6+3 = h-3 := by omega
        rw [heq]
        simp [shiftTape, setBit, h3, show h-3 ≠ h by omega,
          show h-3 ≠ h-1 by omega, show h-3 ≠ h-2 by omega,
          show h-3 ≠ h-4 by omega]
      simp [hlast] at hw

/-- Any finite alternating 10n sweep preserves every forbidden left 4-word
    whose rightmost symbol is 0. -/
theorem shiftMany_preserves_noLeft4 (p q r : Bool) (n : Nat) (u : Conf)
    (he : extended n u) (hs : NoLeft4 p q r u) :
    NoLeft4 p q r (shiftMany n u) := by
  induction n generalizing u with
  | zero => simpa [shiftMany] using hs
  | succ n ih =>
    have hv : valid u := extended_valid u he
    have hn : extended n (shifted u) := shifted_extended u he
    have hnew := shifted_preserves_noLeft4 p q r u hv hs
    simpa [shiftMany] using ih (shifted u) hn hnew

/-- Every exact `run` witness is a true descendant in the original
    inductively defined blank-root reachability relation. -/
theorem reachable_of_run (n : Nat) (c d : Conf) (hc : Reach c)
    (hr : run n c = some d) : Reach d := by
  induction n generalizing c with
  | zero =>
    simp only [run, Option.some.injEq] at hr
    subst d
    exact hc
  | succ n ih =>
    simp only [run] at hr
    cases he : next c with
    | none => simp [he] at hr
    | some e =>
      simp only [he, Option.bind_some] at hr
      exact ih e (Reach.follow hc he) hr

/-- A real blank-orbit B configuration with the alternating word gives an
    exact later reached configuration preserving any left 4-word ending in 0. -/
theorem reached_sweep_preserves_noLeft4 (p q r : Bool) (n : Nat)
    (c : Conf) (hc : Reach c) (hv : extended n c)
    (hs : NoLeft4 p q r c) :
    Reach (shiftMany n c) ∧ NoLeft4 p q r (shiftMany n c) := by
  exact ⟨reachable_of_run (10*n) c (shiftMany n c) hc (ten_n_steps n c hv),
    shiftMany_preserves_noLeft4 p q r n c hv hs⟩

#print axioms BB6Root119.reached_sweep_preserves_noLeft4
#print axioms BB6Root119.shifted_preserves_noLeft4
#print axioms BB6Root119.shiftMany_preserves_noLeft4
end BB6Root119
