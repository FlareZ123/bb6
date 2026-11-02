import RayMacro
import RayFinite
import FreshRayGlider
import Lean.Elab.Tactic.Omega

namespace BB6Coverage

/-- A finite sparse trace returns to the blank state A, shifted right by
    `delta`, with an unmarked right ray. All preceding heads stay at or
    to the right of the original origin. Every consulted transition is
    already assigned ordinary in the sparse table. -/
def finiteMacroRightCheck (p : PartialMachine) (n delta : Nat) : Bool :=
  match finitePartialRun p n finiteBlank with
  | none => false
  | some c =>
      decide (c.state = 0) &&
      decide (c.head = (delta : Int)) &&
      finiteFreshRight c &&
      (List.range n).all (fun k =>
        match finitePartialRun p k finiteBlank with
        | none => false
        | some d => decide (0 <= d.head))

/-- A positive finite certificate is a universally valid nonhalting leaf,
    with no condition on any unassigned transition. -/
theorem finiteMacroRightCheck_sound (p : PartialMachine)
    (n delta bound : Nat) (hn : 0 < n) (hdelta : 0 < delta)
    (h : finiteMacroRightCheck p n delta = true) :
    Cover (DecidedBelow bound) p := by
  cases hfin : finitePartialRun p n finiteBlank with
  | none =>
      simp [finiteMacroRightCheck, hfin] at h
  | some c =>
      simp only [finiteMacroRightCheck, hfin, Bool.and_eq_true,
        decide_eq_true_eq] at h
      rcases h with ⟨⟨⟨hs, hh⟩, hfresh⟩, hwindow⟩
      apply Cover.leaf
      intro m hm
      left
      apply fresh_ray_macro_never m n delta hn hdelta
      · refine ⟨embedFinRay c, ?_, ?_, ?_, ?_⟩
        · simpa only [embedFinRay_blank] using
            (finitePartialRun_sound p m hm finiteBlank c n hfin)
        · exact hs
        · exact hh
        · intro x hx
          have hblank := finiteFreshRight_sound c hfresh
          apply hblank x
          simpa [embedFinRay, hh] using hx
      · intro k hk d hrun
        have hflag :
            (match finitePartialRun p k finiteBlank with
              | none => false
              | some t => decide (0 <= t.head)) = true :=
          (List.all_eq_true.mp hwindow) k (List.mem_range.mpr hk)
        cases hkfin : finitePartialRun p k finiteBlank with
        | none =>
            simp [hkfin] at hflag
        | some t =>
            have hge : 0 <= t.head := of_decide_eq_true (by simpa [hkfin] using hflag)
            have hsource : run m k blank = some (embedFinRay t) := by
              simpa only [embedFinRay_blank] using
                (finitePartialRun_sound p m hm finiteBlank t k hkfin)
            have heq : d = embedFinRay t :=
              Option.some.inj (hrun.symm.trans hsource)
            subst d
            simpa [embedFinRay] using hge

/-- Discover finite rightward self-replication witnesses of any positive
    length and displacement below a finite search cutoff. The cutoff is
    only for proof discovery, and places no bound on the certified run. -/
def finiteMacroRightOracle (p : PartialMachine) (limit : Nat) : Bool :=
  (List.range limit).any (fun i =>
    (List.range limit).any (fun j =>
      finiteMacroRightCheck p (i+1) (j+1)))

theorem finiteMacroRightOracle_sound (p : PartialMachine) (limit bound : Nat)
    (h : finiteMacroRightOracle p limit = true) :
    Cover (DecidedBelow bound) p := by
  obtain ⟨i, _, hi⟩ := List.any_eq_true.mp h
  obtain ⟨j, _, hij⟩ := List.any_eq_true.mp hi
  exact finiteMacroRightCheck_sound p (i+1) (j+1) bound
    (by omega) (by omega) hij

/-- The original three-step bounce is accepted without a specialized
    glider shape matcher. -/
theorem macro_example_check : finiteMacroRightCheck threeGliderExample 3 1 = true := by
  decide

theorem macro_example_leaf (bound : Nat) :
    Cover (DecidedBelow bound) threeGliderExample :=
  finiteMacroRightCheck_sound threeGliderExample 3 1 bound
    (by decide) (by decide) macro_example_check

theorem macro_example_oracle :
    finiteMacroRightOracle threeGliderExample 3 = true := by decide

#print axioms finiteMacroRightCheck_sound
#print axioms finiteMacroRightOracle_sound
#print axioms macro_example_leaf

end BB6Coverage
