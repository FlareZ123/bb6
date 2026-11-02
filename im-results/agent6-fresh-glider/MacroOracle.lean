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

/-- The symmetric finite witness advances into a pristine LEFT ray, while
    every intermediate head stays at or left of its original location. -/
def finiteMacroLeftCheck (p : PartialMachine) (n delta : Nat) : Bool :=
  match finitePartialRun p n finiteBlank with
  | none => false
  | some c =>
      decide (c.state = 0) &&
      decide (c.head = -(delta : Int)) &&
      finiteFreshLeft c &&
      (List.range n).all (fun k =>
        match finitePartialRun p k finiteBlank with
        | none => false
        | some d => decide (d.head <= 0))

theorem finiteMacroLeftCheck_sound (p : PartialMachine)
    (n delta bound : Nat) (hn : 0 < n) (hdelta : 0 < delta)
    (h : finiteMacroLeftCheck p n delta = true) :
    Cover (DecidedBelow bound) p := by
  cases hfin : finitePartialRun p n finiteBlank with
  | none =>
      simp [finiteMacroLeftCheck, hfin] at h
  | some c =>
      simp only [finiteMacroLeftCheck, hfin, Bool.and_eq_true,
        decide_eq_true_eq] at h
      rcases h with ⟨⟨⟨hs, hh⟩, hfresh⟩, hwindow⟩
      apply Cover.leaf
      intro m hm
      left
      apply fresh_left_macro_never m n delta hn hdelta
      · refine ⟨embedFinRay c, ?_, ?_, ?_, ?_⟩
        · simpa only [embedFinRay_blank] using
            (finitePartialRun_sound p m hm finiteBlank c n hfin)
        · exact hs
        · exact hh
        · intro x hx
          have hblank := finiteFreshLeft_sound c hfresh
          apply hblank x
          simpa [embedFinRay, hh] using hx
      · intro k hk d hrun
        have hflag :
            (match finitePartialRun p k finiteBlank with
              | none => false
              | some t => decide (t.head <= 0)) = true :=
          (List.all_eq_true.mp hwindow) k (List.mem_range.mpr hk)
        cases hkfin : finitePartialRun p k finiteBlank with
        | none =>
            simp [hkfin] at hflag
        | some t =>
            have hle : t.head <= 0 := of_decide_eq_true (by simpa [hkfin] using hflag)
            have hsource : run m k blank = some (embedFinRay t) := by
              simpa only [embedFinRay_blank] using
                (finitePartialRun_sound p m hm finiteBlank t k hkfin)
            have heq : d = embedFinRay t :=
              Option.some.inj (hrun.symm.trans hsource)
            subst d
            simpa [embedFinRay] using hle

def finiteMacroLeftOracle (p : PartialMachine) (limit : Nat) : Bool :=
  (List.range limit).any (fun i =>
    (List.range limit).any (fun j =>
      finiteMacroLeftCheck p (i+1) (j+1)))

theorem finiteMacroLeftOracle_sound (p : PartialMachine) (limit bound : Nat)
    (h : finiteMacroLeftOracle p limit = true) :
    Cover (DecidedBelow bound) p := by
  obtain ⟨i, _, hi⟩ := List.any_eq_true.mp h
  obtain ⟨j, _, hij⟩ := List.any_eq_true.mp hi
  exact finiteMacroLeftCheck_sound p (i+1) (j+1) bound
    (by omega) (by omega) hij

/-- Bidirectional version of the reusable finite-macro oracle. -/
def finiteMacroOracle (p : PartialMachine) (limit : Nat) : Bool :=
  finiteMacroRightOracle p limit || finiteMacroLeftOracle p limit

theorem finiteMacroOracle_sound (p : PartialMachine) (limit bound : Nat)
    (h : finiteMacroOracle p limit = true) :
    Cover (DecidedBelow bound) p := by
  rcases (Bool.or_eq_true _ _).mp h with hr | hl
  · exact finiteMacroRightOracle_sound p limit bound hr
  · exact finiteMacroLeftOracle_sound p limit bound hl

/-- Five-step ray pump using five assigned slots; disjoint from all 620
    previously enumerated 3/4-step and turnaround glider cylinder patterns.
    A/0=1RB, B/0=1LC, C/1=0RD, D/1=0LE, E/0=0RA. -/
def fiveStepMacroTable : PartialMachine := fun s =>
  if s = (0,false) then some (some ⟨true,true,1⟩)
  else if s = (1,false) then some (some ⟨true,false,2⟩)
  else if s = (2,true) then some (some ⟨false,true,3⟩)
  else if s = (3,true) then some (some ⟨false,false,4⟩)
  else if s = (4,false) then some (some ⟨false,true,0⟩)
  else none

theorem five_step_macro_check :
    finiteMacroRightCheck fiveStepMacroTable 5 1 = true := by decide

theorem five_step_macro_leaf (bound : Nat) :
    Cover (DecidedBelow bound) fiveStepMacroTable :=
  finiteMacroRightCheck_sound fiveStepMacroTable 5 1 bound
    (by decide) (by decide) five_step_macro_check

def leftMacroExample : PartialMachine := fun s =>
  if s = (0,false) then some (some ⟨true,false,1⟩)
  else if s = (1,false) then some (some ⟨false,true,2⟩)
  else if s = (2,true) then some (some ⟨false,false,0⟩)
  else none

theorem left_macro_example_check :
    finiteMacroLeftCheck leftMacroExample 3 1 = true := by decide

theorem left_macro_example_leaf (bound : Nat) :
    Cover (DecidedBelow bound) leftMacroExample :=
  finiteMacroLeftCheck_sound leftMacroExample 3 1 bound
    (by decide) (by decide) left_macro_example_check

#print axioms finiteMacroLeftCheck_sound
#print axioms finiteMacroLeftOracle_sound
#print axioms finiteMacroOracle_sound
#print axioms five_step_macro_leaf
#print axioms left_macro_example_leaf


end BB6Coverage
