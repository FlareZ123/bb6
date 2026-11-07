import HighEvenRightC23Residual
import FullForcedFilter
import FastFullBoolean
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent3FullForcedResidual

def highTargetX (j : Nat) : Nat := 2*j+3
def highTargetY (j m : Nat) : Nat :=
  2^(2*m+2)*(j+3)-(j+3*m+5)

/-- The sum-seven residue family is already a subfamily of the C23
    high exclusion. It is an independent source proof, not a new residual
    exclusion beyond C23. -/
theorem sum7_family_subset_c23_gate (j m : Nat)
    (hm5 : 5≤m) (hm4 : m%4=1)
    (hrel : (j+8)%32=(3*m+1)%32) :
    2≤m ∧ j%4=0 ∧ (j+7)%32=(3*m)%32 := by
  omega

#print axioms sum7_family_subset_c23_gate

/-- Existing exact high predicate before the four-sector forced filter. -/
def highAllowedC23WithEvenRightBool (j m : Nat) : Bool :=
  BB6.Agent27FastBool.fastHighAllowedFullBool j m &&
  decide (¬((j % 128 = 63 ∧ m % 128 = 82) ∨
            (j % 128 = 127 ∧ m % 128 = 18))) &&
  decide (¬(2 ≤ m ∧ j % 4 = 0 ∧ (j+7) % 32 = (3*m) % 32)) &&
  decide (¬(3 ≤ m ∧ m % 4 = 3 ∧ j % 8 = (m+3) % 8))

theorem highAllowedC23WithEvenRightBool_iff (j m : Nat) :
    highAllowedC23WithEvenRightBool j m = true ↔
      BB6.Agent19HighEvenRight.highAllowedC23WithEvenRight j m := by
  constructor
  · intro h
    simp only [highAllowedC23WithEvenRightBool, Bool.and_eq_true,
      decide_eq_true_eq] at h
    rcases h with ⟨hrest,hEvenRight⟩
    rcases hrest with ⟨hrest,hC23⟩
    rcases hrest with ⟨hFast,hC70⟩
    have hPhase : BB6.Agent24Phase.highAllowed j m :=
      (BB6.Agent27FastBool.fastHighAllowedFullBool_iff j m).mp hFast
    exact ⟨⟨⟨hPhase,hC70⟩,hC23⟩,hEvenRight⟩
  · intro h
    rcases h with ⟨hC23,hEvenRight⟩
    rcases hC23 with ⟨hC70,hC23⟩
    rcases hC70 with ⟨hPhase,hC70⟩
    have hFast : BB6.Agent27FastBool.fastHighAllowedFullBool j m = true :=
      (BB6.Agent27FastBool.fastHighAllowedFullBool_iff j m).mpr hPhase
    simp [highAllowedC23WithEvenRightBool,hFast,hC70,hC23,hEvenRight]

/-- A root-admitted target cannot be rejected by the source-exact full
    forced normalizer. This transfers its universal nonreachability theorem
    to the exact fixed-target root decision. -/
theorem rootDecision_forces_fullForced_not (j m : Nat)
    (hroot : BB6.Agent3ValSix.valSixMixedRootDecision
      (highTargetX j) (highTargetY j m) = true) :
    BB6.Agent3.fullForcedExcluded (highTargetX j) (highTargetY j m) = false := by
  cases h : BB6.Agent3.fullForcedExcluded (highTargetX j) (highTargetY j m) with
  | false => rfl
  | true =>
      have hreach : BB6.Agent3.CReach (highTargetX j) (highTargetY j m) :=
        (BB6.Agent3ValSix.valSixMixedRootDecision_iff _ _).mp hroot
      rcases hreach with ⟨n, hrun⟩
      exact False.elim
        (BB6.Agent3.fullForcedExcluded_sound (highTargetX j) (highTargetY j m) h n hrun)

/-- The four-sector full forced filter is adjoined to the strongest existing
    C70+C23+all-phase+even-right high residual without changing the exact
    blank-halting equivalence. -/
def highAllowedC23WithEvenRightFullForced (j m : Nat) : Prop :=
  BB6.Agent19HighEvenRight.highAllowedC23WithEvenRight j m ∧
  BB6.Agent3.fullForcedExcluded (highTargetX j) (highTargetY j m) = false

def highAllowedC23WithEvenRightFullForcedBool (j m : Nat) : Bool :=
  highAllowedC23WithEvenRightBool j m &&
  decide (BB6.Agent3.fullForcedExcluded (highTargetX j) (highTargetY j m) = false)

theorem highAllowedC23WithEvenRightFullForcedBool_iff (j m : Nat) :
    highAllowedC23WithEvenRightFullForcedBool j m = true ↔
      highAllowedC23WithEvenRightFullForced j m := by
  simp [highAllowedC23WithEvenRightFullForcedBool,
    highAllowedC23WithEvenRightFullForced,
    highAllowedC23WithEvenRightBool_iff]

theorem blank_halts_iff_c23_even_right_full_forced :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent20C70.lowAllowedC70 m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowedC23WithEvenRightFullForced j m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision (highTargetX j)
          (highTargetY j m)=true) := by
  rw [BB6.Agent19HighEvenRight.blank_halts_iff_c23_and_even_right]
  constructor
  · rintro (hlow | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl hlow
    · have hnot := rootDecision_forces_fullForced_not j m hroot
      exact Or.inr ⟨j,m,⟨hprior,hnot⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hprior,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hprior,hroot⟩

theorem blank_halts_iff_c23_even_right_full_forced_bool :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent20C70.lowAllowedC70 m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowedC23WithEvenRightFullForcedBool j m = true ∧
        BB6.Agent3ValSix.valSixMixedRootDecision (highTargetX j)
          (highTargetY j m)=true) := by
  rw [blank_halts_iff_c23_even_right_full_forced]
  constructor
  · rintro (hlow | ⟨j,m,hallowed,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,
        (highAllowedC23WithEvenRightFullForcedBool_iff j m).mpr hallowed,
        hroot⟩
  · rintro (hlow | ⟨j,m,hallowed,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,
        (highAllowedC23WithEvenRightFullForcedBool_iff j m).mp hallowed,
        hroot⟩

#print axioms rootDecision_forces_fullForced_not
#print axioms highAllowedC23WithEvenRightFullForcedBool_iff
#print axioms blank_halts_iff_c23_even_right_full_forced
#print axioms blank_halts_iff_c23_even_right_full_forced_bool

/-- Exact finite count of the additional source exclusions among the current
    C residual candidates. This is an experiment, not a universal theorem. -/
def highPairs (jMax mMax : Nat) : List (Nat × Nat) :=
  (List.range (mMax+1)).flatMap fun m =>
    (List.range (jMax+1)).map fun j => (j,m)

def compareFold (pairs : List (Nat × Nat)) :
    Nat × Nat × List (Nat × Nat) :=
  pairs.foldl (fun acc jm =>
    let (oldCount, removedCount, examples) := acc
    let (j,m) := jm
    if highAllowedC23WithEvenRightBool j m then
      if BB6.Agent3.fullForcedExcluded (highTargetX j) (highTargetY j m) then
        (oldCount+1, removedCount+1,
          if examples.length < 20 then examples ++ [jm] else examples)
      else
        (oldCount+1, removedCount, examples)
    else acc) (0,0,[])

def runComparison : IO Unit := do
  let jMax := 2000
  let mMax := 20
  let pairs := highPairs jMax mMax
  let (oldCount, removedCount, examples) := compareFold pairs
  IO.println "Machine C: four-sector full-forced residual refinement"
  IO.println s!"Existing C70+C23+all-phase+even-right high candidates: {oldCount}"
  IO.println s!"Additional candidates excluded by fullForcedExcluded: {removedCount}"
  IO.println s!"Remaining high candidates after full forced filter: {oldCount-removedCount}"
  IO.println s!"Search domain: j=0..{jMax}, m=0..{mMax}; pairs={pairs.length}"
  IO.println s!"First additional exclusions (j,m): {examples}"

#eval runComparison

end BB6.Agent3FullForcedResidual
