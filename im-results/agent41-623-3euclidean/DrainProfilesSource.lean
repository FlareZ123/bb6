import Agent41DrainProfiles
import Agent49FlatDrainSource

namespace BB6.Agent41DrainProfiles
open BB6.Agent49FlatDrainSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

def pairOf : HighLevelState → Nat × Nat
  | .D a d => (a,d)

def originalDrain (a b d : Nat) : Option (Nat × Nat) := (drainB a b d).map pairOf

theorem original_laws : Laws originalDrain where
  zero := by
    intro a d
    unfold originalDrain
    rw [drainB]
    rfl
  three := by
    intro a q d hq
    simp only [originalDrain,drain_three a q d hq]
  oneZero := by
    intro q d
    simp [originalDrain,drain_three_one_zero]
  oneSucc := by
    intro a q d
    simp only [originalDrain,drain_three_one (a+1) q d (by omega),Nat.add_sub_cancel]
  twoZero := by
    intro q d
    simp only [originalDrain,drain_three_two_zero]
  twoSucc := by
    intro a q d
    simp only [originalDrain,drain_three_two (a+1) q d (by omega),Nat.add_sub_cancel]

def profileDrain (a b d : Nat) : Option (Nat × Nat) := render (get (profiles b).mid a) a b d

theorem original_profile (a b d : Nat) : originalDrain a b d = profileDrain a b d :=
  drain_exact originalDrain original_laws a b d

theorem original_sharp_affine (b k : Nat) :
    AffineFrom originalDrain b k ↔ (profiles b).mid.front.length≤k :=
  sharp_affine_threshold originalDrain original_laws b k

/-- Same exact bundled right-even branch as Agent49's FatalDiagonalSource. -/
private theorem bundled (A a : Nat) :
    drainB A (a+1) 0 = (evalA A a (2*a+5)).bind fun p => drainB p.1 p.2.1 p.2.2 := by
  conv => lhs; rw [drainB]
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false, Nat.add_sub_cancel]
  have h : 0+2*(a+1)+3=2*a+5 := by omega
  rw [h]
  cases he : evalA A a (2*a+5) with
  | none => rfl
  | some p =>
    rcases p with ⟨a1,b1,d1⟩
    simp only [Option.bind_some]
    have hh := evalA_second_le A a (2*a+5) a1 b1 d1 he
    rw [if_pos (show b1<a+1 by omega)]

def sectionEval (a d : Nat) : Option (Nat × Nat) :=
  if a=0 then
    if d%2=1 then profileDrain (d+1) 2 2 else some (d,7)
  else if d%2=1 ∧ a≥d+5 then profileDrain (a-d-5) (d+3) 5
  else if d%2=0 ∧ a≥d+3 then profileDrain (a-d-2) (d+2) 2
  else if a%2=1 then none
  else if a=d+2 then profileDrain 0 a 2
  else if d%2=1 then profileDrain (d+4-a) (a-1) 3
  else profileDrain (d+1-a) (a+1) 0

/-- All input states, all successful outputs and all failures; no canonical
    sector or survival-budget assumption. -/
theorem section_exact (a d : Nat) :
    (highLevelNext (.D a d)).map pairOf = sectionEval a d := by
  unfold highLevelNext sectionEval
  by_cases h0 : a=0
  · simp only [if_pos h0]
    by_cases hd : d%2=1
    · simp only [if_pos hd]
      exact original_profile _ _ _
    · simp [hd,pairOf]
  · simp only [if_neg h0]
    by_cases h1 : d%2=1 ∧ a≥d+5
    · simp only [if_pos h1]
      exact original_profile _ _ _
    · simp only [if_neg h1]
      by_cases h2 : d%2=0 ∧ a≥d+3
      · simp only [if_pos h2]
        exact original_profile _ _ _
      · simp only [if_neg h2]
        by_cases h3 : a%2=1
        · simp [h3]
        · simp only [if_neg h3]
          by_cases h4 : a=d+2
          · simp only [if_pos h4]
            exact original_profile _ _ _
          · simp only [if_neg h4]
            by_cases h5 : d%2=1
            · simp only [if_pos h5]
              exact original_profile _ _ _
            · simp only [if_neg h5,←bundled]
              exact original_profile _ _ _

def profileRun : Nat → Option (Nat × Nat)
  | 0 => some (0,7)
  | n+1 => (profileRun n).bind fun p => sectionEval p.1 p.2

def sourceRun : Nat → Option HighLevelState
  | 0 => some (.D 0 7)
  | n+1 => (sourceRun n).bind highLevelNext

theorem root_run_exact (n : Nat) : (sourceRun n).map pairOf = profileRun n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sourceRun,profileRun,←ih]
    cases hg : sourceRun n with
    | none => rfl
    | some s =>
      cases s with
      | D a d => exact section_exact a d

#print axioms original_laws
#print axioms original_profile
#print axioms original_sharp_affine
#print axioms section_exact
#print axioms root_run_exact
end BB6.Agent41DrainProfiles
