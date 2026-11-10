import NeedleGrowthRoot
import Lean.Elab.Tactic.Omega

namespace BB6.Agent20.SpaceNeedleGrowthScan
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle
open BB6.Agent20.SpaceNeedleGrowth

/-- A single-pass finite high-level trajectory from a supplied state. -/
def runFrom (st : Option HighLevelState) : Nat → Option HighLevelState
  | 0 => st
  | n+1 => (runFrom st n).bind highLevelNext

private theorem runFrom_shift (st : Option HighLevelState) (n : Nat) :
    runFrom (st.bind highLevelNext) n = runFrom st (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (runFrom (st.bind highLevelNext) n).bind highLevelNext =
        (runFrom st (n+1)).bind highLevelNext
      rw [ih]

private theorem runFrom_iter (st : Option HighLevelState) (n : Nat) :
    runFrom st n = Nat.iterate
      (fun z : Option HighLevelState => z.bind highLevelNext) n st := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (runFrom st n).bind highLevelNext = _
      rw [ih]
      rw [Nat.add_comm n 1, Function.iterate_add_apply]
      rfl

private def isTarget (d : Nat) : Option HighLevelState → Bool
  | none => false
  | some (.N e) => decide (e=d)

private theorem isTarget_spec (d : Nat) (st : Option HighLevelState) :
    isTarget d st = true ↔ st=some (.N d) := by
  cases st with
  | none => simp [isTarget]
  | some s =>
      cases s with
      | N e => simp [isTarget]

/-- The search makes one forward transition per unsuccessful checked state. -/
def scan (d : Nat) : Nat → Option HighLevelState → Bool
  | 0, _ => false
  | fuel+1, st => isTarget d st || scan d fuel (st.bind highLevelNext)

/-- Exact characterisation of a single-pass forward scan. -/
theorem scan_spec (d fuel : Nat) (st : Option HighLevelState) :
    scan d fuel st = true ↔
      ∃ i, i < fuel ∧ runFrom st i = some (.N d) := by
  induction fuel generalizing st with
  | zero => simp [scan]
  | succ fuel ih =>
      change (isTarget d st || scan d fuel (st.bind highLevelNext)) = true ↔ _
      rw [Bool.or_eq_true, isTarget_spec, ih]
      constructor
      · intro h
        rcases h with hnow | ⟨i,hi,he⟩
        · exact ⟨0,by omega,by simpa [runFrom] using hnow⟩
        · refine ⟨i+1,by omega,?_⟩
          rw [←runFrom_shift]
          exact he
      · rintro ⟨i,hi,he⟩
        cases i with
        | zero =>
            left
            simpa [runFrom] using he
        | succ i =>
            right
            refine ⟨i,by omega,?_⟩
            rw [runFrom_shift]
            exact he

/-- An exact executable Boolean decision for any prescribed authentic
    Space Needle blank-root counter using O(d/log d) high-level transitions
    and a single pass without retaining earlier states. -/
def optimizedScan (d : Nat) : Bool :=
  scan d (optimizedFuel d) (some highLevelStart)

theorem optimizedScan_spec (d : Nat) :
    optimizedScan d = true ↔ ReachN d := by
  rw [optimizedScan, scan_spec]
  constructor
  · rintro ⟨n,hn,htarget⟩
    refine ⟨n,?_⟩
    rw [←runFrom_iter]
    exact htarget
  · rintro ⟨n,hn⟩
    refine ⟨n,?_,?_⟩
    · have hb := original_iterate_time_upper d n (Nat.log2 (d+2)/2) hn
      rcases hb with hsmall | hlarge
      · exact Nat.lt_of_lt_of_le hsmall (Nat.le_max_left _ _)
      · have hh : n < 2*((d+2)/((Nat.log2 (d+2)/2)+2))+2 := by omega
        exact Nat.lt_of_lt_of_le hh (Nat.le_max_right _ _)
    · rw [runFrom_iter]
      exact hn

#print axioms BB6.Agent20.SpaceNeedleGrowthScan.scan_spec
#print axioms BB6.Agent20.SpaceNeedleGrowthScan.optimizedScan_spec
end BB6.Agent20.SpaceNeedleGrowthScan
