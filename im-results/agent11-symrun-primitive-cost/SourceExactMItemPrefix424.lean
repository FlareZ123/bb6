import SourceExactF424Core

/-!
# F424 exact primitive-cost lift for the initial MItem acceleration

This lifts the already source-checked mode-specific BB/DL/CB primitive
witnesses to the upstream MItem-level stepElemM transition used by
runElemFast. It is a draft until the exact import closure is Lean-compiled.
-/

set_option maxRecDepth 16384
set_option maxHeartbeats 0

open Mathlib Relation Nat Turing BusyBeaver
open BusyBeaver.RleStackEngine BusyBeaver.SymRunEngine

namespace BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution

abbrev MState := SymMode × List MItem × List MItem

/-- F424's exact primitive charge for one source MItem transition. -/
def costElemM424 : MState → Nat
  | (.BB, [], _) => 1
  | (.BB, .zero :: _, _) => 1
  | (.BB, .run 0 :: _, _) => 8
  | (.BB, .run 1 :: _, _) => 3
  | (.BB, .run 2 :: _, _) => 5
  | (.BB, .run 3 :: _, _) => 9
  | (.BB, .run (_ + 4) :: _, _) => 9
  | (.DL, .zero :: _, _) => 0
  | (.DL, .run 0 :: _, _) => 1
  | (.DL, .run 1 :: _, _) => 3
  | (.DL, .run 2 :: _, .run d0 :: _) => 3 * d0 + 22
  | (.CB, _, []) => 2
  | (.CB, _, .zero :: _) => 2
  | (.CB, _, .run 0 :: []) => 3
  | (.CB, _, .run 0 :: .zero :: _) => 3
  | (.CB, _, .run 0 :: .run 0 :: _) => 6
  | (.CB, _, .run 0 :: .run (d2 + 1) :: _) => 3 * d2 + 21
  | (.CB, _, .run 1 :: _) => 3
  | (.CB, _, .run 2 :: _) => 5
  | (.CB, _, .run (_ + 3) :: _) => 5
  | _ => 0

/-- Every MItem-level stepElemM branch is an exact original-TM run.
    The only zero-cost branches are stutters or the symbolic HALT marker,
    whose evalM image is the already-halting DL configuration. -/
theorem sourceElemM424_exact (s : MState) :
    ReachesIn target_tm (costElemM424 s)
      (evalM target_tm s)
      (evalM target_tm (stepElemM s)) := by
  rcases s with ⟨mode, L, R⟩
  cases mode with
  | BB =>
    cases L with
    | nil =>
      simpa [costElemM424, stepElemM, strictMList_eq, evalM] using
        step_BB_nil_exact R
    | cons t L1 =>
      cases t with
      | zero =>
        simpa [costElemM424, stepElemM, strictMList_eq, evalM] using
          step_BB_zero_exact L1 R
      | run d =>
        rcases d with _ | _ | _ | _ | d
        · simpa [costElemM424, stepElemM, strictMList_eq, strictNat_eq, evalM] using
            step_BB_run0_exact L1 R
        · simpa [costElemM424, stepElemM, strictMList_eq, strictNat_eq, evalM] using
            step_BB_run1_exact L1 R
        · simpa [costElemM424, stepElemM, strictMList_eq, strictNat_eq, evalM] using
            step_BB_run2_exact L1 R
        · simpa [costElemM424, stepElemM, strictMList_eq, strictNat_eq, evalM] using
            step_BB_run3_exact L1 R
        · simpa [costElemM424, stepElemM, strictMList_eq, strictNat_eq, evalM] using
            step_BB_run_ge4_exact d L1 R
  | DL =>
    cases L with
    | nil => rfl
    | cons t L1 =>
      cases t with
      | zero => rfl
      | run d =>
        rcases d with _ | _ | _ | d
        · simpa [costElemM424, stepElemM, strictMList_eq, strictNat_eq, evalM] using
            step_DL_run0_exact L1 R
        · simpa [costElemM424, stepElemM, strictMList_eq, strictNat_eq, evalM] using
            step_DL_run1_exact L1 R
        · cases R with
          | nil => rfl
          | cons rt R1 =>
            cases rt with
            | zero => rfl
            | run d0 =>
              simpa [costElemM424, stepElemM, strictMList_eq, strictNat_eq,
                prependZeroM_eq, evalM] using
                step_DL_run2_exact d0 L1 R1
        · rfl
  | CB =>
    cases R with
    | nil =>
      simpa [costElemM424, stepElemM, strictMList_eq, evalM] using
        step_CB_nil_exact L
    | cons t R1 =>
      cases t with
      | zero =>
        simpa [costElemM424, stepElemM, strictMList_eq, evalM] using
          step_CB_zero_exact L R1
      | run d =>
        rcases d with _ | _ | _ | d
        · cases R1 with
          | nil =>
            simpa [costElemM424, stepElemM, strictMList_eq, evalM] using
              step_CB_run0_nil_exact L
          | cons t2 R2 =>
            cases t2 with
            | zero =>
              simpa [costElemM424, stepElemM, strictMList_eq, evalM] using
                step_CB_run0_zero_exact L R2
            | run d2 =>
              rcases d2 with _ | d2
              · simpa [costElemM424, stepElemM, strictMList_eq, evalM] using
                  step_CB_run0_run0_exact L R2
              · simpa [costElemM424, stepElemM, strictMList_eq, strictNat_eq,
                  prependZeroM_eq, evalM] using
                  step_CB_run0_run_pos_exact d2 L R2
        · simpa [costElemM424, stepElemM, strictMList_eq, strictNat_eq, evalM] using
            step_CB_run1_exact L R1
        · simpa [costElemM424, stepElemM, strictMList_eq, strictNat_eq, evalM] using
            step_CB_run2_exact L R1
        · simpa [costElemM424, stepElemM, strictMList_eq, strictNat_eq, evalM] using
            step_CB_run_ge3_exact d L R1
  | HALT => rfl

/-- Exact primitive cost of n successive source stepElemM transitions. -/
def costIterM424 : Nat → MState → Nat
  | 0, _ => 0
  | n + 1, s => costElemM424 s + costIterM424 n (stepElemM s)

theorem costIterM424_exact_reaches (n : Nat) (s : MState) :
    multiStep target_tm (evalM target_tm s) (costIterM424 n s) =
      some (evalM target_tm (iterStep stepElemM n s)) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    change multiStep target_tm (evalM target_tm s)
      (costElemM424 s + costIterM424 n (stepElemM s)) =
        some (evalM target_tm (iterStep stepElemM n (stepElemM s)))
    exact multiStep_trans (sourceElemM424_exact s) (ih (stepElemM s))

#print axioms sourceElemM424_exact
#print axioms costIterM424_exact_reaches

end BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution
