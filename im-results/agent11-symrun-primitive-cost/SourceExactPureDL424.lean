import SourceCostModel
import SourceExactF424Core

/-!
# Source-direct exact-cost DL mode for Cryptids F424.
Pending original-source Lean 4.36.0-rc2 CI; source one-step counts
are sourced from Agent42's exact primitive lemmas.
-/

set_option maxRecDepth 16384
set_option maxHeartbeats 0

open Mathlib Relation Nat Turing BusyBeaver
open BusyBeaver.RleStackEngine BusyBeaver.SymRunEngine
open BB6.Agent11.SourceCost

namespace BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution

theorem sourceElemDL_exact (L R : List SymTok) :
    ReachesIn target_tm (costElemDL true L R)
      ((evalSym target_tm) (.DL, L, R))
      ((evalSym target_tm) (stepElemDL L R)) := by
  cases L with
  | nil => rfl
  | cons t L1 =>
    cases t with
    | item x =>
      cases x with
      | zero => rfl
      | run d =>
        rcases d with _ | _ | _ | d
        · simpa only [costElemDL, stepElemDL, strictList_eq,
            evalSym, evalM, encSymL, encSymR_bumpSymR] using
              step_DL_run0_exact (encSymL L1) (encSymR R)
        · simpa only [costElemDL, stepElemDL, strictList_eq,
            evalSym, evalM, encSymL, encSymR, encSymR_bumpSymR] using
              step_DL_run1_exact (encSymL L1) (encSymR R)
        · cases R with
          | nil => rfl
          | cons rt R1 =>
            cases rt with
            | item it =>
              cases it with
              | zero => rfl
              | run d0 =>
                simpa only [costElemDL, stepElemDL, fcost, ite_true,
                  strictList_eq, evalSym, evalM, encSymL, encSymR,
                  encSymL_prependZeroSym] using
                    step_DL_run2_exact d0 (encSymL L1) (encSymR R1)
            | repB1 _ => rfl
            | rep2 _ => rfl
            | rep12 _ => rfl
        · rfl
    | repB1 _ => rfl
    | rep2 _ => rfl
    | rep12 _ => rfl

theorem sourcePureDL_exact (L R : List SymTok) :
    ReachesIn target_tm (costPureDL true L R)
      ((evalSym target_tm) (.DL, L, R))
      ((evalSym target_tm) (stepPureDL L R)) := by
  cases L with
  | nil => rfl
  | cons t L1 =>
    have heq : (evalSym target_tm) (.DL, t :: L1, R) =
        (evalSym target_tm) (.DL, peelPureTok t L1, R) := by
      simp only [evalSym, encSymL_peelPureTok]
    rw [heq]
    simpa only [costPureDL, stepPureDL] using
      sourceElemDL_exact (peelPureTok t L1) R

#print axioms sourceElemDL_exact
#print axioms sourcePureDL_exact

end BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution
