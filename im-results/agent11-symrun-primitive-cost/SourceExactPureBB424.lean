import SourceCostModel
import SourceExactF424Core

/-!
# F424 exact original-machine primitive cost of source `stepPureBB`

This is the first of three mode-specific discharged original-source exact cost
obligations (BB, DL, CB). Imports the previously independent Agent42 exact
primitive witnesses, now isolated as `SourceExactF424Core.lean`. This file
must be compiled by Lean 4.36.0-rc2 original-source CI before any claim
of formal exact machine time.
-/

set_option maxRecDepth 16384
set_option maxHeartbeats 0

open Mathlib Relation Nat Turing BusyBeaver
open BusyBeaver.RleStackEngine BusyBeaver.SymRunEngine
open BB6.Agent11.SourceCost

namespace BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution

/-- Exact source `stepElemBB` primitive cost, including inert symbolic tokens. -/
theorem sourceElemBB_exact (L R : List SymTok) :
    ReachesIn target_tm (costElemBB true L)
      ((evalSym target_tm) (.BB, L, R))
      ((evalSym target_tm) (stepElemBB L R)) := by
  cases L with
  | nil =>
    simpa only [costElemBB, stepElemBB, strictList_eq, evalSym, evalM, encSymL,
      encSymR_bumpSymR] using step_BB_nil_exact (encSymR R)
  | cons t L1 =>
    cases t with
    | item x =>
      cases x with
      | zero =>
        simpa only [costElemBB, stepElemBB, strictList_eq, evalSym, evalM, encSymL,
          encSymR_bumpSymR] using step_BB_zero_exact (encSymL L1) (encSymR R)
      | run d =>
        rcases d with _ | _ | _ | _ | d
        · simpa only [costElemBB, fcost, ite_true, stepElemBB, strictList_eq,
            strictNat_eq, evalSym, evalM, encSymL, encSymR,
            encSymR_bumpSymR] using step_BB_run0_exact (encSymL L1) (encSymR R)
        · simpa only [costElemBB, stepElemBB, strictList_eq, strictNat_eq,
            evalSym, evalM, encSymL, encSymR, encSymR_bumpSymR]
            using step_BB_run1_exact (encSymL L1) (encSymR R)
        · simpa only [costElemBB, stepElemBB, strictList_eq, strictNat_eq,
            evalSym, evalM, encSymL, encSymR, encSymR_bumpSymR]
            using step_BB_run2_exact (encSymL L1) (encSymR R)
        · simpa only [costElemBB, stepElemBB, strictList_eq, strictNat_eq,
            evalSym, evalM, encSymL, encSymR, encSymR_bumpSymR]
            using step_BB_run3_exact (encSymL L1) (encSymR R)
        · simpa only [costElemBB, stepElemBB, strictList_eq, strictNat_eq,
            evalSym, evalM, encSymL, encSymR, encSymR_bumpSymR]
            using step_BB_run_ge4_exact d (encSymL L1) (encSymR R)
    | repB1 _ => rfl
    | rep2 _ => rfl
    | rep12 _ => rfl

/-- Exact source `stepPureBB` cost, including all three repeated-block
    sweeps and the representation-preserving peeling fallback. -/
theorem sourcePureBB_exact (L R : List SymTok) :
    ReachesIn target_tm (costPureBB true L R)
      ((evalSym target_tm) (.BB, L, R))
      ((evalSym target_tm) (stepPureBB L R)) := by
  cases L with
  | nil =>
    simpa only [costPureBB, stepPureBB] using sourceElemBB_exact [] R
  | cons t L1 =>
    cases t with
    | item x =>
      simpa only [costPureBB, stepPureBB] using sourceElemBB_exact (.item x :: L1) R
    | repB1 k =>
      simpa only [costPureBB, stepPureBB, fcost, ite_true, evalSym, evalM,
        encSymL, encSymR, List.cons_append, List.nil_append]
        using sweep_BB_B1_exact k (encSymL L1) (encSymR R)
    | rep2 p =>
      simp only [costPureBB, stepPureBB]
      cases hs : stripPrefixSym [.item (.run 0), .item (.run 1)] R with
      | some R2 =>
        have hR := stripPrefixSym_some _ R R2 hs
        rw [hR]
        simp only [fcost, ite_true, evalSym, evalM, encSymL, encSymR,
          List.cons_append, List.nil_append]
        exact sweep_BB_C2_exact p (encSymL L1) (encSymR R2)
      | none =>
        have heq : (evalSym target_tm) (.BB, .rep2 p :: L1, R) =
            (evalSym target_tm) (.BB, peelPureTok (.rep2 p) L1, R) := by
          simp only [evalSym, encSymL_peelPureTok]
        rw [heq]
        exact sourceElemBB_exact (peelPureTok (.rep2 p) L1) R
    | rep12 m =>
      simp only [costPureBB, stepPureBB]
      cases hs : stripPrefixSym [.item (.run 0), .item (.run 1)] R with
      | some R2 =>
        have hR := stripPrefixSym_some _ R R2 hs
        rw [hR]
        simp only [fcost, ite_true, evalSym, evalM, encSymL, encSymR,
          List.cons_append, List.nil_append]
        exact sweep_BB_C12_exact m (encSymL L1) (encSymR R2)
      | none =>
        have heq : (evalSym target_tm) (.BB, .rep12 m :: L1, R) =
            (evalSym target_tm) (.BB, peelPureTok (.rep12 m) L1, R) := by
          simp only [evalSym, encSymL_peelPureTok]
        rw [heq]
        exact sourceElemBB_exact (peelPureTok (.rep12 m) L1) R

#print axioms sourceElemBB_exact
#print axioms sourcePureBB_exact

end BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution
