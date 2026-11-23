import SourceCostModel
import SourceExactF424Core

/-!
F424 exact source pure CB-mode primitive cost, original Cryptids 3647718b5d.
Uses Agent42's direct original-machine exact witnesses.
This draft must pass source CI before being treated as a theorem.
-/

set_option maxRecDepth 16384
set_option maxHeartbeats 0

open Mathlib Relation Nat Turing BusyBeaver
open BusyBeaver.RleStackEngine BusyBeaver.SymRunEngine
open BB6.Agent11.SourceCost

namespace BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution

theorem sourceElemCBRun0_exact (L R1 : List SymTok) :
    ReachesIn target_tm (costElemCBRun0 true R1)
      ((evalSym target_tm) (.CB, L, .item (.run 0) :: R1))
      ((evalSym target_tm) (stepElemCB_run0 L R1)) := by
  cases R1 with
  | nil =>
    simpa only [costElemCBRun0, stepElemCB_run0, strictList_eq,
      evalSym, evalM, encSymL, encSymR, encSymL_bumpSymL] using
      step_CB_run0_nil_exact (encSymL L)
  | cons t R2 =>
    cases t with
    | item x =>
      cases x with
      | zero =>
        simpa only [costElemCBRun0, stepElemCB_run0, strictList_eq,
          evalSym, evalM, encSymL, encSymR, encSymL_bumpSymL] using
          step_CB_run0_zero_exact (encSymL L) (encSymR R2)
      | run d =>
        rcases d with _ | d
        · simpa only [costElemCBRun0, stepElemCB_run0, strictList_eq,
            evalSym, evalM, encSymL, encSymR, encSymL_bumpSymL,
            encSymL_prependZeroSym] using
            step_CB_run0_run0_exact (encSymL L) (encSymR R2)
        · simpa only [costElemCBRun0, fcost, ite_true, stepElemCB_run0,
            strictList_eq, evalSym, evalM, encSymL, encSymR,
            encSymL_bumpSymL, encSymL_prependZeroSym] using
            step_CB_run0_run_pos_exact d (encSymL L) (encSymR R2)
    | repB1 _ => rfl
    | rep2 _ => rfl
    | rep12 _ => rfl

theorem sourceElemCB_exact (L R : List SymTok) :
    ReachesIn target_tm (costElemCB true R)
      ((evalSym target_tm) (.CB, L, R))
      ((evalSym target_tm) (stepElemCB L R)) := by
  cases R with
  | nil =>
    simpa only [costElemCB, stepElemCB, strictList_eq, evalSym, evalM,
      encSymL_bumpSymL] using step_CB_nil_exact (encSymL L)
  | cons t R1 =>
    cases t with
    | item x =>
      cases x with
      | zero =>
        simpa only [costElemCB, stepElemCB, strictList_eq, evalSym, evalM,
          encSymL_bumpSymL, encSymR_bumpSymR] using
            step_CB_zero_exact (encSymL L) (encSymR R1)
      | run d =>
        rcases d with _ | _ | _ | d
        · simpa only [costElemCB, stepElemCB] using sourceElemCBRun0_exact L R1
        · simpa only [costElemCB, stepElemCB, strictList_eq, evalSym, evalM,
            encSymL, encSymR, encSymL_bumpSymL] using
              step_CB_run1_exact (encSymL L) (encSymR R1)
        · simpa only [costElemCB, stepElemCB, strictList_eq, evalSym, evalM,
            encSymL, encSymR, encSymL_bumpSymL] using
              step_CB_run2_exact (encSymL L) (encSymR R1)
        · simpa only [costElemCB, stepElemCB, strictList_eq, strictNat_eq,
            evalSym, evalM, encSymL, encSymR, encSymL_bumpSymL] using
              step_CB_run_ge3_exact d (encSymL L) (encSymR R1)
    | repB1 _ => rfl
    | rep2 _ => rfl
    | rep12 _ => rfl

theorem sourcePureCB_exact (L R : List SymTok) :
    ReachesIn target_tm (costPureCB true L R)
      ((evalSym target_tm) (.CB, L, R))
      ((evalSym target_tm) (stepPureCB L R)) := by
  cases R with
  | nil =>
    simpa only [costPureCB, stepPureCB] using sourceElemCB_exact L []
  | cons t R1 =>
    cases t with
    | item x =>
      cases x with
      | zero => simpa only [costPureCB, stepPureCB] using sourceElemCB_exact L (.item .zero :: R1)
      | run d =>
        rcases d with _ | _ | _ | d
        · simpa only [costPureCB, stepPureCB] using sourceElemCBRun0_exact L R1
        · simpa only [costPureCB, stepPureCB] using sourceElemCB_exact L (.item (.run 1) :: R1)
        · simpa only [costPureCB, stepPureCB] using sourceElemCB_exact L (.item (.run 2) :: R1)
        · simpa only [costPureCB, stepPureCB, evalSym, evalM, encSymL_bumpSymL] using
            step_CB_run_ge3_exact d (encSymL L) (encSymR R1)
    | repB1 k =>
      cases hs2 : stripPrefixSym [.item (.run 0), .item (.run 0), .item (.run 1)] L with
      | some L2 =>
        have hL := stripPrefixSym_some _ L L2 hs2
        rw [hL]
        simpa [costPureCB, stepPureCB, fcost, evalSym, evalM,
          encSymL, encSymR, List.cons_append, List.nil_append] using
          sweep_CB_B1_exact k (.run 0 :: .run 1 :: encSymL L2) (encSymR R1)
      | none =>
        cases hs1 : stripPrefixSym [.item (.run 0)] L with
        | some L1 =>
          have hL := stripPrefixSym_some _ L L1 hs1
          rw [hL]
          simpa [costPureCB, stepPureCB, fcost, evalSym, evalM,
            encSymL, encSymR, List.cons_append, List.nil_append] using
            sweep_CB_B1_exact k (encSymL L1) (encSymR R1)
        | none =>
          simp [costPureCB, stepPureCB, hs2, hs1]
    | rep2 p =>
      cases hs2 : stripPrefixSym [.item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1)] L with
      | some L2 =>
        have hL := stripPrefixSym_some _ L L2 hs2
        rw [hL]
        simpa [costPureCB, stepPureCB, fcost, evalSym, evalM,
          encSymL, encSymR, List.cons_append, List.nil_append] using
          sweep_CB_B2_exact p (.run 1 :: .run 0 :: .run 1 :: encSymL L2) (encSymR R1)
      | none =>
        cases hs1 : stripPrefixSym [.item (.run 0)] L with
        | some L1 =>
          have hL := stripPrefixSym_some _ L L1 hs1
          rw [hL]
          simpa [costPureCB, stepPureCB, fcost, evalSym, evalM,
            encSymL, encSymR, List.cons_append, List.nil_append] using
            sweep_CB_B2_exact p (encSymL L1) (encSymR R1)
        | none =>
          simp [costPureCB, stepPureCB, hs2, hs1]
    | rep12 m =>
      cases hs1 : stripPrefixSym [.item (.run 0)] L with
      | some L1 =>
        have hL := stripPrefixSym_some _ L L1 hs1
        rw [hL]
        simpa [costPureCB, stepPureCB, fcost, evalSym, evalM,
          encSymL, encSymR, List.cons_append, List.nil_append] using
          sweep_CB_B12R_exact m (encSymL L1) (encSymR R1)
      | none =>
        simp [costPureCB, stepPureCB, hs1]

#print axioms sourceElemCBRun0_exact
#print axioms sourceElemCB_exact
#print axioms sourcePureCB_exact

end BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution
