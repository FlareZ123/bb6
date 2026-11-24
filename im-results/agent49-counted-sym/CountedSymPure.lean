module
public import SourceCostModel
public import BusyBeaver.Calculi.HaltShared

@[expose] public section

/-!
A machine-independent counted counterpart of the upstream HasSymRunRules
interface. The 19 assumptions are exact primitive witnesses, not mere
halting equivalences. The single pure-step theorem below serves both
F412 (flag=false) and F424 (flag=true). Proof structure adapted from
Agent26's F412CountedPure and the original HaltShared proofs; the abstract
machine parameter prevents accidental dependence on one machine's states.
This is a draft until original-source Lean CI accepts it.
-/
open Mathlib Relation Nat Turing BusyBeaver
open BusyBeaver.RleStackEngine BusyBeaver.SymRunEngine
open BB6.Agent11.SourceCost

namespace BB6.Agent49.CountedSym

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

structure CountedAtoms (target_tm : Machine (Fin 2) (Fin 6)) (flag : Bool) : Prop where
  step_BB_nil_exact (R : List MItem) :
    ReachesIn target_tm 1 (cfgBB target_tm [] R) (cfgCB target_tm [] (bumpM R))
  step_BB_zero_exact (L1 R : List MItem) :
    ReachesIn target_tm 1 (cfgBB target_tm (.zero :: L1) R) (cfgCB target_tm L1 (bumpM R))
  step_BB_run0_exact (L1 R : List MItem) :
    ReachesIn target_tm (fcost flag 8 6) (cfgBB target_tm (.run 0 :: L1) R) (cfgBB target_tm L1 (.run 0 :: R))
  step_BB_run1_exact (L1 R : List MItem) :
    ReachesIn target_tm 3 (cfgBB target_tm (.run 1 :: L1) R) (cfgBB target_tm L1 (.run 0 :: bumpM R))
  step_BB_run2_exact (L1 R : List MItem) :
    ReachesIn target_tm 5 (cfgBB target_tm (.run 2 :: L1) R) (cfgDL target_tm L1 (.run 0 :: .run 0 :: bumpM R))
  step_BB_run3_exact (L1 R : List MItem) :
    ReachesIn target_tm 9 (cfgBB target_tm (.run 3 :: L1) R) (cfgBB target_tm (.run 0 :: .zero :: .zero :: L1) (bumpM R))
  step_BB_run_ge4_exact (d : Nat) (L1 R : List MItem) :
    ReachesIn target_tm 9 (cfgBB target_tm (.run (d + 4) :: L1) R) (cfgBB target_tm (.run 0 :: .zero :: .run d :: L1) (bumpM R))
  step_DL_run0_exact (L1 R : List MItem) :
    ReachesIn target_tm 1 (cfgDL target_tm (.run 0 :: L1) R) (cfgBB target_tm L1 (bumpM R))
  step_DL_run1_exact (L1 R : List MItem) :
    ReachesIn target_tm 3 (cfgDL target_tm (.run 1 :: L1) R) (cfgDL target_tm L1 (.run 0 :: bumpM R))
  step_DL_run2_exact (d0 : Nat) (L1 R1 : List MItem) :
    ReachesIn target_tm (3*d0 + fcost flag 22 20)
      (cfgDL target_tm (.run 2 :: L1) (.run d0 :: R1))
      (cfgCB target_tm (.run 0 :: .run 0 :: List.replicate (d0 + 1) .zero ++ L1) R1)
  step_CB_nil_exact (L : List MItem) :
    ReachesIn target_tm 2 (cfgCB target_tm L []) (cfgDL target_tm (bumpM L) [.run 0])
  step_CB_zero_exact (L R1 : List MItem) :
    ReachesIn target_tm 2 (cfgCB target_tm L (.zero :: R1)) (cfgDL target_tm (bumpM L) (bumpM R1))
  step_CB_run0_nil_exact (L : List MItem) :
    ReachesIn target_tm 3 (cfgCB target_tm L [.run 0]) (cfgBB target_tm (.run 0 :: bumpM L) [])
  step_CB_run0_zero_exact (L R2 : List MItem) :
    ReachesIn target_tm 3 (cfgCB target_tm L (.run 0 :: .zero :: R2)) (cfgBB target_tm (.run 0 :: bumpM L) R2)
  step_CB_run0_run0_exact (L R2 : List MItem) :
    ReachesIn target_tm 6 (cfgCB target_tm L (.run 0 :: .run 0 :: R2)) (cfgBB target_tm (.run 0 :: .zero :: bumpM L) R2)
  step_CB_run0_run_pos_exact (d2 : Nat) (L R2 : List MItem) :
    ReachesIn target_tm (3*d2 + fcost flag 21 19)
      (cfgCB target_tm L (.run 0 :: .run (d2+1) :: R2))
      (cfgCB target_tm (.run 0 :: .run 0 :: List.replicate d2 .zero ++ bumpM L) R2)
  step_CB_run1_exact (L R1 : List MItem) :
    ReachesIn target_tm 3 (cfgCB target_tm L (.run 1 :: R1)) (cfgCB target_tm (.run 0 :: bumpM L) R1)
  step_CB_run2_exact (L R1 : List MItem) :
    ReachesIn target_tm 5 (cfgCB target_tm L (.run 2 :: R1)) (cfgBB target_tm (bumpM L) (.run 0 :: .zero :: R1))
  step_CB_run_ge3_exact (d : Nat) (L R1 : List MItem) :
    ReachesIn target_tm 5 (cfgCB target_tm L (.run (d+3) :: R1)) (cfgBB target_tm (bumpM L) (.run 0 :: .run d :: R1))

namespace CountedAtoms

variable {target_tm : Machine (Fin 2) (Fin 6)} {flag : Bool}
variable (rules : CountedAtoms target_tm flag)
include rules

theorem step_BB_r0_r1_exact (L R : List MItem) :
    ReachesIn target_tm (fcost flag 11 9)
      (cfgBB target_tm (.run 0 :: .run 1 :: L) R)
      (cfgBB target_tm L (.run 0 :: .run 1 :: R)) := by
  have h1 := rules.step_BB_run0_exact (.run 1 :: L) R
  have h2 := rules.step_BB_run1_exact L (.run 0 :: R)
  have hc : fcost flag 8 6 + 3 = fcost flag 11 9 := by cases flag <;> rfl
  rw [← hc]
  simpa only [bumpM] using ReachesIn.trans h1 h2


theorem step_BB_r1_r0_r1_comm_exact (L R : List MItem) :
    ReachesIn target_tm (fcost flag 14 12)
      (cfgBB target_tm (.run 1 :: .run 0 :: .run 1 :: L) (.run 0 :: .run 1 :: R))
      (cfgBB target_tm L
        (.run 0 :: .run 1 :: .run 0 :: .run 1 :: .run 1 :: R)) := by
  have h1 := rules.step_BB_run1_exact (.run 0 :: .run 1 :: L) (.run 0 :: .run 1 :: R)
  have h1' :
      ReachesIn target_tm 3
        (cfgBB target_tm (.run 1 :: .run 0 :: .run 1 :: L) (.run 0 :: .run 1 :: R))
        (cfgBB target_tm (.run 0 :: .run 1 :: L)
          (.run 0 :: .run 1 :: .run 1 :: R)) := by
    simpa only [bumpM] using h1
  have h2 := rules.step_BB_run0_exact (.run 1 :: L) (.run 0 :: .run 1 :: .run 1 :: R)
  have h3 := rules.step_BB_run1_exact L (.run 0 :: .run 0 :: .run 1 :: .run 1 :: R)
  have h3' :
      ReachesIn target_tm 3
        (cfgBB target_tm (.run 1 :: L) (.run 0 :: .run 0 :: .run 1 :: .run 1 :: R))
        (cfgBB target_tm L
          (.run 0 :: .run 1 :: .run 0 :: .run 1 :: .run 1 :: R)) := by
    simpa only [bumpM] using h3
  have hc : 3 + fcost flag 8 6 + 3 = fcost flag 14 12 := by cases flag <;> rfl
  rw [← hc]
  exact ReachesIn.trans (ReachesIn.trans h1' h2) h3'


theorem sweep_BB_B1_exact (k : Nat) (L R : List MItem) :
    ReachesIn target_tm (fcost flag 11 9 * k)
      (cfgBB target_tm (repBlock [.run 0, .run 1] k ++ L) R)
      (cfgBB target_tm L (repBlock [.run 0, .run 1] k ++ R)) := by
  induction k generalizing R with
  | zero =>
      change multiStep target_tm _ 0 = some _
      simp only [BusyBeaver.multiStep_zero]
      rfl
  | succ k ih =>
    have h_eq : repBlock [.run 0, .run 1] (k + 1) ++ R =
        repBlock [.run 0, .run 1] k ++ (.run 0 :: .run 1 :: R) := by
      rw [repBlock_succ_right, List.append_assoc]
      rfl
    rw [h_eq]
    have h1 := rules.step_BB_r0_r1_exact (repBlock [.run 0, .run 1] k ++ L) R
    have h2 := ih (.run 0 :: .run 1 :: R)
    convert ReachesIn.trans h1 h2 using 1
    all_goals (try simp [repBlock, repBlock_succ_right, List.append_assoc, List.cons_append, List.nil_append])
    all_goals (cases flag <;> simp only [fcost, Bool.false_eq_true, ite_false, ite_true] at * <;> omega)


theorem sweep_BB_C2_exact (p : Nat) (L R : List MItem) :
    ReachesIn target_tm (fcost flag 14 12 * p)
      (cfgBB target_tm (repBlock [.run 1, .run 0, .run 1] p ++ L)
        (.run 0 :: .run 1 :: R))
      (cfgBB target_tm L
        (.run 0 :: .run 1 :: repBlock [.run 0, .run 1, .run 1] p ++ R)) := by
  induction p generalizing R with
  | zero =>
      change multiStep target_tm _ 0 = some _
      simp only [BusyBeaver.multiStep_zero]
      rfl
  | succ p ih =>
    have h_eq :
        (.run 0 :: .run 1 :: repBlock [.run 0, .run 1, .run 1] (p + 1) ++ R) =
        (.run 0 :: .run 1 :: repBlock [.run 0, .run 1, .run 1] p ++
          (.run 0 :: .run 1 :: .run 1 :: R)) := by
      simp only [repBlock_succ_right, List.cons_append, List.nil_append, List.append_assoc]
    rw [h_eq]
    have h1 := rules.step_BB_r1_r0_r1_comm_exact (repBlock [.run 1, .run 0, .run 1] p ++ L) R
    have h2 := ih (.run 0 :: .run 1 :: .run 1 :: R)
    convert ReachesIn.trans h1 h2 using 1
    all_goals (try simp [repBlock, repBlock_succ_right, List.append_assoc, List.cons_append, List.nil_append])
    all_goals (cases flag <;> simp only [fcost, Bool.false_eq_true, ite_false, ite_true] at * <;> omega)


theorem sweep_BB_C12_exact (m : Nat) (L R : List MItem) :
    ReachesIn target_tm (fcost flag 25 21 * m)
      (cfgBB target_tm
        (repBlock [.run 1, .run 0, .run 1, .run 0, .run 1] m ++ L)
        (.run 0 :: .run 1 :: R))
      (cfgBB target_tm L
        (.run 0 :: .run 1 ::
          repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R)) := by
  induction m generalizing R with
  | zero =>
      change multiStep target_tm _ 0 = some _
      simp only [BusyBeaver.multiStep_zero]
      rfl
  | succ m ih =>
    have h_eq :
        (.run 0 :: .run 1 ::
          repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] (m + 1) ++ R) =
        (.run 0 :: .run 1 ::
          repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++
          (.run 0 :: .run 1 :: .run 0 :: .run 1 :: .run 1 :: R)) := by
      simp only [repBlock_succ_right, List.cons_append, List.nil_append, List.append_assoc]
    rw [h_eq]
    have h1 := rules.step_BB_r1_r0_r1_comm_exact
      (.run 0 :: .run 1 ::
        (repBlock [.run 1, .run 0, .run 1, .run 0, .run 1] m ++ L)) R
    have h2 := rules.step_BB_r0_r1_exact
      (repBlock [.run 1, .run 0, .run 1, .run 0, .run 1] m ++ L)
      (.run 0 :: .run 1 :: .run 0 :: .run 1 :: .run 1 :: R)
    have h3 := ih (.run 0 :: .run 1 :: .run 0 :: .run 1 :: .run 1 :: R)
    have h12 := ReachesIn.trans h1 h2
    convert ReachesIn.trans h12 h3 using 1
    all_goals (try simp [repBlock, repBlock_succ_right, List.append_assoc, List.cons_append, List.nil_append])
    all_goals (cases flag <;> simp only [fcost, Bool.false_eq_true, ite_false, ite_true] at * <;> omega)


theorem sweep_CB_B1_exact (k : Nat) (L R : List MItem) :
    ReachesIn target_tm (fcost flag 21 19 * k)
      (cfgCB target_tm (.run 0 :: L)
        (repBlock [.run 0, .run 1] k ++ R))
      (cfgCB target_tm (.run 0 :: repBlock [.run 0, .run 1] k ++ L) R) := by
  induction k generalizing L with
  | zero =>
      change multiStep target_tm _ 0 = some _
      simp only [BusyBeaver.multiStep_zero]
      rfl
  | succ k ih =>
    have h_eq :
        (.run 0 :: repBlock [.run 0, .run 1] (k + 1) ++ L) =
        (.run 0 :: repBlock [.run 0, .run 1] k ++ (.run 0 :: .run 1 :: L)) := by
      simp only [repBlock_succ_right, List.cons_append, List.nil_append, List.append_assoc]
    rw [h_eq]
    have h1 : ReachesIn target_tm (fcost flag 21 19)
        (cfgCB target_tm (.run 0 :: L)
          (.run 0 :: .run 1 :: repBlock [.run 0, .run 1] k ++ R))
        (cfgCB target_tm (.run 0 :: .run 0 :: .run 1 :: L)
          (repBlock [.run 0, .run 1] k ++ R)) := by
      simpa only [bumpM] using
        rules.step_CB_run0_run_pos_exact 0 (.run 0 :: L)
          (repBlock [.run 0, .run 1] k ++ R)
    have h2 := ih (.run 0 :: .run 1 :: L)
    convert ReachesIn.trans h1 h2 using 1
    all_goals (try simp [repBlock, repBlock_succ_right, List.append_assoc, List.cons_append, List.nil_append])
    all_goals (cases flag <;> simp only [fcost, Bool.false_eq_true, ite_false, ite_true] at * <;> omega)


theorem sweep_CB_B2_exact (p : Nat) (L R : List MItem) :
    ReachesIn target_tm (fcost flag 24 22 * p)
      (cfgCB target_tm (.run 0 :: L)
        (repBlock [.run 0, .run 1, .run 1] p ++ R))
      (cfgCB target_tm
        (.run 0 :: repBlock [.run 1, .run 0, .run 1] p ++ L) R) := by
  induction p generalizing L with
  | zero =>
      change multiStep target_tm _ 0 = some _
      simp only [BusyBeaver.multiStep_zero]
      rfl
  | succ p ih =>
    have h_eq :
        (.run 0 :: repBlock [.run 1, .run 0, .run 1] (p + 1) ++ L) =
        (.run 0 :: repBlock [.run 1, .run 0, .run 1] p ++
          (.run 1 :: .run 0 :: .run 1 :: L)) := by
      simp only [repBlock_succ_right, List.cons_append, List.nil_append, List.append_assoc]
    rw [h_eq]
    have h1 :
        ReachesIn target_tm (fcost flag 21 19)
          (cfgCB target_tm (.run 0 :: L)
            (.run 0 :: .run 1 :: .run 1 ::
              (repBlock [.run 0, .run 1, .run 1] p ++ R)))
          (cfgCB target_tm (.run 0 :: .run 0 :: .run 1 :: L)
            (.run 1 :: (repBlock [.run 0, .run 1, .run 1] p ++ R))) := by
      simpa only [bumpM] using
        rules.step_CB_run0_run_pos_exact 0 (.run 0 :: L)
          (.run 1 :: (repBlock [.run 0, .run 1, .run 1] p ++ R))
    have h2 :
        ReachesIn target_tm 3
          (cfgCB target_tm (.run 0 :: .run 0 :: .run 1 :: L)
            (.run 1 :: (repBlock [.run 0, .run 1, .run 1] p ++ R)))
          (cfgCB target_tm (.run 0 :: .run 1 :: .run 0 :: .run 1 :: L)
            (repBlock [.run 0, .run 1, .run 1] p ++ R)) := by
      simpa only [bumpM] using
        rules.step_CB_run1_exact (.run 0 :: .run 0 :: .run 1 :: L)
          (repBlock [.run 0, .run 1, .run 1] p ++ R)
    have h3 := ih (.run 1 :: .run 0 :: .run 1 :: L)
    have h12 := ReachesIn.trans h1 h2
    convert ReachesIn.trans h12 h3 using 1
    all_goals (try simp [repBlock, repBlock_succ_right, List.append_assoc, List.cons_append, List.nil_append])
    all_goals (cases flag <;> simp only [fcost, Bool.false_eq_true, ite_false, ite_true] at * <;> omega)


theorem sweep_CB_B12R_exact (m : Nat) (L R : List MItem) :
    ReachesIn target_tm (fcost flag 45 41 * m)
      (cfgCB target_tm (.run 0 :: L)
        (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R))
      (cfgCB target_tm
        (.run 0 :: repBlock [.run 1, .run 0, .run 1, .run 0, .run 1] m ++ L) R) := by
  induction m generalizing L with
  | zero =>
      change multiStep target_tm _ 0 = some _
      simp only [BusyBeaver.multiStep_zero]
      rfl
  | succ m ih =>
    have h_eq :
        (.run 0 :: repBlock [.run 1, .run 0, .run 1, .run 0, .run 1] (m + 1) ++ L) =
        (.run 0 :: repBlock [.run 1, .run 0, .run 1, .run 0, .run 1] m ++
          (.run 1 :: .run 0 :: .run 1 :: .run 0 :: .run 1 :: L)) := by
      simp only [repBlock_succ_right, List.cons_append, List.nil_append, List.append_assoc]
    rw [h_eq]
    have h1 :
        ReachesIn target_tm (fcost flag 21 19)
          (cfgCB target_tm (.run 0 :: L)
            (.run 0 :: .run 1 :: .run 0 :: .run 1 :: .run 1 ::
              (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R)))
          (cfgCB target_tm (.run 0 :: .run 0 :: .run 1 :: L)
            (.run 0 :: .run 1 :: .run 1 ::
              (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R))) := by
      simpa only [bumpM] using
        rules.step_CB_run0_run_pos_exact 0 (.run 0 :: L)
          (.run 0 :: .run 1 :: .run 1 ::
            (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R))
    have h2 :
        ReachesIn target_tm (fcost flag 21 19)
          (cfgCB target_tm (.run 0 :: .run 0 :: .run 1 :: L)
            (.run 0 :: .run 1 :: .run 1 ::
              (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R)))
          (cfgCB target_tm (.run 0 :: .run 0 :: .run 1 :: .run 0 :: .run 1 :: L)
            (.run 1 ::
              (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R))) := by
      simpa only [bumpM] using
        rules.step_CB_run0_run_pos_exact 0 (.run 0 :: .run 0 :: .run 1 :: L)
          (.run 1 ::
            (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R))
    have h3 :
        ReachesIn target_tm 3
          (cfgCB target_tm
            (.run 0 :: .run 0 :: .run 1 :: .run 0 :: .run 1 :: L)
            (.run 1 ::
              (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R)))
          (cfgCB target_tm
            (.run 0 :: .run 1 :: .run 0 :: .run 1 :: .run 0 :: .run 1 :: L)
            (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R)) := by
      simpa only [bumpM] using
        rules.step_CB_run1_exact
          (.run 0 :: .run 0 :: .run 1 :: .run 0 :: .run 1 :: L)
          (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R)
    have h3' := ih (.run 1 :: .run 0 :: .run 1 :: .run 0 :: .run 1 :: L)
    have h12 := ReachesIn.trans (ReachesIn.trans h1 h2) h3
    convert ReachesIn.trans h12 h3' using 1
    all_goals (try simp [repBlock, repBlock_succ_right, List.append_assoc, List.cons_append, List.nil_append])
    all_goals (cases flag <;> simp only [fcost, Bool.false_eq_true, ite_false, ite_true] at * <;> omega)



theorem sourceElemBB_exact (L R : List SymTok) :
    ReachesIn target_tm (costElemBB flag L)
      ((evalSym target_tm) (.BB, L, R))
      ((evalSym target_tm) (stepElemBB L R)) := by
  cases L with
  | nil =>
    simp only [costElemBB, stepElemBB, strictList_eq, evalSym, evalM, encSymL,
      encSymR_bumpSymR]
    exact rules.step_BB_nil_exact (encSymR R)
  | cons t L1 =>
    cases t with
    | item x =>
      cases x with
      | zero =>
        simp only [costElemBB, stepElemBB, strictList_eq, evalSym, evalM, encSymL,
          encSymR_bumpSymR]
        exact rules.step_BB_zero_exact (encSymL L1) (encSymR R)
      | run d =>
        rcases d with _ | _ | _ | _ | d
        · simp only [costElemBB, stepElemBB, strictList_eq,
            SymRunEngine.strictNat_eq, evalSym, evalM, encSymL, encSymR,
            encSymR_bumpSymR]
   exact rules.step_BB_run0_exact (encSymL L1) (encSymR R)
        · simp only [costElemBB, stepElemBB, strictList_eq, SymRunEngine.strictNat_eq,
            evalSym, evalM, encSymL, encSymR, encSymR_bumpSymR]
   exact rules.step_BB_run1_exact (encSymL L1) (encSymR R)
        · simp only [costElemBB, stepElemBB, strictList_eq, SymRunEngine.strictNat_eq,
            evalSym, evalM, encSymL, encSymR, encSymR_bumpSymR]
   exact rules.step_BB_run2_exact (encSymL L1) (encSymR R)
        · simp only [costElemBB, stepElemBB, strictList_eq, SymRunEngine.strictNat_eq,
            evalSym, evalM, encSymL, encSymR, encSymR_bumpSymR]
   exact rules.step_BB_run3_exact (encSymL L1) (encSymR R)
        · simp only [costElemBB, stepElemBB, strictList_eq, SymRunEngine.strictNat_eq,
            evalSym, evalM, encSymL, encSymR, encSymR_bumpSymR]
   exact rules.step_BB_run_ge4_exact d (encSymL L1) (encSymR R)
    | repB1 _ => rfl
    | rep2 _ => rfl
    | rep12 _ => rfl

/-- Exact source `stepPureBB` cost, including all three repeated-block
    sweeps and the representation-preserving peeling fallback. -/
theorem sourcePureBB_exact (L R : List SymTok) :
    ReachesIn target_tm (costPureBB flag L R)
      ((evalSym target_tm) (.BB, L, R))
      ((evalSym target_tm) (stepPureBB L R)) := by
  cases L with
  | nil =>
    simpa only [costPureBB, stepPureBB] using rules.sourceElemBB_exact [] R
  | cons t L1 =>
    cases t with
    | item x =>
      simpa only [costPureBB, stepPureBB] using rules.sourceElemBB_exact (.item x :: L1) R
    | repB1 k =>
      simpa only [costPureBB, stepPureBB, evalSym, evalM,
        encSymL, encSymR, List.cons_append, List.nil_append]
        using rules.sweep_BB_B1_exact k (encSymL L1) (encSymR R)
    | rep2 p =>
      simp only [costPureBB, stepPureBB]
      cases hs : stripPrefixSym [.item (.run 0), .item (.run 1)] R with
      | some R2 =>
        have hR := stripPrefixSym_some _ R R2 hs
        rw [hR]
        simp only [fcost, Bool.false_eq_true, ite_false, evalSym, evalM, encSymL, encSymR,
          List.cons_append, List.nil_append]
        exact rules.sweep_BB_C2_exact p (encSymL L1) (encSymR R2)
      | none =>
        have heq : (evalSym target_tm) (.BB, .rep2 p :: L1, R) =
            (evalSym target_tm) (.BB, peelPureTok (.rep2 p) L1, R) := by
          simp only [evalSym, encSymL_peelPureTok]
        rw [heq]
        exact rules.sourceElemBB_exact (peelPureTok (.rep2 p) L1) R
    | rep12 m =>
      simp only [costPureBB, stepPureBB]
      cases hs : stripPrefixSym [.item (.run 0), .item (.run 1)] R with
      | some R2 =>
        have hR := stripPrefixSym_some _ R R2 hs
        rw [hR]
        simp only [fcost, Bool.false_eq_true, ite_false, evalSym, evalM, encSymL, encSymR,
          List.cons_append, List.nil_append]
        exact rules.sweep_BB_C12_exact m (encSymL L1) (encSymR R2)
      | none =>
        have heq : (evalSym target_tm) (.BB, .rep12 m :: L1, R) =
            (evalSym target_tm) (.BB, peelPureTok (.rep12 m) L1, R) := by
          simp only [evalSym, encSymL_peelPureTok]
        rw [heq]
        exact rules.sourceElemBB_exact (peelPureTok (.rep12 m) L1) R


theorem sourceElemDL_exact (L R : List SymTok) :
    ReachesIn target_tm (costElemDL flag L R)
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
        · simp only [costElemDL, stepElemDL, strictList_eq,
            evalSym, evalM, encSymL, encSymR_bumpSymR]
   exact rules.step_DL_run0_exact (encSymL L1) (encSymR R)
        · simp only [costElemDL, stepElemDL, strictList_eq,
            evalSym, evalM, encSymL, encSymR, encSymR_bumpSymR]
   exact rules.step_DL_run1_exact (encSymL L1) (encSymR R)
        · cases R with
          | nil => rfl
          | cons rt R1 =>
            cases rt with
            | item it =>
              cases it with
              | zero => rfl
              | run d0 =>
                simp only [costElemDL, stepElemDL,
                  strictList_eq, evalSym, evalM, encSymL, encSymR,
                  encSymL_prependZeroSym]
                exact rules.step_DL_run2_exact d0 (encSymL L1) (encSymR R1)
            | repB1 _ => rfl
            | rep2 _ => rfl
            | rep12 _ => rfl
        · rfl
    | repB1 _ => rfl
    | rep2 _ => rfl
    | rep12 _ => rfl

theorem sourcePureDL_exact (L R : List SymTok) :
    ReachesIn target_tm (costPureDL flag L R)
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
      rules.sourceElemDL_exact (peelPureTok t L1) R


theorem sourceElemCBRun0_exact (L R1 : List SymTok) :
    ReachesIn target_tm (costElemCBRun0 flag R1)
      ((evalSym target_tm) (.CB, L, .item (.run 0) :: R1))
      ((evalSym target_tm) (stepElemCB_run0 L R1)) := by
  cases R1 with
  | nil =>
    simp only [costElemCBRun0, stepElemCB_run0, strictList_eq,
      evalSym, evalM, encSymL, encSymR, encSymL_bumpSymL]
    exact rules.step_CB_run0_nil_exact (encSymL L)
  | cons t R2 =>
    cases t with
    | item x =>
      cases x with
      | zero =>
        simp only [costElemCBRun0, stepElemCB_run0, strictList_eq,
          evalSym, evalM, encSymL, encSymR, encSymL_bumpSymL]
        exact rules.step_CB_run0_zero_exact (encSymL L) (encSymR R2)
      | run d =>
        rcases d with _ | d
        · simp only [costElemCBRun0, stepElemCB_run0, strictList_eq,
            evalSym, evalM, encSymL, encSymR, encSymL_bumpSymL,
            encSymL_prependZeroSym]
   exact rules.step_CB_run0_run0_exact (encSymL L) (encSymR R2)
        · simp only [costElemCBRun0, stepElemCB_run0,
            strictList_eq, evalSym, evalM, encSymL, encSymR,
            encSymL_bumpSymL, encSymL_prependZeroSym]
   exact rules.step_CB_run0_run_pos_exact d (encSymL L) (encSymR R2)
    | repB1 _ => rfl
    | rep2 _ => rfl
    | rep12 _ => rfl

theorem sourceElemCB_exact (L R : List SymTok) :
    ReachesIn target_tm (costElemCB flag R)
      ((evalSym target_tm) (.CB, L, R))
      ((evalSym target_tm) (stepElemCB L R)) := by
  cases R with
  | nil =>
    simp only [costElemCB, stepElemCB, strictList_eq, evalSym, evalM,
      encSymL_bumpSymL, encSymR]
    exact rules.step_CB_nil_exact (encSymL L)
  | cons t R1 =>
    cases t with
    | item x =>
      cases x with
      | zero =>
        simp only [costElemCB, stepElemCB, strictList_eq, evalSym, evalM,
          encSymL_bumpSymL, encSymR_bumpSymR]
        exact rules.step_CB_zero_exact (encSymL L) (encSymR R1)
      | run d =>
        rcases d with _ | _ | _ | d
        · simpa only [costElemCB, stepElemCB] using rules.sourceElemCBRun0_exact L R1
        · simp only [costElemCB, stepElemCB, strictList_eq, evalSym, evalM,
            encSymL, encSymR, encSymL_bumpSymL]
   exact rules.step_CB_run1_exact (encSymL L) (encSymR R1)
        · simp only [costElemCB, stepElemCB, strictList_eq, evalSym, evalM,
            encSymL, encSymR, encSymL_bumpSymL]
   exact rules.step_CB_run2_exact (encSymL L) (encSymR R1)
        · simp only [costElemCB, stepElemCB, strictList_eq, SymRunEngine.strictNat_eq,
            evalSym, evalM, encSymL, encSymR, encSymL_bumpSymL]
   exact rules.step_CB_run_ge3_exact d (encSymL L) (encSymR R1)
    | repB1 _ => rfl
    | rep2 _ => rfl
    | rep12 _ => rfl

theorem sourcePureCB_exact (L R : List SymTok) :
    ReachesIn target_tm (costPureCB flag L R)
      ((evalSym target_tm) (.CB, L, R))
      ((evalSym target_tm) (stepPureCB L R)) := by
  cases R with
  | nil =>
    simpa only [costPureCB, stepPureCB] using rules.sourceElemCB_exact L []
  | cons t R1 =>
    cases t with
    | item x =>
      cases x with
      | zero => simpa only [costPureCB, stepPureCB] using rules.sourceElemCB_exact L (.item .zero :: R1)
      | run d =>
        rcases d with _ | _ | _ | d
        · simpa only [costPureCB, stepPureCB] using rules.sourceElemCBRun0_exact L R1
        · simpa only [costPureCB, stepPureCB] using rules.sourceElemCB_exact L (.item (.run 1) :: R1)
        · simpa only [costPureCB, stepPureCB] using rules.sourceElemCB_exact L (.item (.run 2) :: R1)
        · simpa only [costPureCB, stepPureCB, evalSym, evalM, encSymL_bumpSymL] using
            rules.step_CB_run_ge3_exact d (encSymL L) (encSymR R1)
    | repB1 k =>
      simp only [costPureCB, stepPureCB]
      cases hs2 : stripPrefixSym [.item (.run 0), .item (.run 0), .item (.run 1)] L with
      | some L2 =>
        have hL := stripPrefixSym_some _ L L2 hs2
        rw [hL]
        simp only [Option.isSome, Bool.or_true, Bool.true_or, Bool.false_or, ite_true, evalSym, evalM,
          encSymL, encSymR, List.cons_append, List.nil_append,
          repBlock_succ_right, List.append_assoc]
        exact rules.sweep_CB_B1_exact k (.run 0 :: .run 1 :: encSymL L2) (encSymR R1)
      | none =>
        cases hs1 : stripPrefixSym [.item (.run 0)] L with
        | some L1 =>
          have hL := stripPrefixSym_some _ L L1 hs1
          rw [hL]
          simp only [Option.isSome, Bool.or_true, Bool.true_or, Bool.false_or, ite_true, evalSym, evalM,
            encSymL, encSymR, List.cons_append, List.nil_append,
          repBlock_succ_right, List.append_assoc]
          exact rules.sweep_CB_B1_exact k (encSymL L1) (encSymR R1)
        | none =>
          rfl
    | rep2 p =>
      simp only [costPureCB, stepPureCB]
      cases hs2 : stripPrefixSym [.item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1)] L with
      | some L2 =>
        have hL := stripPrefixSym_some _ L L2 hs2
        rw [hL]
        simp only [Option.isSome, Bool.or_true, Bool.true_or, Bool.false_or, ite_true, evalSym, evalM,
          encSymL, encSymR, List.cons_append, List.nil_append,
          repBlock_succ_right, List.append_assoc]
        exact rules.sweep_CB_B2_exact p (.run 1 :: .run 0 :: .run 1 :: encSymL L2) (encSymR R1)
      | none =>
        cases hs1 : stripPrefixSym [.item (.run 0)] L with
        | some L1 =>
          have hL := stripPrefixSym_some _ L L1 hs1
          rw [hL]
          simp only [Option.isSome, Bool.or_true, Bool.true_or, Bool.false_or, ite_true, evalSym, evalM,
            encSymL, encSymR, List.cons_append, List.nil_append,
          repBlock_succ_right, List.append_assoc]
          exact rules.sweep_CB_B2_exact p (encSymL L1) (encSymR R1)
        | none =>
          rfl
    | rep12 m =>
      simp only [costPureCB, stepPureCB]
      cases hs1 : stripPrefixSym [.item (.run 0)] L with
      | some L1 =>
        have hL := stripPrefixSym_some _ L L1 hs1
        rw [hL]
        simp only [Option.isSome, Bool.or_true, Bool.true_or, Bool.false_or, ite_true, evalSym, evalM,
          encSymL, encSymR, List.cons_append, List.nil_append,
          repBlock_succ_right, List.append_assoc]
        exact rules.sweep_CB_B12R_exact m (encSymL L1) (encSymR R1)
      | none =>
        rfl



theorem stepPure_exact (s : SymState) : ReachesIn target_tm (costPure flag s)
    (evalSym target_tm s) (evalSym target_tm (stepPure s)) := by
  rcases s with ⟨mode,L,R⟩
  cases mode with
  | BB => exact rules.sourcePureBB_exact L R
  | DL => exact rules.sourcePureDL_exact L R
  | CB => exact rules.sourcePureCB_exact L R
  | HALT => rfl

theorem costIter_exact (n : Nat) (s : SymState) : ReachesIn target_tm (costIter flag n s)
    (evalSym target_tm s) (evalSym target_tm (iterStep stepPure n s)) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    exact ReachesIn.trans (rules.stepPure_exact s) (ih (stepPure s))


#print axioms stepPure_exact
#print axioms costIter_exact
end CountedAtoms
end BB6.Agent49.CountedSym
end
