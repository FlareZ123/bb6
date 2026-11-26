module
meta import Witness
import SourceCostModel
import all BusyBeaver.Basic
import all BusyBeaver.Defs.Core
import all BusyBeaver.Calculi.HaltShared
import all BusyBeaver.BB6.Halt.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA

open Mathlib Relation Nat Turing BusyBeaver
open BusyBeaver.RleStackEngine BusyBeaver.SymRunEngine
open BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA

open BB6.Agent11.SourceCost

namespace Agent26F412
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

recover_count BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.step_BB_nil as step_BB_nil_exact positive
recover_count BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.step_BB_zero as step_BB_zero_exact positive
recover_count BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.step_BB_run0 as step_BB_run0_exact positive
recover_count BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.step_BB_run1 as step_BB_run1_exact positive
recover_count BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.step_BB_run2 as step_BB_run2_exact positive
recover_count BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.step_BB_run3 as step_BB_run3_exact positive
recover_count BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.step_BB_run_ge4 as step_BB_run_ge4_exact positive
recover_count BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.exit_R_A as exit_R_A_exact positive
recover_count BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.step_DL_run0 as step_DL_run0_exact positive
recover_count BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.step_DL_run1 as step_DL_run1_exact positive
recover_count BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.step_CB_nil as step_CB_nil_exact positive
recover_count BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.step_CB_zero as step_CB_zero_exact positive
recover_count BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.step_CB_run0_nil as step_CB_run0_nil_exact positive
recover_count BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.step_CB_run0_zero as step_CB_run0_zero_exact positive
recover_count BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.step_CB_run0_run0 as step_CB_run0_run0_exact positive
recover_count BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.step_CB_run1 as step_CB_run1_exact positive
recover_count BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.step_CB_run2 as step_CB_run2_exact positive
recover_count BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.step_CB_run_ge3 as step_CB_run_ge3_exact positive
recover_count BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.init_to_BB as init_to_BB_exact positive
recover_count BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.step_DL_zero_halt as step_DL_zero_halt_exact positive

theorem cyc_R_A_exact (k : ℕ) (V s : ListBlank (Fin 2)) :
    ReachesIn target_tm (3*k)
      (⟨some BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.A, ⟨0, (0 : Fin 2) >> V, (([1] : List (Fin 2)) ^ k) +> s⟩⟩ : Cfg (Fin 2) (Fin 6))
      ⟨some BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.A, ⟨0, (0 : Fin 2) >> ((([0] : List (Fin 2)) ^ k) +> V), s⟩⟩ := by
  induction k generalizing V with
  | zero => exact witness_proof% (BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.cyc_R_A 0 V s) using []
  | succ k ih =>
    let hc (V' : ListBlank (Fin 2)) :
        ReachesStar target_tm
          (⟨some BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.A, ⟨0, (0 : Fin 2) >> V', (([1] : List (Fin 2)) ^ k) +> s⟩⟩ : Cfg (Fin 2) (Fin 6))
          ⟨some BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.A, ⟨0, (0 : Fin 2) >> ((([0] : List (Fin 2)) ^ k) +> V'), s⟩⟩ :=
        ⟨3*k, ih V'⟩
    have h := witness_proof% (BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.cyc_R_A (k+1) V s) using [hc]
    have hc : 3 + 3*k = 3*(k+1) := by omega
    rw [← hc]
    exact h

private def cycleWitness (k : ℕ) (V s : ListBlank (Fin 2)) :
    ReachesStar target_tm
      (⟨some BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.A, ⟨0, (0 : Fin 2) >> V, (([1] : List (Fin 2)) ^ k) +> s⟩⟩ : Cfg (Fin 2) (Fin 6))
      ⟨some BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.A, ⟨0, (0 : Fin 2) >> ((([0] : List (Fin 2)) ^ k) +> V), s⟩⟩ :=
  ⟨3*k, cyc_R_A_exact k V s⟩

theorem step_DL_run2_exact (d0 : ℕ) (L1 R1 : List MItem) :
    ReachesIn target_tm (3*d0+20)
      (cfgDL target_tm (.run 2 :: L1) (.run d0 :: R1))
      (cfgCB target_tm (.run 0 :: .run 0 :: List.replicate (d0 + 1) .zero ++ L1) R1) := by
  have h := witness_replaced% (BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.step_DL_run2 d0 L1 R1) using [] replacing [BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.cyc_R_A := cycleWitness]
  have hc : 6 + 3*(d0+1) + 11 = 3*d0+20 := by omega
  rw [← hc]
  exact h.2

theorem step_CB_run0_run_pos_exact (d2 : ℕ) (L R2 : List MItem) :
    ReachesIn target_tm (3*d2+19)
      (cfgCB target_tm L (.run 0 :: .run (d2 + 1) :: R2))
      (cfgCB target_tm (.run 0 :: .run 0 :: List.replicate d2 .zero ++ bumpM L) R2) := by
  have h := witness_replaced% (BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.step_CB_run0_run_pos d2 L R2) using [] replacing [BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.Solution.cyc_R_A := cycleWitness]
  have hc : 5 + 3*(d2+1) + 11 = 3*d2+19 := by omega
  rw [← hc]
  exact h.2

#print axioms step_BB_nil_exact
#print axioms step_BB_zero_exact
#print axioms step_BB_run0_exact
#print axioms step_BB_run1_exact
#print axioms step_BB_run2_exact
#print axioms step_BB_run3_exact
#print axioms step_BB_run_ge4_exact
#print axioms exit_R_A_exact
#print axioms step_DL_run0_exact
#print axioms step_DL_run1_exact
#print axioms step_CB_nil_exact
#print axioms step_CB_zero_exact
#print axioms step_CB_run0_nil_exact
#print axioms step_CB_run0_zero_exact
#print axioms step_CB_run0_run0_exact
#print axioms step_CB_run1_exact
#print axioms step_CB_run2_exact
#print axioms step_CB_run_ge3_exact
#print axioms init_to_BB_exact
#print axioms step_DL_zero_halt_exact
#print axioms cyc_R_A_exact
#print axioms step_DL_run2_exact
#print axioms step_CB_run0_run_pos_exact

/-! The following counted sweeps and mode proof structure are adapted from
Agent11's SourceExactF424Core and SourceExactPure{BB,DL,CB}424. The source
transition theorem statements are unchanged except for the F412 charges.
This file needs original-source CI; no unproved root claim. -/

theorem reachesIn_trans {m n : Nat} {c1 c2 c3 : Cfg (Fin 2) (Fin 6)}
    (h1 : ReachesIn target_tm m c1 c2) (h2 : ReachesIn target_tm n c2 c3) :
    ReachesIn target_tm (m + n) c1 c3 := by
  unfold ReachesIn at *
  exact multiStep_trans h1 h2


theorem step_BB_r0_r1_exact (L R : List MItem) :
    ReachesIn target_tm 9
      (cfgBB target_tm (.run 0 :: .run 1 :: L) R)
      (cfgBB target_tm L (.run 0 :: .run 1 :: R)) := by
  have h1 := step_BB_run0_exact (.run 1 :: L) R
  have h2 := step_BB_run1_exact L (.run 0 :: R)
  simpa [ReachesIn, bumpM, SymRunEngine.strictNat_eq] using reachesIn_trans h1 h2


theorem step_BB_r1_r0_r1_comm_exact (L R : List MItem) :
    ReachesIn target_tm 12
      (cfgBB target_tm (.run 1 :: .run 0 :: .run 1 :: L) (.run 0 :: .run 1 :: R))
      (cfgBB target_tm L
        (.run 0 :: .run 1 :: .run 0 :: .run 1 :: .run 1 :: R)) := by
  have h1 := step_BB_run1_exact (.run 0 :: .run 1 :: L) (.run 0 :: .run 1 :: R)
  have h1' :
      ReachesIn target_tm 3
        (cfgBB target_tm (.run 1 :: .run 0 :: .run 1 :: L) (.run 0 :: .run 1 :: R))
        (cfgBB target_tm (.run 0 :: .run 1 :: L)
          (.run 0 :: .run 1 :: .run 1 :: R)) := by
    simpa [ReachesIn, bumpM, SymRunEngine.strictNat_eq] using h1
  have h2 := step_BB_run0_exact (.run 1 :: L) (.run 0 :: .run 1 :: .run 1 :: R)
  have h3 := step_BB_run1_exact L (.run 0 :: .run 0 :: .run 1 :: .run 1 :: R)
  have h3' :
      ReachesIn target_tm 3
        (cfgBB target_tm (.run 1 :: L) (.run 0 :: .run 0 :: .run 1 :: .run 1 :: R))
        (cfgBB target_tm L
          (.run 0 :: .run 1 :: .run 0 :: .run 1 :: .run 1 :: R)) := by
    simpa [ReachesIn, bumpM, SymRunEngine.strictNat_eq] using h3
  simpa [ReachesIn] using reachesIn_trans (reachesIn_trans h1' h2) h3'


theorem sweep_BB_B1_exact (k : Nat) (L R : List MItem) :
    ReachesIn target_tm (9 * k)
      (cfgBB target_tm (repBlock [.run 0, .run 1] k ++ L) R)
      (cfgBB target_tm L (repBlock [.run 0, .run 1] k ++ R)) := by
  induction k generalizing R with
  | zero =>
      change multiStep target_tm _ 0 = some _
      rfl
  | succ k ih =>
    have h_eq : repBlock [.run 0, .run 1] (k + 1) ++ R =
        repBlock [.run 0, .run 1] k ++ (.run 0 :: .run 1 :: R) := by
      rw [repBlock_succ_right, List.append_assoc]
      rfl
    rw [h_eq]
    have h1 := step_BB_r0_r1_exact (repBlock [.run 0, .run 1] k ++ L) R
    have h2 := ih (.run 0 :: .run 1 :: R)
    convert reachesIn_trans h1 h2 using 1
    all_goals (try simp [repBlock, repBlock_succ_right, List.append_assoc, List.cons_append, List.nil_append])
    all_goals omega


theorem sweep_BB_C2_exact (p : Nat) (L R : List MItem) :
    ReachesIn target_tm (12 * p)
      (cfgBB target_tm (repBlock [.run 1, .run 0, .run 1] p ++ L)
        (.run 0 :: .run 1 :: R))
      (cfgBB target_tm L
        (.run 0 :: .run 1 :: repBlock [.run 0, .run 1, .run 1] p ++ R)) := by
  induction p generalizing R with
  | zero =>
      change multiStep target_tm _ 0 = some _
      rfl
  | succ p ih =>
    have h_eq :
        (.run 0 :: .run 1 :: repBlock [.run 0, .run 1, .run 1] (p + 1) ++ R) =
        (.run 0 :: .run 1 :: repBlock [.run 0, .run 1, .run 1] p ++
          (.run 0 :: .run 1 :: .run 1 :: R)) := by
      simp only [repBlock_succ_right, List.cons_append, List.nil_append, List.append_assoc]
    rw [h_eq]
    have h1 := step_BB_r1_r0_r1_comm_exact (repBlock [.run 1, .run 0, .run 1] p ++ L) R
    have h2 := ih (.run 0 :: .run 1 :: .run 1 :: R)
    convert reachesIn_trans h1 h2 using 1
    all_goals (try simp [repBlock, repBlock_succ_right, List.append_assoc, List.cons_append, List.nil_append])
    all_goals omega


theorem sweep_BB_C12_exact (m : Nat) (L R : List MItem) :
    ReachesIn target_tm (21 * m)
      (cfgBB target_tm
        (repBlock [.run 1, .run 0, .run 1, .run 0, .run 1] m ++ L)
        (.run 0 :: .run 1 :: R))
      (cfgBB target_tm L
        (.run 0 :: .run 1 ::
          repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R)) := by
  induction m generalizing R with
  | zero =>
      change multiStep target_tm _ 0 = some _
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
    have h1 := step_BB_r1_r0_r1_comm_exact
      (.run 0 :: .run 1 ::
        (repBlock [.run 1, .run 0, .run 1, .run 0, .run 1] m ++ L)) R
    have h2 := step_BB_r0_r1_exact
      (repBlock [.run 1, .run 0, .run 1, .run 0, .run 1] m ++ L)
      (.run 0 :: .run 1 :: .run 0 :: .run 1 :: .run 1 :: R)
    have h3 := ih (.run 0 :: .run 1 :: .run 0 :: .run 1 :: .run 1 :: R)
    have h12 := reachesIn_trans h1 h2
    convert reachesIn_trans h12 h3 using 1
    all_goals (try simp [repBlock, repBlock_succ_right, List.append_assoc, List.cons_append, List.nil_append])
    all_goals omega


theorem sweep_CB_B1_exact (k : Nat) (L R : List MItem) :
    ReachesIn target_tm (19 * k)
      (cfgCB target_tm (.run 0 :: L)
        (repBlock [.run 0, .run 1] k ++ R))
      (cfgCB target_tm (.run 0 :: repBlock [.run 0, .run 1] k ++ L) R) := by
  induction k generalizing L with
  | zero =>
      change multiStep target_tm _ 0 = some _
      rfl
  | succ k ih =>
    have h_eq :
        (.run 0 :: repBlock [.run 0, .run 1] (k + 1) ++ L) =
        (.run 0 :: repBlock [.run 0, .run 1] k ++ (.run 0 :: .run 1 :: L)) := by
      simp only [repBlock_succ_right, List.cons_append, List.nil_append, List.append_assoc]
    rw [h_eq]
    have h1 : ReachesIn target_tm 19
        (cfgCB target_tm (.run 0 :: L)
          (.run 0 :: .run 1 :: repBlock [.run 0, .run 1] k ++ R))
        (cfgCB target_tm (.run 0 :: .run 0 :: .run 1 :: L)
          (repBlock [.run 0, .run 1] k ++ R)) := by
      simpa [ReachesIn, bumpM, SymRunEngine.strictNat_eq] using
        step_CB_run0_run_pos_exact 0 (.run 0 :: L)
          (repBlock [.run 0, .run 1] k ++ R)
    have h2 := ih (.run 0 :: .run 1 :: L)
    convert reachesIn_trans h1 h2 using 1
    all_goals (try simp [repBlock, repBlock_succ_right, List.append_assoc, List.cons_append, List.nil_append])
    all_goals omega


theorem sweep_CB_B2_exact (p : Nat) (L R : List MItem) :
    ReachesIn target_tm (22 * p)
      (cfgCB target_tm (.run 0 :: L)
        (repBlock [.run 0, .run 1, .run 1] p ++ R))
      (cfgCB target_tm
        (.run 0 :: repBlock [.run 1, .run 0, .run 1] p ++ L) R) := by
  induction p generalizing L with
  | zero =>
      change multiStep target_tm _ 0 = some _
      rfl
  | succ p ih =>
    have h_eq :
        (.run 0 :: repBlock [.run 1, .run 0, .run 1] (p + 1) ++ L) =
        (.run 0 :: repBlock [.run 1, .run 0, .run 1] p ++
          (.run 1 :: .run 0 :: .run 1 :: L)) := by
      simp only [repBlock_succ_right, List.cons_append, List.nil_append, List.append_assoc]
    rw [h_eq]
    have h1 :
        ReachesIn target_tm 19
          (cfgCB target_tm (.run 0 :: L)
            (.run 0 :: .run 1 :: .run 1 ::
              (repBlock [.run 0, .run 1, .run 1] p ++ R)))
          (cfgCB target_tm (.run 0 :: .run 0 :: .run 1 :: L)
            (.run 1 :: (repBlock [.run 0, .run 1, .run 1] p ++ R))) := by
      simpa [ReachesIn, bumpM, SymRunEngine.strictNat_eq] using
        step_CB_run0_run_pos_exact 0 (.run 0 :: L)
          (.run 1 :: (repBlock [.run 0, .run 1, .run 1] p ++ R))
    have h2 :
        ReachesIn target_tm 3
          (cfgCB target_tm (.run 0 :: .run 0 :: .run 1 :: L)
            (.run 1 :: (repBlock [.run 0, .run 1, .run 1] p ++ R)))
          (cfgCB target_tm (.run 0 :: .run 1 :: .run 0 :: .run 1 :: L)
            (repBlock [.run 0, .run 1, .run 1] p ++ R)) := by
      simpa [ReachesIn, bumpM, SymRunEngine.strictNat_eq] using
        step_CB_run1_exact (.run 0 :: .run 0 :: .run 1 :: L)
          (repBlock [.run 0, .run 1, .run 1] p ++ R)
    have h3 := ih (.run 1 :: .run 0 :: .run 1 :: L)
    have h12 := reachesIn_trans h1 h2
    convert reachesIn_trans h12 h3 using 1
    all_goals (try simp [repBlock, repBlock_succ_right, List.append_assoc, List.cons_append, List.nil_append])
    all_goals omega


theorem sweep_CB_B12R_exact (m : Nat) (L R : List MItem) :
    ReachesIn target_tm (41 * m)
      (cfgCB target_tm (.run 0 :: L)
        (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R))
      (cfgCB target_tm
        (.run 0 :: repBlock [.run 1, .run 0, .run 1, .run 0, .run 1] m ++ L) R) := by
  induction m generalizing L with
  | zero =>
      change multiStep target_tm _ 0 = some _
      rfl
  | succ m ih =>
    have h_eq :
        (.run 0 :: repBlock [.run 1, .run 0, .run 1, .run 0, .run 1] (m + 1) ++ L) =
        (.run 0 :: repBlock [.run 1, .run 0, .run 1, .run 0, .run 1] m ++
          (.run 1 :: .run 0 :: .run 1 :: .run 0 :: .run 1 :: L)) := by
      simp only [repBlock_succ_right, List.cons_append, List.nil_append, List.append_assoc]
    rw [h_eq]
    have h1 :
        ReachesIn target_tm 19
          (cfgCB target_tm (.run 0 :: L)
            (.run 0 :: .run 1 :: .run 0 :: .run 1 :: .run 1 ::
              (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R)))
          (cfgCB target_tm (.run 0 :: .run 0 :: .run 1 :: L)
            (.run 0 :: .run 1 :: .run 1 ::
              (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R))) := by
      simpa [ReachesIn, bumpM, SymRunEngine.strictNat_eq] using
        step_CB_run0_run_pos_exact 0 (.run 0 :: L)
          (.run 0 :: .run 1 :: .run 1 ::
            (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R))
    have h2 :
        ReachesIn target_tm 19
          (cfgCB target_tm (.run 0 :: .run 0 :: .run 1 :: L)
            (.run 0 :: .run 1 :: .run 1 ::
              (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R)))
          (cfgCB target_tm (.run 0 :: .run 0 :: .run 1 :: .run 0 :: .run 1 :: L)
            (.run 1 ::
              (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R))) := by
      simpa [ReachesIn, bumpM, SymRunEngine.strictNat_eq] using
        step_CB_run0_run_pos_exact 0 (.run 0 :: .run 0 :: .run 1 :: L)
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
      simpa [ReachesIn, bumpM, SymRunEngine.strictNat_eq] using
        step_CB_run1_exact
          (.run 0 :: .run 0 :: .run 1 :: .run 0 :: .run 1 :: L)
          (repBlock [.run 0, .run 1, .run 0, .run 1, .run 1] m ++ R)
    have h3' := ih (.run 1 :: .run 0 :: .run 1 :: .run 0 :: .run 1 :: L)
    have h12 := reachesIn_trans (reachesIn_trans h1 h2) h3
    convert reachesIn_trans h12 h3' using 1
    all_goals (try simp [repBlock, repBlock_succ_right, List.append_assoc, List.cons_append, List.nil_append])
    all_goals omega



theorem sourceElemBB_exact (L R : List SymTok) :
    ReachesIn target_tm (costElemBB false L)
      ((evalSym target_tm) (.BB, L, R))
      ((evalSym target_tm) (stepElemBB L R)) := by
  cases L with
  | nil =>
    simpa only [ReachesIn, Nat.zero_add, Nat.reduceAdd, List.cons_append, List.nil_append, costElemBB, stepElemBB, strictList_eq, evalSym, evalM, encSymL,
      encSymR_bumpSymR] using step_BB_nil_exact (encSymR R)
  | cons t L1 =>
    cases t with
    | item x =>
      cases x with
      | zero =>
        simpa only [ReachesIn, Nat.zero_add, Nat.reduceAdd, List.cons_append, List.nil_append, costElemBB, stepElemBB, strictList_eq, evalSym, evalM, encSymL,
          encSymR_bumpSymR] using step_BB_zero_exact (encSymL L1) (encSymR R)
      | run d =>
        rcases d with _ | _ | _ | _ | d
        · simpa only [ReachesIn, Nat.zero_add, Nat.reduceAdd, List.cons_append, List.nil_append, costElemBB, fcost, Bool.false_eq_true, ite_false, stepElemBB, strictList_eq,
            SymRunEngine.strictNat_eq, evalSym, evalM, encSymL, encSymR,
            encSymR_bumpSymR] using step_BB_run0_exact (encSymL L1) (encSymR R)
        · simpa only [ReachesIn, Nat.zero_add, Nat.reduceAdd, List.cons_append, List.nil_append, costElemBB, stepElemBB, strictList_eq, SymRunEngine.strictNat_eq,
            evalSym, evalM, encSymL, encSymR, encSymR_bumpSymR]
            using step_BB_run1_exact (encSymL L1) (encSymR R)
        · simpa only [ReachesIn, Nat.zero_add, Nat.reduceAdd, List.cons_append, List.nil_append, costElemBB, stepElemBB, strictList_eq, SymRunEngine.strictNat_eq,
            evalSym, evalM, encSymL, encSymR, encSymR_bumpSymR]
            using step_BB_run2_exact (encSymL L1) (encSymR R)
        · simpa only [ReachesIn, Nat.zero_add, Nat.reduceAdd, List.cons_append, List.nil_append, costElemBB, stepElemBB, strictList_eq, SymRunEngine.strictNat_eq,
            evalSym, evalM, encSymL, encSymR, encSymR_bumpSymR]
            using step_BB_run3_exact (encSymL L1) (encSymR R)
        · simpa only [ReachesIn, Nat.zero_add, Nat.reduceAdd, List.cons_append, List.nil_append, costElemBB, stepElemBB, strictList_eq, SymRunEngine.strictNat_eq,
            evalSym, evalM, encSymL, encSymR, encSymR_bumpSymR]
            using step_BB_run_ge4_exact d (encSymL L1) (encSymR R)
    | repB1 _ => rfl
    | rep2 _ => rfl
    | rep12 _ => rfl

/-- Exact source `stepPureBB` cost, including all three repeated-block
    sweeps and the representation-preserving peeling fallback. -/
theorem sourcePureBB_exact (L R : List SymTok) :
    ReachesIn target_tm (costPureBB false L R)
      ((evalSym target_tm) (.BB, L, R))
      ((evalSym target_tm) (stepPureBB L R)) := by
  cases L with
  | nil =>
    simpa only [ReachesIn, Nat.zero_add, Nat.reduceAdd, List.cons_append, List.nil_append, costPureBB, stepPureBB] using sourceElemBB_exact [] R
  | cons t L1 =>
    cases t with
    | item x =>
      simpa only [ReachesIn, Nat.zero_add, Nat.reduceAdd, List.cons_append, List.nil_append, costPureBB, stepPureBB] using sourceElemBB_exact (.item x :: L1) R
    | repB1 k =>
      simpa only [ReachesIn, Nat.zero_add, Nat.reduceAdd, List.cons_append, List.nil_append, costPureBB, stepPureBB, fcost, Bool.false_eq_true, ite_false, evalSym, evalM,
        encSymL, encSymR]
        using sweep_BB_B1_exact k (encSymL L1) (encSymR R)
    | rep2 p =>
      simp only [costPureBB, stepPureBB]
      cases hs : stripPrefixSym [.item (.run 0), .item (.run 1)] R with
      | some R2 =>
        have hR := stripPrefixSym_some _ R R2 hs
        rw [hR]
        simp only [fcost, Bool.false_eq_true, ite_false, evalSym, evalM, encSymL, encSymR,
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
        simp only [fcost, Bool.false_eq_true, ite_false, evalSym, evalM, encSymL, encSymR,
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


theorem sourceElemDL_exact (L R : List SymTok) :
    ReachesIn target_tm (costElemDL false L R)
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
        · simpa only [ReachesIn, Nat.zero_add, Nat.reduceAdd, List.cons_append, List.nil_append, costElemDL, stepElemDL, strictList_eq,
            evalSym, evalM, encSymL, encSymR_bumpSymR] using
              step_DL_run0_exact (encSymL L1) (encSymR R)
        · simpa only [ReachesIn, Nat.zero_add, Nat.reduceAdd, List.cons_append, List.nil_append, costElemDL, stepElemDL, strictList_eq,
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
                simpa only [ReachesIn, Nat.zero_add, Nat.reduceAdd, List.cons_append, List.nil_append, costElemDL, stepElemDL, fcost, Bool.false_eq_true, ite_false,
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
    ReachesIn target_tm (costPureDL false L R)
      ((evalSym target_tm) (.DL, L, R))
      ((evalSym target_tm) (stepPureDL L R)) := by
  cases L with
  | nil => rfl
  | cons t L1 =>
    have heq : (evalSym target_tm) (.DL, t :: L1, R) =
        (evalSym target_tm) (.DL, peelPureTok t L1, R) := by
      simp only [evalSym, encSymL_peelPureTok]
    rw [heq]
    simpa only [ReachesIn, Nat.zero_add, Nat.reduceAdd, List.cons_append, List.nil_append, costPureDL, stepPureDL] using
      sourceElemDL_exact (peelPureTok t L1) R

#print axioms sourceElemDL_exact
#print axioms sourcePureDL_exact


theorem sourceElemCBRun0_exact (L R1 : List SymTok) :
    ReachesIn target_tm (costElemCBRun0 false R1)
      ((evalSym target_tm) (.CB, L, .item (.run 0) :: R1))
      ((evalSym target_tm) (stepElemCB_run0 L R1)) := by
  cases R1 with
  | nil =>
    simpa only [ReachesIn, Nat.zero_add, Nat.reduceAdd, List.cons_append, List.nil_append, costElemCBRun0, stepElemCB_run0, strictList_eq,
      evalSym, evalM, encSymL, encSymR, encSymL_bumpSymL] using
      step_CB_run0_nil_exact (encSymL L)
  | cons t R2 =>
    cases t with
    | item x =>
      cases x with
      | zero =>
        simpa only [ReachesIn, Nat.zero_add, Nat.reduceAdd, List.cons_append, List.nil_append, costElemCBRun0, stepElemCB_run0, strictList_eq,
          evalSym, evalM, encSymL, encSymR, encSymL_bumpSymL] using
          step_CB_run0_zero_exact (encSymL L) (encSymR R2)
      | run d =>
        rcases d with _ | d
        · simpa only [ReachesIn, Nat.zero_add, Nat.reduceAdd, List.cons_append, List.nil_append, costElemCBRun0, stepElemCB_run0, strictList_eq,
            evalSym, evalM, encSymL, encSymR, encSymL_bumpSymL,
            encSymL_prependZeroSym] using
            step_CB_run0_run0_exact (encSymL L) (encSymR R2)
        · simpa only [ReachesIn, Nat.zero_add, Nat.reduceAdd, List.cons_append, List.nil_append, costElemCBRun0, fcost, Bool.false_eq_true, ite_false, stepElemCB_run0,
            strictList_eq, evalSym, evalM, encSymL, encSymR,
            encSymL_bumpSymL, encSymL_prependZeroSym] using
            step_CB_run0_run_pos_exact d (encSymL L) (encSymR R2)
    | repB1 _ => rfl
    | rep2 _ => rfl
    | rep12 _ => rfl

theorem sourceElemCB_exact (L R : List SymTok) :
    ReachesIn target_tm (costElemCB false R)
      ((evalSym target_tm) (.CB, L, R))
      ((evalSym target_tm) (stepElemCB L R)) := by
  cases R with
  | nil =>
    simpa only [ReachesIn, Nat.zero_add, Nat.reduceAdd, List.cons_append, List.nil_append, costElemCB, stepElemCB, strictList_eq, evalSym, evalM,
      encSymL_bumpSymL, encSymR] using step_CB_nil_exact (encSymL L)
  | cons t R1 =>
    cases t with
    | item x =>
      cases x with
      | zero =>
        simpa only [ReachesIn, Nat.zero_add, Nat.reduceAdd, List.cons_append, List.nil_append, costElemCB, stepElemCB, strictList_eq, evalSym, evalM,
          encSymL_bumpSymL, encSymR_bumpSymR, encSymR] using
            step_CB_zero_exact (encSymL L) (encSymR R1)
      | run d =>
        rcases d with _ | _ | _ | d
        · simpa only [ReachesIn, Nat.zero_add, Nat.reduceAdd, List.cons_append, List.nil_append, costElemCB, stepElemCB] using sourceElemCBRun0_exact L R1
        · simpa only [ReachesIn, Nat.zero_add, Nat.reduceAdd, List.cons_append, List.nil_append, costElemCB, stepElemCB, strictList_eq, evalSym, evalM,
            encSymL, encSymR, encSymL_bumpSymL] using
              step_CB_run1_exact (encSymL L) (encSymR R1)
        · simpa only [ReachesIn, Nat.zero_add, Nat.reduceAdd, List.cons_append, List.nil_append, costElemCB, stepElemCB, strictList_eq, evalSym, evalM,
            encSymL, encSymR, encSymL_bumpSymL] using
              step_CB_run2_exact (encSymL L) (encSymR R1)
        · simpa only [ReachesIn, Nat.zero_add, Nat.reduceAdd, List.cons_append, List.nil_append, costElemCB, stepElemCB, strictList_eq, SymRunEngine.strictNat_eq,
            evalSym, evalM, encSymL, encSymR, encSymL_bumpSymL] using
              step_CB_run_ge3_exact d (encSymL L) (encSymR R1)
    | repB1 _ => rfl
    | rep2 _ => rfl
    | rep12 _ => rfl

theorem sourcePureCB_exact (L R : List SymTok) :
    ReachesIn target_tm (costPureCB false L R)
      ((evalSym target_tm) (.CB, L, R))
      ((evalSym target_tm) (stepPureCB L R)) := by
  cases R with
  | nil =>
    simpa only [ReachesIn, Nat.zero_add, Nat.reduceAdd, List.cons_append, List.nil_append, costPureCB, stepPureCB] using sourceElemCB_exact L []
  | cons t R1 =>
    cases t with
    | item x =>
      cases x with
      | zero => simpa only [ReachesIn, Nat.zero_add, Nat.reduceAdd, List.cons_append, List.nil_append, costPureCB, stepPureCB] using sourceElemCB_exact L (.item .zero :: R1)
      | run d =>
        rcases d with _ | _ | _ | d
        · simpa only [ReachesIn, Nat.zero_add, Nat.reduceAdd, List.cons_append, List.nil_append, costPureCB, stepPureCB] using sourceElemCBRun0_exact L R1
        · simpa only [ReachesIn, Nat.zero_add, Nat.reduceAdd, List.cons_append, List.nil_append, costPureCB, stepPureCB] using sourceElemCB_exact L (.item (.run 1) :: R1)
        · simpa only [ReachesIn, Nat.zero_add, Nat.reduceAdd, List.cons_append, List.nil_append, costPureCB, stepPureCB] using sourceElemCB_exact L (.item (.run 2) :: R1)
        · simpa only [ReachesIn, Nat.zero_add, Nat.reduceAdd, List.cons_append, List.nil_append, costPureCB, stepPureCB, costElemCB, stepElemCB, BusyBeaver.SymRunEngine.strictNat_eq, BusyBeaver.SymRunEngine.strictList_eq] using
            sourceElemCB_exact L (.item (.run (d+1+1+1)) :: R1)
    | repB1 k =>
      simp only [costPureCB, stepPureCB]
      cases hs2 : stripPrefixSym [.item (.run 0), .item (.run 0), .item (.run 1)] L with
      | some L2 =>
        have hL := stripPrefixSym_some _ L L2 hs2
        rw [hL]
        simpa only [ReachesIn, Option.isSome_some, Option.isSome_none, Bool.true_or, Bool.false_or,
           Bool.false_eq_true, ite_false, ite_true, eq_self, fcost, evalSym, evalM,
          encSymL, encSymR, List.cons_append, List.nil_append,
          repBlock_succ_right, List.append_assoc] using
          sweep_CB_B1_exact k (.run 0 :: .run 1 :: encSymL L2) (encSymR R1)
      | none =>
        cases hs1 : stripPrefixSym [.item (.run 0)] L with
        | some L1 =>
          have hL := stripPrefixSym_some _ L L1 hs1
          rw [hL]
          simpa only [ReachesIn, Option.isSome_some, Option.isSome_none, Bool.true_or, Bool.false_or,
           Bool.false_eq_true, ite_false, ite_true, eq_self, fcost, evalSym, evalM,
            encSymL, encSymR, List.cons_append, List.nil_append,
          repBlock_succ_right, List.append_assoc] using
            sweep_CB_B1_exact k (encSymL L1) (encSymR R1)
        | none =>
          simp only [Option.isSome_none, Bool.false_or, Bool.false_eq_true, ite_false] <;> rfl
    | rep2 p =>
      simp only [costPureCB, stepPureCB]
      cases hs2 : stripPrefixSym [.item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1)] L with
      | some L2 =>
        have hL := stripPrefixSym_some _ L L2 hs2
        rw [hL]
        simpa only [ReachesIn, Option.isSome_some, Option.isSome_none, Bool.true_or, Bool.false_or,
           Bool.false_eq_true, ite_false, ite_true, eq_self, fcost, evalSym, evalM,
          encSymL, encSymR, List.cons_append, List.nil_append,
          repBlock_succ_right, List.append_assoc] using
          sweep_CB_B2_exact p (.run 1 :: .run 0 :: .run 1 :: encSymL L2) (encSymR R1)
      | none =>
        cases hs1 : stripPrefixSym [.item (.run 0)] L with
        | some L1 =>
          have hL := stripPrefixSym_some _ L L1 hs1
          rw [hL]
          simpa only [ReachesIn, Option.isSome_some, Option.isSome_none, Bool.true_or, Bool.false_or,
           Bool.false_eq_true, ite_false, ite_true, eq_self, fcost, evalSym, evalM,
            encSymL, encSymR, List.cons_append, List.nil_append,
          repBlock_succ_right, List.append_assoc] using
            sweep_CB_B2_exact p (encSymL L1) (encSymR R1)
        | none =>
          simp only [Option.isSome_none, Bool.false_or, Bool.false_eq_true, ite_false] <;> rfl
    | rep12 m =>
      simp only [costPureCB, stepPureCB]
      cases hs1 : stripPrefixSym [.item (.run 0)] L with
      | some L1 =>
        have hL := stripPrefixSym_some _ L L1 hs1
        rw [hL]
        simpa only [ReachesIn, Option.isSome_some, Option.isSome_none, Bool.true_or, Bool.false_or,
           Bool.false_eq_true, ite_false, ite_true, eq_self, fcost, evalSym, evalM,
          encSymL, encSymR, List.cons_append, List.nil_append,
          repBlock_succ_right, List.append_assoc] using
          sweep_CB_B12R_exact m (encSymL L1) (encSymR R1)
      | none =>
        simp only [Option.isSome_none, Bool.false_eq_true, ite_false] <;> rfl

#print axioms sourceElemCBRun0_exact
#print axioms sourceElemCB_exact
#print axioms sourcePureCB_exact


theorem stepPure_exact (s : SymState) : ReachesIn target_tm (costPure false s)
    (evalSym target_tm s) (evalSym target_tm (stepPure s)) := by
  rcases s with ⟨mode,L,R⟩
  cases mode with
  | BB => exact sourcePureBB_exact L R
  | DL => exact sourcePureDL_exact L R
  | CB => exact sourcePureCB_exact L R
  | HALT => rfl

theorem costIter_exact (n : Nat) (s : SymState) : ReachesIn target_tm (costIter false n s)
    (evalSym target_tm s) (evalSym target_tm (iterStep stepPure n s)) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    exact reachesIn_trans (stepPure_exact s) (ih (stepPure s))

#print axioms stepPure_exact
#print axioms costIter_exact
end Agent26F412
