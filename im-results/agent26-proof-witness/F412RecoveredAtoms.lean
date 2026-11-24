module
meta import Witness
import all BusyBeaver.Basic
import all BusyBeaver.Defs.Core
import all BusyBeaver.Calculi.HaltShared
import all BusyBeaver.BB6.Halt.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA

open Mathlib Relation Nat Turing BusyBeaver
open BusyBeaver.RleStackEngine BusyBeaver.SymRunEngine
open BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA

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
end Agent26F412
