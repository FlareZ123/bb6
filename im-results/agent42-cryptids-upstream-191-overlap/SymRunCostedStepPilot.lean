/-
Scratch pilot: turn the upstream execute tactic into an exact ReachesIn proof.
Pinned source: google-deepmind/cryptids @ 3647718b5df22e1a61462dec0376bd204526285a.
-/
import BusyBeaver.BB6.Halt.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution

open BusyBeaver.RleStackEngine BusyBeaver.SymRunEngine

macro "stepWithin" : tactic => `(tactic| (
  try simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, pow_succ_list, pow_zero_list,
    cons_append_list, nil_append_list, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, default_head, default_tail,
    encM_nil, encM_cons_zero, encM_cons_run, encLeft_cons_head, cons_one_encLeft_tail,
    encRight_cons_head, cons_one_encRight_tail, encM_cons_run_head, cons_one_encM_cons_run_tail]
  apply BusyBeaver.ReachesIn.step_left
  · rfl
  · simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, Turing.Tape.move,
      pow_succ_list, pow_zero_list, cons_append_list, nil_append_list,
      listblank_append_cons, listblank_append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons, Tape.write, zero_cons_default, default_head,
      default_tail, encM_nil, encM_cons_zero, encM_cons_run, encLeft_cons_head,
      cons_one_encLeft_tail, encRight_cons_head, cons_one_encRight_tail,
      encM_cons_run_head, cons_one_encM_cons_run_tail]
))

macro "finishWithin" : tactic => `(tactic| (
  change multiStep target_tm _ 0 = some _
  simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, pow_succ_list, pow_zero_list,
    cons_append_list, nil_append_list, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, zero_cons_default, default_head,
    default_tail, enc1_nil, encM_nil, encM_cons_zero, encM_cons_run, encLeft_cons_head,
    cons_one_encLeft_tail, encRight_cons_head, cons_one_encRight_tail, encM_cons_run_head,
    cons_one_encM_cons_run_tail, multiStep_zero]
  try rfl
))

macro "executeWithin" n:num : tactic => `(tactic| (
  iterate $n stepWithin
  finishWithin
))

theorem step_BB_nil_exact (R : List MItem) :
    ReachesIn target_tm 1 (cfgBB target_tm [] R) (cfgCB target_tm [] (bumpM R)) := by
  unfold cfgBB cfgCB
  dsimp only [isVarA_tm, ite_true, ite_false]
  rw [← encM_bumpM]
  executeWithin 1

theorem step_BB_run0_exact (L1 R : List MItem) :
    ReachesIn target_tm 8 (cfgBB target_tm (.run 0 :: L1) R)
      (cfgBB target_tm L1 (.run 0 :: R)) := by
  unfold cfgBB
  dsimp only [isVarA_tm, ite_true, ite_false]
  executeWithin 8

theorem reachesIn_trans {m n : Nat} {c1 c2 c3 : Cfg (Fin 2) (Fin 6)}
    (h1 : ReachesIn target_tm m c1 c2) (h2 : ReachesIn target_tm n c2 c3) :
    ReachesIn target_tm (m + n) c1 c3 := by
  unfold ReachesIn at *
  exact multiStep_trans h1 h2

theorem cyc_R_A_exact (k : Nat) (V s : ListBlank (Fin 2)) :
    ReachesIn target_tm (3 * k)
      (⟨some A, ⟨0, (0 : Fin 2) >> V, (([1] : List (Fin 2)) ^ k) +> s⟩⟩ :
        Cfg (Fin 2) (Fin 6))
      ⟨some A, ⟨0, (0 : Fin 2) >> ((([0] : List (Fin 2)) ^ k) +> V), s⟩⟩ := by
  induction k generalizing V with
  | zero =>
      change multiStep target_tm _ 0 = some _
      simp only [multiStep_zero]
      rfl
  | succ k ih =>
      have h1 :
          ReachesIn target_tm 3
            (⟨some A, ⟨0, (0 : Fin 2) >> V, (([1] : List (Fin 2)) ^ (k + 1)) +> s⟩⟩ :
              Cfg (Fin 2) (Fin 6))
            ⟨some A, ⟨0, (0 : Fin 2) >> (0 : Fin 2) >> V,
              (([1] : List (Fin 2)) ^ k) +> s⟩⟩ := by
        executeWithin 3
      have h2 := ih ((0 : Fin 2) >> V)
      have h12 := reachesIn_trans h1 h2
      have h_eq :
          (([0] : List (Fin 2)) ^ k) +> ((0 : Fin 2) >> V) =
            (([0] : List (Fin 2)) ^ (k + 1)) +> V := by
        rw [zeros_append_cons_zero k V]
        simp only [pow_succ_list, cons_append_list, nil_append_list,
          listblank_append_cons]
      rw [h_eq] at h12
      have hlen : 3 + 3 * k = 3 * (k + 1) := by omega
      simpa [hlen] using h12

theorem exit_R_A_exact (W R1 : List MItem) :
    ReachesIn target_tm 13
      (⟨some A, ⟨0, (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encM W,
        (0 : Fin 2) >> encM R1⟩⟩ : Cfg (Fin 2) (Fin 6))
      (cfgCB target_tm (.run 0 :: .run 0 :: W) R1) := by
  unfold cfgCB
  dsimp only [isVarA_tm, ite_true, ite_false]
  executeWithin 13

theorem step_DL_run2_exact (d0 : Nat) (L1 R1 : List MItem) :
    ReachesIn target_tm (3 * d0 + 22)
      (cfgDL target_tm (.run 2 :: L1) (.run d0 :: R1))
      (cfgCB target_tm
        (.run 0 :: .run 0 :: List.replicate (d0 + 1) .zero ++ L1) R1) := by
  unfold cfgDL
  dsimp only [isVarA_tm, ite_true, ite_false]
  have h1 :
      ReachesIn target_tm 6
        (encM (.run 2 :: L1) <{{D}} encM (.run d0 :: R1))
        (⟨some A, ⟨0, (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encM L1,
          (([1] : List (Fin 2)) ^ (d0 + 1)) +> ((0 : Fin 2) >> encM R1)⟩⟩ :
            Cfg (Fin 2) (Fin 6)) := by
    executeWithin 6
  have h2 := cyc_R_A_exact (d0 + 1)
    ((0 : Fin 2) >> (0 : Fin 2) >> encM L1) ((0 : Fin 2) >> encM R1)
  have h12 := reachesIn_trans h1 h2
  have h_z1 := zeros_append_cons_zero (d0 + 1)
    ((0 : Fin 2) >> (0 : Fin 2) >> encM L1)
  have h_z2 := zeros_append_cons_zero (d0 + 1) (encM L1)
  rw [h_z1, h_z2, encM_replicate_zero] at h12
  have h3 := exit_R_A_exact (List.replicate (d0 + 1) .zero ++ L1) R1
  have hfin := reachesIn_trans h12 h3
  convert hfin using 1 <;> omega

theorem step_CB_run0_run_pos_exact (d2 : Nat) (L R2 : List MItem) :
    ReachesIn target_tm (3 * d2 + 21)
      (cfgCB target_tm L (.run 0 :: .run (d2 + 1) :: R2))
      (cfgCB target_tm
        (.run 0 :: .run 0 :: List.replicate d2 .zero ++ bumpM L) R2) := by
  unfold cfgCB
  dsimp only [isVarA_tm, ite_true, ite_false]
  have h1 :
      ReachesIn target_tm 5
        (⟨some C, ⟨0, encM L, encM (.run 0 :: .run (d2 + 1) :: R2)⟩⟩ :
          Cfg (Fin 2) (Fin 6))
        (⟨some A, ⟨0, (0 : Fin 2) >> (0 : Fin 2) >> encM (bumpM L),
          (([1] : List (Fin 2)) ^ (d2 + 1)) +> ((0 : Fin 2) >> encM R2)⟩⟩ :
          Cfg (Fin 2) (Fin 6)) := by
    rw [← encM_bumpM L]
    executeWithin 5
  have h2 := cyc_R_A_exact (d2 + 1)
    ((0 : Fin 2) >> encM (bumpM L)) ((0 : Fin 2) >> encM R2)
  have h12 := reachesIn_trans h1 h2
  have h_z1 := zeros_append_cons_zero (d2 + 1) (encM (bumpM L))
  have h_z2 :
      ((([0] : List (Fin 2)) ^ (d2 + 1)) +> encM (bumpM L)) =
        (0 : Fin 2) >> ((([0] : List (Fin 2)) ^ d2) +> encM (bumpM L)) := by
    simp only [pow_succ_list, cons_append_list, nil_append_list, listblank_append_cons]
  rw [h_z1, h_z2, encM_replicate_zero] at h12
  have h3 := exit_R_A_exact (List.replicate d2 .zero ++ bumpM L) R2
  have hfin := reachesIn_trans h12 h3
  convert hfin using 1 <;> omega

end BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution
