import SourceF424Machine

/-! Standalone first primitive F424 exact reachability tests. No dependency on
Agent42's later uncompiled loops. Source uses original pinned machine table. -/

set_option maxRecDepth 16384
set_option maxHeartbeats 0

open Mathlib Relation Nat Turing BusyBeaver
namespace BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution
open BusyBeaver.RleStackEngine BusyBeaver.SymRunEngine

macro "stepWithin" : tactic => `(tactic| (
  try simp only [isVarA_tm, ite_true, ite_false,BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, pow_succ_list, pow_zero_list,
    cons_append_list, nil_append_list, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, default_head, default_tail,
    encM_nil, encM_cons_zero, encM_cons_run, encLeft_cons_head, cons_one_encLeft_tail,
    encRight_cons_head, cons_one_encRight_tail, encM_cons_run_head, cons_one_encM_cons_run_tail]
  apply BusyBeaver.ReachesIn.step_left
  · rfl
  · simp only [isVarA_tm, ite_true, ite_false,
      BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, Turing.Tape.move,
      pow_succ_list, pow_zero_list, cons_append_list, nil_append_list,
      listblank_append_cons, listblank_append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons, Tape.write, zero_cons_default, default_head,
      default_tail, encM_nil, encM_cons_zero, encM_cons_run, encLeft_cons_head,
      cons_one_encLeft_tail, encRight_cons_head, cons_one_encRight_tail,
      encM_cons_run_head, cons_one_encM_cons_run_tail]
    try rfl
))

macro "finishWithin" : tactic => `(tactic| (
  all_goals (
    change multiStep target_tm _ 0 = some _
    simp only [isVarA_tm, ite_true, ite_false,
      BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, pow_succ_list, pow_zero_list,
      cons_append_list, nil_append_list, listblank_append_cons, listblank_append_nil,
      Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, zero_cons_default, default_head,
      default_tail, enc1_nil, encM_nil, encM_cons_zero, encM_cons_run, encLeft_cons_head,
      cons_one_encLeft_tail, encRight_cons_head, cons_one_encRight_tail, encM_cons_run_head,
      cons_one_encM_cons_run_tail, multiStep_zero]
    try rfl
  )
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


#print axioms step_BB_nil_exact
#print axioms step_BB_run0_exact
end BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.Solution
