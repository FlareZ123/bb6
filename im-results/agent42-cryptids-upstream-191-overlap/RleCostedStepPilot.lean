import BusyBeaver.Calculi.HaltShared
import BusyBeaver.BB6.Halt.M_1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LAHHH
import BusyBeaver.BB6.Halt.M_1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RDHHH

open Mathlib Relation Nat Turing BusyBeaver BusyBeaver.RleStackEngine

namespace BB6Agent42.RleCostedStepPilot

/-- One exact primitive transition, leaving the remaining indexed path as the goal. -/
macro "exactStep" : tactic => `(tactic| (
  apply ReachesIn.step_left
  · simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft,
      BusyBeaver.RleStackEngine.listblank_append_cons,
      BusyBeaver.RleStackEngine.listblank_append_nil,
      Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
      BusyBeaver.RleStackEngine.default_head]
    rfl
))

/-- Build an exact `ReachesIn` witness by reducing each primitive step in the kernel. -/
macro "executeExact " n:num : tactic => `(tactic| (
  iterate $n exactStep
  exact ReachesIn.zero _ _
))

namespace FirstF289
open BusyBeaver.M_1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LAHHH
open BusyBeaver.M_1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LAHHH.Solution

theorem rule_B_nil_exact (L : List ℕ) :
    ReachesIn target_tm 1 (cfg_B target_tm L []) (cfg_C target_tm (bumpHead L) []) := by
  executeExact 1

theorem rule_B_zero_exact (L R : List ℕ) :
    ReachesIn target_tm 4 (cfg_B target_tm L (0 :: R)) (cfg_B target_tm (0 :: L) R) := by
  executeExact 4

end FirstF289

namespace SecondF289
open BusyBeaver.M_1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RDHHH
open BusyBeaver.M_1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RDHHH.Solution

theorem rule_B_nil_exact (L : List ℕ) :
    ReachesIn target_tm 1 (cfg_B target_tm L []) (cfg_C target_tm (bumpHead L) []) := by
  executeExact 1

theorem rule_B_zero_exact (L R : List ℕ) :
    ReachesIn target_tm 4 (cfg_B target_tm L (0 :: R)) (cfg_B target_tm (0 :: L) R) := by
  executeExact 4

end SecondF289

end BB6Agent42.RleCostedStepPilot


#print axioms BB6Agent42.RleCostedStepPilot.FirstF289.rule_B_nil_exact
#print axioms BB6Agent42.RleCostedStepPilot.FirstF289.rule_B_zero_exact
#print axioms BB6Agent42.RleCostedStepPilot.SecondF289.rule_B_nil_exact
#print axioms BB6Agent42.RleCostedStepPilot.SecondF289.rule_B_zero_exact
