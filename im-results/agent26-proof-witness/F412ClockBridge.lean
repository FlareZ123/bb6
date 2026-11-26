import F412Partition
import CryptidsHaltIff
import BusyBeaver.Bridge
import BusyBeaver.Basic
import BusyBeaver.BB6.Halt.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA

namespace BB6.Agent26F412Graft
open BB6Coverage BB6.ConjectureBridge

set_option maxRecDepth 100000

/-- Clock transport at every finite index, without evaluating the clock. -/
theorem multiStep_sourceRun (m : ConjectureMachines.Machine 6 2) (n : Nat) :
    BusyBeaver.multiStep m.toBB (BusyBeaver.init []) n =
      (sourceRun m n).map ConjectureMachines.Cfg.toBB := by
  induction n with
  | zero => rw [BusyBeaver.multiStep_zero, ConjectureMachines.init_toBB]; rfl
  | succ n ih =>
    rw [BusyBeaver.multiStep_succ', ih]
    cases hs : sourceRun m n with
    | none => simp [sourceRun,hs]
    | some c => simp [sourceRun,hs,ConjectureMachines.step_toBB]

abbrev fSource : ConjectureMachines.Machine 6 2 :=
  BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.machine

theorem fSource_literal : toAgent8 fSource = fLiteral := by
  funext s
  rcases s with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl

theorem fClock_of_source
    (hStop : BusyBeaver.multiStep fSource.toBB (BusyBeaver.init []) (fMoves+1) = none)
    (hLive : (BusyBeaver.multiStep fSource.toBB (BusyBeaver.init []) fMoves).isSome = true) :
    HaltsAfter fLiteral fMoves := by
  rw [multiStep_sourceRun] at hStop hLive
  have hL : (sourceRun fSource fMoves).isSome = true := by
    cases hs : sourceRun fSource fMoves <;> simp [hs] at hLive ⊢
  have hS : sourceRun fSource (fMoves+1) = none := by
    cases hs : sourceRun fSource (fMoves+1) <;> simp [hs] at hStop ⊢
  rw [← fSource_literal]
  exact (source_halts_after_iff_agent8_halts_after fSource fMoves).mp ⟨hL,hS⟩

#print axioms multiStep_sourceRun
#print axioms fSource_literal
#print axioms fClock_of_source
end BB6.Agent26F412Graft
