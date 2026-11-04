import SpaceNeedleOddBlocksSource
import FiveAdicExtra
import TerminalOddInverse
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0
namespace BB6.Agent48.FiveAdic
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle
open BB6.Agent48.NeedleTerminalOddInverse

/-- For every t there is a source-valid t+1-long odd block feeding the
terminal power 2^(4*5^t). No claim of blank-orbit reachability. -/
theorem every_length_terminal_odd_path (t : Nat) :
  ∃ m, 0<m ∧ runHigh (t+1) (some (.N (2^(t+1)*m-1))) =
      some (.N (2^(4*5^t)-2)) := by
  have hK : 0<4*5^t := by
    have hpos : 0<5^t := Nat.pow_pos (by decide)
    omega
  obtain ⟨m,hm,heq⟩ :=
    (terminal_odd_quotient_iff (4*5^t) (t+1) hK).mpr (five_power_divides t)
  refine ⟨m,hm,?_⟩
  rw [odd_block (t+1) m hm, heq]

#print axioms every_length_terminal_odd_path
end BB6.Agent48.FiveAdic
