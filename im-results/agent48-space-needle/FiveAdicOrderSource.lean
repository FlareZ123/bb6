import SpaceNeedleOddBlocksSource
import TerminalOddInverse
import FiveAdicOrderFull
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0
namespace BB6.Agent48.FiveAdic
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle
open BB6.Agent48.NeedleTerminalOddInverse

/-- The exact terminal-exponent language of t consecutive odd original
high-level returns is the single divisibility class 4*5^(t-1)|K.
The paths are synthetic and do not imply reachability from N 1. -/
theorem original_odd_terminal_order_iff (K t : Nat) (hK : 0<K) (ht : 0<t) :
  (∃ m, 0<m ∧ runHigh t (some (.N (2^t*m-1))) = some (.N (2^K-2))) ↔
    4*5^(t-1) ∣ K := by
  have ht' : t-1+1=t := by omega
  have heq : (∃ m, 0<m ∧ runHigh t (some (.N (2^t*m-1))) = some (.N (2^K-2))) ↔
      5^t ∣ 2^K-1 := by
    constructor
    · rintro ⟨m,hm,h⟩
      have hb := odd_block t m hm
      rw [hb] at h
      have houtput : 5^t*m-1=2^K-2 := by
        simpa only [Option.some.injEq,HighLevelState.N.injEq] using h
      exact (terminal_odd_quotient_iff K t hK).mp ⟨m,hm,houtput⟩
    · intro h
      obtain ⟨m,hm,heq⟩ := (terminal_odd_quotient_iff K t hK).mpr h
      refine ⟨m,hm,?_⟩
      rw [odd_block t m hm,heq]
  rw [heq]
  simpa only [ht'] using exact_power_five_order (t-1) K

#print axioms original_odd_terminal_order_iff
end BB6.Agent48.FiveAdic
