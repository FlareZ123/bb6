import SpaceNeedleOddBlocksSource
import TerminalOddInverse
import Lean.Elab.Tactic.Omega

namespace BB6.Agent48.NeedleTerminalOddInverseSource
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle
open BB6.Agent48.NeedleTerminalOddInverse

/-- Complete terminal-target language of t successful odd returns. -/
theorem original_terminal_odd_block_iff (K t : Nat) (hK : 0<K) :
  (∃ m, 0<m ∧ runHigh t (some (.N (2^t*m-1))) = some (.N (2^K-2))) ↔
    5^t ∣ 2^K-1 := by
  constructor
  · rintro ⟨m,hm,h⟩
    have hb := odd_block t m hm
    rw [hb] at h
    have heq : 5^t*m-1=2^K-2 := by
      simpa only [Option.some.injEq, HighLevelState.N.injEq] using h
    exact (terminal_odd_quotient_iff K t hK).mp ⟨m,hm,heq⟩
  · intro h
    obtain ⟨m,hm,heq⟩ := (terminal_odd_quotient_iff K t hK).mpr h
    refine ⟨m,hm,?_⟩
    rw [odd_block t m hm, heq]

/-- A finite set of all positive-length source-valid odd terminal blocks. -/
theorem original_odd_terminal_lengths_spec (K t : Nat) (hK : 0<K) :
  t ∈ oddTerminalLengths K ↔
    0<t ∧ ∃ m, 0<m ∧ runHigh t (some (.N (2^t*m-1))) =
                       some (.N (2^K-2)) := by
  rw [oddTerminalLengths_spec K t hK]
  simp only [and_congr_right_iff]
  intro ht
  constructor
  · rintro ⟨m,hm,heq⟩
    refine ⟨m,hm,?_⟩
    rw [odd_block t m hm,heq]
  · rintro ⟨m,hm,h⟩
    have hs := odd_block t m hm
    rw [hs] at h
    refine ⟨m,hm,?_⟩
    simpa only [Option.some.injEq,HighLevelState.N.injEq] using h

#print axioms original_terminal_odd_block_iff
#print axioms original_odd_terminal_lengths_spec
end BB6.Agent48.NeedleTerminalOddInverseSource
