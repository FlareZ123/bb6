import DrainImageDensity
import FatalBandSource

namespace BB6.Agent41FatalBand
open BB6.Agent41DrainImageDecoder
open BB6.Agent41DrainImageSource
open BB6.Agent49InverseWindowSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

/-- At least 2N-6 distinct immediately halting states of the special
terminal family with row index below 18N have no predecessor. -/
theorem terminal_density (N : Nat) :
    (goodTerminalRows N).Nodup ∧
    2*N≤ (goodTerminalRows N).length+6 ∧
    ∀ d ∈ goodTerminalRows N,
      d < 18*N ∧ highLevelNext (.D (terminalFirst d) d)=none ∧
      (∀ a e, highLevelNext (.D a e)≠some (.D (terminalFirst d) d)) ∧
      (∀ n, BB6.Agent49ParitySource.run n≠some (.D (terminalFirst d) d)) := by
  refine ⟨goodTerminalRows_nodup N,goodTerminalRows_count excessLaws N,?_⟩
  intro d hd
  obtain ⟨hbound,hlarge,hmod,hblocked⟩ := goodTerminalRows_spec N d hd
  have hbudget := terminal_budget d (by omega)
  exact ⟨hbound,terminal_of_mod d hmod,
    fun a e => no_parent_of_blocked a e (terminalFirst d) d hlarge hbudget hblocked,
    fun n => root_excluded_of_blocked n (terminalFirst d) d hlarge hbudget hblocked⟩

#print axioms terminal_density
end BB6.Agent41FatalBand
