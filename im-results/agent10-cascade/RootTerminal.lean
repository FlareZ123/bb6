import SweepInvariant
import GapOddJoin

namespace CascadeRootTerminal

/-- Uniform blank-reset-root exclusion of the terminal dyadic gap heights.
    This is a theorem about the exact copied source C-episode semantics; a separate
    backward-chain argument is still necessary to exclude the original fatal c_n. -/
theorem root_excludes_terminal (n : Nat) (hn : 6 ≤ n)
    (hc : n%6=0 ∨ n%6=1 ∨ n%6=2 ∨ n%6=3) :
    ∃ i, ¬ CascadeSweep.ReachC (2,0)
      (8*2^(n-1)+n-1-(2*n+3)*2^(i+1),0) := by
  obtain ⟨i, hodd, heven⟩ := CascadeGapJoin.all_excluded_residue_gate n hn hc
  exact ⟨i, CascadeSweep.root_excludes_nonimage _ hodd heven⟩

#print axioms root_excludes_terminal
end CascadeRootTerminal
