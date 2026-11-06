import BB429AffineReturn
import BB429RootPrefix
import Lean.Elab.Tactic.Omega

namespace Agent6RootBlockReach

/-- The n=14 affine return map carries the blank-root checkpoint through
1,887 returns, each taking 15 source steps. -/
theorem n14_zero_row_block :
    BB429.run (1887*15) (0,98408)=some (0,196532) := by
  have hn : 14%4=2 := by decide
  have hW : 98408%4=0 := by decide
  have hpow : 2^14=16384 := by decide
  have hlo : 6*2^14≤98408+3*14+6 := by rw [hpow]; omega
  have hmul : 1887*52=98124 := by decide
  have hhi : 98408+1887*(3*14+10)+3*14+18≤12*2^14 := by
    rw [show 3*14+10=52 by decide,
        show 3*14+18=60 by decide, hpow]
    omega
  have hsum : 98408+98124=196532 := by decide
  simpa [show 14+1=15 by decide,
    show 3*14+10=52 by decide, hmul, hsum] using
      Agent6AffineReturn.even_burst_affine_iter 14 98408 1887 hn hW hlo hhi

/-- Exact blank-root reachability of the endpoint after 51,902 source steps. -/
theorem blank_reaches_n14_block_end :
    BB429.run (23597+1887*15) (0,0)=some (0,196532) := by
  rw [BB429.run_add]
  simp [Agent6RootPrefix.blank_reaches_n14_start, n14_zero_row_block]

#print axioms n14_zero_row_block
#print axioms blank_reaches_n14_block_end

end Agent6RootBlockReach
