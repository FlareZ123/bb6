import Lean.Elab.Tactic.Omega
import SeventeenthBlock1
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2SeventeenthArithmetic

open DRegular

/-- Exact second 512-transition block, starting at the first checkpoint. -/
def block2 : L :=
  (BB6.Agent2Fast64.fastRun 512 block1).getD ⟨9, 0, 0⟩

theorem block2_exact : run 512 block1 = some block2 := by
  rw [BB6.Agent2Fast64.fastRun_correct 512 block1 block1_canon]
  decide

theorem block2_canon : Canon block2 :=
  BB6.DRegularFast.run_canon 512 block1 block2 block1_canon block2_exact

#print axioms block2_exact
#print axioms block2_canon

end BB6.Agent2SeventeenthArithmetic
