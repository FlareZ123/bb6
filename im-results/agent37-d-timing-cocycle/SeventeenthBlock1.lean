import Lean.Elab.Tactic.Omega
import SeventeenthFirstHalf
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2SeventeenthArithmetic

open DRegular

/-- Exact first 512-transition block from the authentic seventeenth seed. -/
def block1 : L :=
  (BB6.Agent2Fast64.fastRun 512 seed17).getD ⟨9, 0, 0⟩

theorem block1_exact : run 512 seed17 = some block1 := by
  rw [BB6.Agent2Fast64.fastRun_correct 512 seed17 seed17_canon]
  decide

theorem block1_canon : Canon block1 :=
  BB6.DRegularFast.run_canon 512 seed17 block1 seed17_canon block1_exact

#print axioms block1_exact
#print axioms block1_canon

end BB6.Agent2SeventeenthArithmetic
