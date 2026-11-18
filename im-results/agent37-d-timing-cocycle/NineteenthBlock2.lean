import NineteenthBlock1
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2NineteenthRoot

open DRegular

/-- Second 4,096-section arithmetic checkpoint. -/
def block19_2 : L :=
  (BB6.DRegularFast.fastRun 4096 block19_1).getD ⟨9,0,0⟩

theorem block19_2_exact :
    run 4096 block19_1 = some block19_2 := by
  rw [BB6.DRegularFast.fastRun_correct 4096 block19_1 block19_1_canon]
  decide

theorem block19_2_canon : Canon block19_2 :=
  BB6.DRegularFast.run_canon 4096 block19_1 block19_2
    block19_1_canon block19_2_exact

#print axioms block19_2_exact
#print axioms block19_2_canon

end BB6.Agent2NineteenthRoot
