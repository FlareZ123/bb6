import Lean.Elab.Tactic.Omega
import BlankEighteenthRejoin
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2NineteenthRoot

open DRegular

def seed19 : L :=
  ⟨64*BB6.Agent2EighteenthRoot.t18+23,1,5⟩

theorem seed19_canon : Canon seed19 := by
  constructor
  · dsimp [seed19]
    omega
  · simp [seed19]

/-- First 4,096 of the 9,780 regular sections, evaluated in eight
    exact 512-section 3-adic blocks. -/
def block19_1 : L :=
  (BB6.DRegularFast.fastRun 4096 seed19).getD ⟨9,0,0⟩

theorem block19_1_exact :
    run 4096 seed19 = some block19_1 := by
  rw [BB6.DRegularFast.fastRun_correct 4096 seed19 seed19_canon]
  decide

theorem block19_1_canon : Canon block19_1 :=
  BB6.DRegularFast.run_canon 4096 seed19 block19_1
    seed19_canon block19_1_exact

#print axioms block19_1_exact
#print axioms block19_1_canon

end BB6.Agent2NineteenthRoot
