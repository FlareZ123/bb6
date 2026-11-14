import Lean.Elab.Tactic.Omega
import BlankSixteenthRejoin
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2SeventeenthArithmetic

open DRegular

def seed17 : L :=
  ⟨64 * BB6.Agent2SixteenthRoot.t16 + 27, 1, 5⟩

theorem seed17_canon : Canon seed17 := by
  constructor
  · dsimp [seed17]
    omega
  · simp [seed17]

def middle17 : L :=
  (BB6.Agent2Fast64.fastRun 1328 seed17).getD ⟨9, 0, 0⟩

theorem middle17_exact : run 1328 seed17 = some middle17 := by
  rw [BB6.Agent2Fast64.fastRun_correct 1328 seed17 seed17_canon]
  decide

theorem middle17_canon : Canon middle17 :=
  BB6.DRegularFast.run_canon 1328 seed17 middle17 seed17_canon middle17_exact

#print axioms middle17_exact

end BB6.Agent2SeventeenthArithmetic
