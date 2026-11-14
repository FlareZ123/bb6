import Lean.Elab.Tactic.Omega
import SeventeenthFirstHalf
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2SeventeenthArithmetic

open DRegular

def terminal2656 : L :=
  (BB6.Agent2Fast64.fastRun 1328 middle17).getD ⟨9, 0, 0⟩

theorem terminal2656_half_exact :
    run 1328 middle17 = some terminal2656 := by
  rw [BB6.Agent2Fast64.fastRun_correct 1328 middle17 middle17_canon]
  decide

theorem terminal2656_canon : Canon terminal2656 :=
  BB6.DRegularFast.run_canon 1328 middle17 terminal2656 middle17_canon
    terminal2656_half_exact

def t17 : Nat := (terminal2656.a - 7) / 9

theorem terminal2656_signature :
    terminal2656 = ⟨9 * t17 + 7, 7, 1⟩ ∧ t17 % 27 = 6 := by
  decide

#print axioms terminal2656_signature

end BB6.Agent2SeventeenthArithmetic
