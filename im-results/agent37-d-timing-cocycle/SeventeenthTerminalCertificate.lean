import Lean.Elab.Tactic.Omega
import BlankSixteenthRejoin
import SeventeenthSecondHalf
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2SeventeenthRoot

def seed17 : DRegular.L := BB6.Agent2SeventeenthArithmetic.seed17

def terminal2656 : DRegular.L := BB6.Agent2SeventeenthArithmetic.terminal2656

def t17 : Nat := BB6.Agent2SeventeenthArithmetic.t17

theorem terminal2656_certificate :
    DRegular.run 2656 seed17 = some ⟨9 * t17 + 7, 7, 1⟩ ∧ t17 % 27 = 6 := by
  have htotal :
      DRegular.run 2656 BB6.Agent2SeventeenthArithmetic.seed17 =
        some BB6.Agent2SeventeenthArithmetic.terminal2656 := by
    rw [show 2656 = 1328 + 1328 by omega,
      BB6.DRegularFast.run_add 1328 1328
        BB6.Agent2SeventeenthArithmetic.seed17,
      BB6.Agent2SeventeenthArithmetic.middle17_exact]
    exact BB6.Agent2SeventeenthArithmetic.terminal2656_half_exact
  rcases BB6.Agent2SeventeenthArithmetic.terminal2656_signature with ⟨hsig, hmod⟩
  constructor
  · simpa [seed17, t17, hsig] using htotal
  · simpa [t17] using hmod

theorem terminal2656_exact :
    DRegular.run 2656 seed17 = some ⟨9 * t17 + 7, 7, 1⟩ :=
  terminal2656_certificate.1

theorem t17_mod27 : t17 % 27 = 6 :=
  terminal2656_certificate.2

def u17 : Nat := t17 / 3

theorem t17_eq_three_u17 : t17 = 3 * u17 := by
  have h := t17_mod27
  dsimp [u17]
  omega

#print axioms terminal2656_exact
#print axioms t17_mod27
#print axioms t17_eq_three_u17

end BB6.Agent2SeventeenthRoot
