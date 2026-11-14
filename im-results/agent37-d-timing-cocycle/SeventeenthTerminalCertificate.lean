import Lean.Elab.Tactic.Omega
import SeventeenthSecondHalf
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2SeventeenthArithmetic

open DRegular

/-- Compose the two already checked 1,328-step arithmetic runs. -/
theorem run2656_exact : run 2656 seed17 = some terminal2656 := by
  rw [show 2656 = 1328 + 1328 by omega,
    BB6.DRegularFast.run_add 1328 1328 seed17,
    middle17_exact]
  simpa [terminal2656] using terminal2656_half_exact

/-- Exact 2,656-step endpoint and the residue required by the E/E/A return. -/
theorem terminal2656_certificate :
    run 2656 seed17 = some ⟨9 * t17 + 7, 7, 1⟩ ∧
      t17 % 27 = 6 := by
  have htotal := run2656_exact
  rcases terminal2656_signature with ⟨hsig, hmod⟩
  constructor
  · rw [hsig] at htotal
    simpa [t17] using htotal
  · simpa [t17] using hmod

theorem terminal2656_exact :
    run 2656 seed17 = some ⟨9 * t17 + 7, 7, 1⟩ :=
  terminal2656_certificate.1

theorem t17_mod27 : t17 % 27 = 6 :=
  terminal2656_certificate.2

#print axioms run2656_exact
#print axioms terminal2656_exact
#print axioms t17_mod27

end BB6.Agent2SeventeenthArithmetic
