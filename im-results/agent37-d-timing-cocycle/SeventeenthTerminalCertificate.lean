import Lean.Elab.Tactic.Omega
import SeventeenthBlock2
import SeventeenthSecondHalf
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2SeventeenthArithmetic

open DRegular

/-- Recover the final 816 transitions of the first 1,328-step half from
    two short compositions and the already checked half certificate. -/
theorem run816_from_block1 : run 816 block1 = some middle17 := by
  have hcomp : run 1328 seed17 = (run 512 seed17).bind (run 816) := by
    simpa only [show 1328 = 512 + 816 by omega] using
      (BB6.DRegularFast.run_add 512 816 seed17)
  rw [block1_exact, middle17_exact] at hcomp
  simpa using hcomp.symm

/-- The final 304 transitions of the first half end at the certified
    middle state after the two 512-step checkpoints. -/
theorem run304_from_block2 : run 304 block2 = some middle17 := by
  have hcomp : run 816 block1 = (run 512 block1).bind (run 304) := by
    simpa only [show 816 = 512 + 304 by omega] using
      (BB6.DRegularFast.run_add 512 304 block1)
  rw [block2_exact, run816_from_block1] at hcomp
  simpa using hcomp.symm

/-- Compose the authenticated 1,328-step halves using only short
    run-addition lemmas (512, 512, and 304 steps), avoiding a large
    1,328-step induction certificate. -/
theorem run2656_exact : run 2656 seed17 = some terminal2656 := by
  have hcomp1 :
      run 2656 seed17 = (run 512 seed17).bind (run 2144) := by
    simpa only [show 2656 = 512 + 2144 by omega] using
      (BB6.DRegularFast.run_add 512 2144 seed17)
  have hcomp2 :
      run 2144 block1 = (run 512 block1).bind (run 1632) := by
    simpa only [show 2144 = 512 + 1632 by omega] using
      (BB6.DRegularFast.run_add 512 1632 block1)
  have hcomp3 :
      run 1632 block2 = (run 304 block2).bind (run 1328) := by
    simpa only [show 1632 = 304 + 1328 by omega] using
      (BB6.DRegularFast.run_add 304 1328 block2)
  calc
    run 2656 seed17 = (run 512 seed17).bind (run 2144) := hcomp1
    _ = run 2144 block1 := by rw [block1_exact]; rfl
    _ = (run 512 block1).bind (run 1632) := hcomp2
    _ = run 1632 block2 := by rw [block2_exact]; rfl
    _ = (run 304 block2).bind (run 1328) := hcomp3
    _ = run 1328 middle17 := by rw [run304_from_block2]; rfl
    _ = some terminal2656 := terminal2656_half_exact

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

#print axioms run816_from_block1
#print axioms run304_from_block2
#print axioms run2656_exact
#print axioms terminal2656_exact
#print axioms t17_mod27

end BB6.Agent2SeventeenthArithmetic
