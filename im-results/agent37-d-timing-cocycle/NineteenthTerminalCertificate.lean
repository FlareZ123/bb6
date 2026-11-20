import NineteenthTail5684
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2NineteenthRoot

open DRegular BB6.DRegularFast

/-- Exact 9,780-section endpoint, composed through the 19 certified
    512-section blocks and the final 52-section remainder. -/
theorem terminal9780_exact :
    run 9780 seed19 = some ⟨9*t19+10,9,1⟩ := by
  have h := fastRunBlocks_tail_correct 19 52 seed19 seed19_canon
  have hlen : blockSize*19+52 = 9780 := by norm_num [blockSize]
  have hrun :
      run 9780 seed19 =
        (fastRunBlocks 19 seed19).bind (run 52) := by
    simpa [hlen] using h
  rw [blocks19_from_seed_exact, final52_exact] at hrun
  exact hrun

theorem t19_mod27_exact : t19 % 27 = 12 :=
  t19_mod27

#print axioms terminal9780_exact
#print axioms t19_mod27_exact

end BB6.Agent2NineteenthRoot
