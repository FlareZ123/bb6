import NineteenthBlock2
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2NineteenthRoot

open DRegular BB6.DRegularFast

/-- Final 1,588-section arithmetic block after the two 4,096-section blocks. -/
def terminal9780 : L :=
  (BB6.DRegularFast.fastRun 1588 block19_2).getD ⟨9,0,0⟩

def t19 : Nat := (terminal9780.a-10)/9

theorem terminal1588_certificate :
    run 1588 block19_2 = some ⟨9*t19+10,9,1⟩ ∧
      t19 % 27 = 12 := by
  rw [BB6.DRegularFast.fastRun_correct 1588 block19_2 block19_2_canon]
  decide

theorem terminal1588_exact :
    run 1588 block19_2 = some ⟨9*t19+10,9,1⟩ :=
  terminal1588_certificate.1

theorem t19_mod27 : t19 % 27 = 12 :=
  terminal1588_certificate.2

/-- Compose the three exact blocks: 4,096 + 4,096 + 1,588 = 9,780. -/
theorem terminal9780_exact :
    run 9780 seed19 = some ⟨9*t19+10,9,1⟩ := by
  rw [show 9780 = 4096 + (4096 + 1588) by decide,
    BB6.DRegularFast.run_add]
  rw [block19_1_exact]
  change run (4096 + 1588) block19_1 = some ⟨9*t19+10,9,1⟩
  rw [BB6.DRegularFast.run_add]
  rw [block19_2_exact]
  change run 1588 block19_2 = some ⟨9*t19+10,9,1⟩
  exact terminal1588_exact

theorem t19_mod27_exact : t19 % 27 = 12 :=
  t19_mod27

#print axioms terminal9780_exact
#print axioms t19_mod27_exact

end BB6.Agent2NineteenthRoot
