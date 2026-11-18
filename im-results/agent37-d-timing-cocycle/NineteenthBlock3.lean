import NineteenthBlock2
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2NineteenthRoot

open DRegular

/-- Final 1,588 sections after the two 4,096-section checkpoints. -/
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

#print axioms terminal1588_exact
#print axioms t19_mod27

end BB6.Agent2NineteenthRoot
