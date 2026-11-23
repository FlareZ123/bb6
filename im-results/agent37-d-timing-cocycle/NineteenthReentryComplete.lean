import NineteenthBlock2
import BlankEighteenthRejoin
import ExceptionalAGeneral
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2NineteenthRoot

open DRegular BB6.DRegularFast
open CryptidBoundary BB6.BoundaryPadding BB6.Padding

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

/-- Compose all three exact arithmetic blocks: 4,096 + 4,096 + 1,588. -/
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

def exception19Time : Nat :=
  BB6.Agent2EighteenthRoot.reentry18Time +
    DRegular.accumulated 9780 seed19

/-- Lift the exact nineteenth regular segment to the authentic blank root. -/
theorem blank_nineteenth_exception :
    ObsEq (run exception19Time blank)
      (DRegularSource.sourceSection ⟨9*t19+10,9,1⟩) := by
  apply BB6.Agent25RootChain.extend_regular blank
    BB6.Agent2EighteenthRoot.reentry18Time
    9780 seed19 ⟨9*t19+10,9,1⟩
  · exact seed19_canon
  · exact terminal9780_exact
  · exact BB6.Agent2EighteenthRoot.blank_eighteenth_reentry

def packet19Time : Nat :=
  BB6.Agent32EAll.duration (3*t19+2) 8 +
    BB6.Agent25AGeneral.aCost t19 2

def reentry19Time : Nat := exception19Time+packet19Time

/-- The original-source E/A packet returns the nineteenth exception to
    a pure-unary regular section. -/
theorem blank_nineteenth_reentry :
    ObsEq (run reentry19Time blank)
      (DRegularSource.sourceSection ⟨64*t19+113,0,0⟩) := by
  exact source_chain exception19Time packet19Time blank
    (DRegularSource.sourceSection ⟨9*t19+10,9,1⟩)
    (DRegularSource.sourceSection ⟨64*t19+113,0,0⟩)
    blank_nineteenth_exception
    (by simpa only [packet19Time] using
      (BB6.Agent25AGeneral.exceptional_EA_general t19 2))

#print axioms terminal9780_exact
#print axioms blank_nineteenth_exception
#print axioms blank_nineteenth_reentry
#print axioms t19_mod27_exact

end BB6.Agent2NineteenthRoot
